import Mathlib.Data.Finset.Basic

import Ethereum.State.BlockHeader
import Ethereum.State.Transaction
import Ethereum.State.Withdrawal

namespace Ethereum

instance : Repr (Finset BlockHeader) := ⟨λ _ _ ↦ "Dummy Repr for ommers. TODO - change this :)."⟩

structure Transactions where
  trieRoot : ByteArray
  array : Array Transaction
deriving BEq, Inhabited, Repr

structure Withdrawals where
  trieRoot : ByteArray
  array : Array Withdrawal
deriving BEq, Inhabited, Repr

structure DeserializedBlock where
  hash         : UInt256
  blockHeader  : BlockHeader
  transactions : Transactions
  withdrawals  : Withdrawals
deriving BEq, Inhabited, Repr

abbrev DeserializedBlocks := Array DeserializedBlock

structure ProcessedBlock where
  hash        : UInt256
  blockHeader : BlockHeader
  σ           : AccountMap
deriving Inhabited

abbrev ProcessedBlocks := Array ProcessedBlock

def validateUInt256
  (b : ByteArray)
  (e : EVM.Exception)
  : Except EVM.Exception UInt256
:= do
  let b := fromByteArrayBigEndian b
  if b ≥ UInt256.size then throw e
  pure (.ofNat b)

def validateUInt64
  (b : ByteArray)
  (e : EVM.Exception)
  : Except EVM.Exception UInt64
:= do
  let b := fromByteArrayBigEndian b
  if b ≥ UInt64.size then throw e
  pure (.ofNat b)

def validateAccountAddress
  (a : ByteArray)
  (e : EVM.Exception)
  : Except EVM.Exception AccountAddress
:= do
  if a.size ≠ 20 then throw e
  pure (.ofNat (fromByteArrayBigEndian a))

def deserializeBlock
  (rlp : ByteArray)
  : Except EVM.Exception (UInt256 × BlockHeader × Transactions × Withdrawals)
:= do
  let (hash, header, transactionTrieRoot, ts, withdrawalTrieRoot, ws) ←
    Option.toExceptWith (.BlockException .RLP_STRUCTURES_ENCODING) do
      let .inr [headerRLP, transactionsRLP, _, withdrawalsRLP] ← oneStepRLP rlp | none
      let hash : UInt256 := .ofNat <| fromByteArrayBigEndian <| KEC headerRLP
      let header ← deserializeRLP headerRLP
      let (.inr transactions) ← oneStepRLP transactionsRLP | none
      let getTrieSnd (t : ByteArray) : Option ByteArray := do
        match ← oneStepRLP t with
          | .inl typePlusPayload => typePlusPayload
          | .inr _ => t
      let transactionTrieRoot ←
        Transaction.computeTrieRoot (← transactions.toArray.mapM getTrieSnd)
      let ts ← transactions.mapM deserializeRLP
      let (.inr withdrawals) ← oneStepRLP withdrawalsRLP | none
      let withdrawalTrieRoot ← Withdrawal.computeTrieRoot withdrawals.toArray
      let ws ← withdrawals.mapM deserializeRLP
      pure (hash, header, transactionTrieRoot, ts, withdrawalTrieRoot, ws)
  let header ← parseHeader header
  let transactions ← parseTransactions (.𝕃 ts)
  let withdrawals ← parseWithdrawals (.𝕃 ws)
  pure (hash, header, ⟨transactionTrieRoot, Array.mk transactions⟩, ⟨withdrawalTrieRoot, Array.mk withdrawals⟩)
 where
  parseWithdrawal : 𝕋 → Except EVM.Exception Withdrawal
    | .𝕃 [.𝔹 globalIndex, .𝔹 validatorIndex, .𝔹 recipient, .𝔹 amount] => do
      pure <|
        .mk
          (← validateUInt64 globalIndex (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
          (← validateUInt64 validatorIndex (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
          (← validateAccountAddress recipient (.BlockException .RLP_INVALID_ADDRESS))
          (← validateUInt64 amount (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
    | _ =>
      dbg_trace "RLP error: parseWithdrawal"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseWithdrawals : 𝕋 → Except EVM.Exception (List Withdrawal)
    | .𝕃 withdrawals => withdrawals.mapM parseWithdrawal
    | .𝔹 ⟨#[]⟩ => pure []
    | _ =>
      dbg_trace "RLP error: parseWithdrawals"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING

  parseStorageKey : 𝕋 → Except EVM.Exception UInt256
    | .𝔹 key => pure <| .ofNat <| fromByteArrayBigEndian key
    | _ =>
      dbg_trace "RLP error: parseStorageKey"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseAccessListEntry : 𝕋 → Except EVM.Exception (AccountAddress × Array UInt256)
    | .𝕃 [.𝔹 accountAddress, .𝕃 storageKeys] => do
      let storageKeys ← storageKeys.mapM parseStorageKey
      let accountAddress : AccountAddress := .ofNat <| fromByteArrayBigEndian accountAddress
      pure (accountAddress, Array.mk storageKeys)
    | _ =>
      dbg_trace "RLP error: parseAccessListEntry"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING

  parseBlobVersionHash : 𝕋 → Except EVM.Exception ByteArray
    | .𝔹 hash => pure hash
    | _ =>
      dbg_trace "RLP error: parseBlobVersionHash"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseAuthorization : 𝕋 → Except EVM.Exception Authorization
    | .𝕃 [.𝔹 chainId, .𝔹 address, .𝔹 nonce, .𝔹 yParity, .𝔹 r, .𝔹 s] => do
      pure {
        chainId := ← validateUInt256 chainId (.TransactionException .TYPE_4_INVALID_AUTHORIZATION_FORMAT)
        address := ← validateAccountAddress address (.TransactionException .TYPE_4_INVALID_AUTHORIZATION_FORMAT)
        -- The authorization nonce is a `uint64` and `yParity` a `uint8`.
        nonce := .ofNat (← validateUInt64 nonce (.TransactionException .TYPE_4_INVALID_AUTHORIZATION_FORMAT)).toNat
        yParity := ← do
          let y ← validateUInt256 yParity (.TransactionException .TYPE_4_INVALID_AUTHORIZATION_FORMAT)
          if y.toNat ≥ 2 ^ 8 then throw (.TransactionException .TYPE_4_INVALID_AUTHORIZATION_FORMAT)
          pure y
        r
        s
      }
    | _ => throw <| .TransactionException .TYPE_4_INVALID_AUTHORIZATION_FORMAT
  parseTransaction : 𝕋 → Except EVM.Exception Transaction
    | .𝔹 typePlusPayload => -- Transaction type > 0
      match (typePlusPayload[0]? : Option UInt8), deserializeRLP (typePlusPayload.extract 1 typePlusPayload.size) with
        | some 4, some -- Type 4 transactions (EIP-7702)
          (.𝕃
            [ .𝔹 chainId
            , .𝔹 nonce
            , .𝔹 maxPriorityFeePerGas
            , .𝔹 maxFeePerGas
            , .𝔹 gasLimit
            , .𝔹 recipient
            , .𝔹 value
            , .𝔹 p
            , .𝕃 accessList
            , .𝕃 authorizationList
            , .𝔹 y
            , .𝔹 r
            , .𝔹 s
            ]) => do
            let recipient : Option AccountAddress ←
              if recipient.isEmpty then pure none
              else some <$> validateAccountAddress recipient (.BlockException .RLP_INVALID_ADDRESS)
            let base : Transaction.Base :=
              .mk
                (.ofNat <| fromByteArrayBigEndian nonce)
                (.ofNat <| fromByteArrayBigEndian gasLimit)
                recipient
                (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                (← accessList.mapM parseAccessListEntry)
                (.ofNat <| fromByteArrayBigEndian y)
            let dynamic : DynamicFeeTransaction :=
              .mk base withAccessList
                (.ofNat <| fromByteArrayBigEndian maxFeePerGas)
                (.ofNat <| fromByteArrayBigEndian maxPriorityFeePerGas)
            pure <| .setCode <|
              SetCodeTransaction.mk dynamic (← authorizationList.mapM parseAuthorization)
        | some 3, some -- Type 3 transactions
          (.𝕃
            [ .𝔹 chainId
            , .𝔹 nonce
            , .𝔹 maxPriorityFeePerGas
            , .𝔹 maxFeePerGas
            , .𝔹 gasLimit
            , .𝔹 recipient
            , .𝔹 value
            , .𝔹 p
            , .𝕃 accessList
            , .𝔹 maxFeePerBlobGas
            , .𝕃 blobVersionedHashes
            , .𝔹 y
            , .𝔹 r
            , .𝔹 s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry

            let base : Transaction.Base :=
              .mk
                (.ofNat <| fromByteArrayBigEndian nonce)
                (.ofNat <| fromByteArrayBigEndian gasLimit)
                recipient
                (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let maxPriorityFeePerGas :=
              .ofNat <| fromByteArrayBigEndian maxPriorityFeePerGas
            let maxFeePerGas := .ofNat <| fromByteArrayBigEndian maxFeePerGas
            let maxFeePerBlobGas :=
              .ofNat <| fromByteArrayBigEndian maxFeePerBlobGas
            let blobVersionedHashes ←
              blobVersionedHashes.mapM parseBlobVersionHash
            let dynamicFeeTransaction : DynamicFeeTransaction :=
              .mk base withAccessList maxFeePerGas maxPriorityFeePerGas
            pure <| .blob <|
              BlobTransaction.mk
                dynamicFeeTransaction
                  maxFeePerBlobGas
                  blobVersionedHashes
        | some 2, some -- Type 2 transactions
          (.𝕃
            [ .𝔹 chainId
            , .𝔹 nonce
            , .𝔹 maxPriorityFeePerGas
            , .𝔹 maxFeePerGas
            , .𝔹 gasLimit
            , .𝔹 recipient
            , .𝔹 value
            , .𝔹 p
            , .𝕃 accessList
            , .𝔹 y
            , .𝔹 r
            , .𝔹 s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry

            let base : Transaction.Base :=
              .mk
                (.ofNat <| fromByteArrayBigEndian nonce)
                (.ofNat <| fromByteArrayBigEndian gasLimit)
                recipient
                (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let maxPriorityFeePerGas :=
              .ofNat <| fromByteArrayBigEndian maxPriorityFeePerGas
            let maxFeePerGas :=
              .ofNat <| fromByteArrayBigEndian maxFeePerGas
            pure <| .dynamic <|
              DynamicFeeTransaction.mk
                base
                withAccessList
                maxFeePerGas maxPriorityFeePerGas
        | some 1, some -- Type 1 transactions
          (.𝕃
            [ .𝔹 chainId
            , .𝔹 nonce
            , .𝔹 gasPrice
            , .𝔹 gasLimit
            , .𝔹 recipient
            , .𝔹 value
            , .𝔹 p
            , .𝕃 accessList
            , .𝔹 y
            , .𝔹 r
            , .𝔹 s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry

            let base : Transaction.Base :=
              .mk
                (.ofNat <| fromByteArrayBigEndian nonce)
                (.ofNat <| fromByteArrayBigEndian gasLimit)
                recipient
                (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let gasPrice := .ofNat <| fromByteArrayBigEndian gasPrice
            pure <| .access <| AccessListTransaction.mk base withAccessList ⟨gasPrice⟩
        | _, _ =>
          dbg_trace "RLP error: deserializeRLP could not parse non-legacy transaction"
          throw <| .BlockException .RLP_STRUCTURES_ENCODING
    | .𝕃
      [ .𝔹 nonce
      , .𝔹 gasPrice
      , .𝔹 gasLimit
      , .𝔹 recipient
      , .𝔹 value
      , .𝔹 p
      , .𝔹 w
      , .𝔹 r
      , .𝔹 s
      ] => do
        let recipient : Option AccountAddress:=
          if recipient.isEmpty then none
          else some <| .ofNat <| fromByteArrayBigEndian recipient

        let base : Transaction.Base :=
          Transaction.Base.mk
            (.ofNat <| fromByteArrayBigEndian nonce)
            (.ofNat <| fromByteArrayBigEndian gasLimit)
            recipient
            (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
            r
            s
            p
        let gasPrice := .ofNat <| fromByteArrayBigEndian gasPrice
        let w := .ofNat <| fromByteArrayBigEndian w
        pure <| .legacy <| LegacyTransaction.mk base ⟨gasPrice⟩ w
    | _ =>
      dbg_trace "RLP error: parseTransaction"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseTransactions : 𝕋 → Except EVM.Exception (List Transaction)
    | .𝕃 transactions => transactions.mapM parseTransaction
    | .𝔹 ⟨#[]⟩ => pure []
    | _ =>
      dbg_trace "RLP error: parseTransactions"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  /-- The fields of a header up to `parentBeaconBlockRoot`, which every
      header from Cancun on has. -/
  parseCancunHeader : List ByteArray → Option BlockHeader
    | [ parentHash, uncleHash, coinbase, stateRoot, transactionsTrie, receiptTrie
      , bloom, difficulty, number, gasLimit, gasUsed, timestamp, extraData, mixHash
      , nonce, baseFeePerGas, withdrawalsRoot, blobGasUsed, excessBlobGas
      , parentBeaconBlockRoot ] =>
      some {
        parentHash := .ofNat <| fromByteArrayBigEndian parentHash
        ommersHash := .ofNat <| fromByteArrayBigEndian uncleHash
        beneficiary := .ofNat <| fromByteArrayBigEndian coinbase
        stateRoot := .ofNat <| fromByteArrayBigEndian stateRoot
        transRoot := transactionsTrie
        receiptRoot := receiptTrie
        logsBloom := bloom
        difficulty := fromByteArrayBigEndian difficulty
        number := fromByteArrayBigEndian number
        gasLimit := fromByteArrayBigEndian gasLimit
        gasUsed := fromByteArrayBigEndian gasUsed
        timestamp := fromByteArrayBigEndian timestamp
        extraData
        nonce := .ofNat <| fromByteArrayBigEndian nonce
        prevRandao := .ofNat <| fromByteArrayBigEndian mixHash
        baseFeePerGas := fromByteArrayBigEndian baseFeePerGas
        parentBeaconBlockRoot
        withdrawalsRoot
        blobGasUsed := .ofNat <| fromByteArrayBigEndian blobGasUsed
        excessBlobGas := .ofNat <| fromByteArrayBigEndian excessBlobGas
      }
    | _ => none

  /--
  A header: the Cancun fields, then the fields that later forks append. Prague
  appends `requestsHash` (EIP-7685), and Amsterdam `blockAccessListHash`
  (EIP-7928) and `slotNumber` (EIP-7843). Which fields a block's fork requires
  is checked by `validateHeader`.
  -/
  parseHeader : 𝕋 → Except EVM.Exception BlockHeader
    | .𝕃 fields => do
      let malformed : EVM.Exception := .BlockException .RLP_STRUCTURES_ENCODING
      let some fields := fields.mapM (fun | .𝔹 b => some b | .𝕃 _ => none) | throw malformed
      let some header := parseCancunHeader (fields.take 20) | throw malformed
      let hash32 (b : ByteArray) : Except EVM.Exception ByteArray :=
        if b.size = 32 then pure b else throw malformed
      match fields.drop 20 with
      | [] => pure header
      | [requestsHash] =>
        pure { header with requestsHash := some (← hash32 requestsHash) }
      | [requestsHash, blockAccessListHash, slotNumber] =>
        pure { header with
          requestsHash := some (← hash32 requestsHash)
          blockAccessListHash := some (← hash32 blockAccessListHash)
          slotNumber := some (← validateUInt64 slotNumber
            (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64)) }
      | _ => throw malformed
    | .𝔹 _ => throw <| .BlockException .RLP_STRUCTURES_ENCODING

end Ethereum
