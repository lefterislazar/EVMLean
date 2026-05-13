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

structure RawBlock where
  rlp          : ByteArray
  exception    : List String
deriving BEq, Inhabited, Repr

abbrev RawBlocks := Array RawBlock

structure DeserializedBlock where
  hash         : UInt256
  blockHeader  : BlockHeader
  transactions : Transactions
  withdrawals  : Withdrawals
  exception    : List String
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
      let hash : UInt256 := .ofNat <| fromByteArrayBigEndian <| ffi.KEC headerRLP
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
  parseTransaction : 𝕋 → Except EVM.Exception Transaction
    | .𝔹 typePlusPayload => -- Transaction type > 0
      match deserializeRLP (typePlusPayload.extract 1 typePlusPayload.size) with
        | some -- Type 3 transactions
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
        | some -- Type 2 transactions
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
        | some -- Type 1 transactions
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
        | _ =>
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
  parseHeader : 𝕋 → Except EVM.Exception BlockHeader
    | .𝕃
      [ .𝔹 parentHash
      , .𝔹 uncleHash
      , .𝔹 coinbase
      , .𝔹 stateRoot
      , .𝔹 transactionsTrie
      , .𝔹 receiptTrie
      , .𝔹 bloom
      , .𝔹 difficulty
      , .𝔹 number
      , .𝔹 gasLimit
      , .𝔹 gasUsed
      , .𝔹 timestamp
      , .𝔹 extraData
      , .𝔹 mixHash
      , .𝔹 nonce
      , .𝔹 baseFeePerGas
      , .𝔹 withdrawalsRoot
      , .𝔹 blobGasUsed
      , .𝔹 excessBlobGas
      , .𝔹 parentBeaconBlockRoot
      ]
      => pure <|
        BlockHeader.mk
          (.ofNat <| fromByteArrayBigEndian parentHash)
          (.ofNat <| fromByteArrayBigEndian uncleHash)
          (.ofNat <| fromByteArrayBigEndian coinbase)
          (.ofNat <| fromByteArrayBigEndian stateRoot)
          transactionsTrie
          receiptTrie
          bloom
          (fromByteArrayBigEndian difficulty)
          (fromByteArrayBigEndian number)
          (fromByteArrayBigEndian gasLimit)
          (fromByteArrayBigEndian gasUsed)
          (fromByteArrayBigEndian timestamp)
          extraData
          (.ofNat <| fromByteArrayBigEndian nonce)
          (.ofNat <| fromByteArrayBigEndian mixHash)
          (fromByteArrayBigEndian baseFeePerGas)
          parentBeaconBlockRoot
          withdrawalsRoot
          (.ofNat <| fromByteArrayBigEndian blobGasUsed)
          (.ofNat <| fromByteArrayBigEndian excessBlobGas)
    | _ =>
      dbg_trace "Block header has wrong RLP structure"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING

end Ethereum
