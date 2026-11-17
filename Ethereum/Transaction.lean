import Ethereum.Semantics
import Ethereum.EllipticCurves

/-!
# Transactions

Transaction validity and the application of a valid transaction to the state.

`Υ` (`Ethereum/Semantics.lean`) executes a transaction that is already known
to be valid. `validateTransaction` decides validity and recovers the sender,
and `applyTransaction` combines the two, which is the entry point for
executing a transaction of a block.
-/

namespace Ethereum

namespace EVM

/--
The signing payload `L_X(T)` of a transaction (Yellow Paper, Appendix F),
the RLP structure whose hash the sender signs. A legacy transaction is either
pre-EIP-155 (`w ∈ {27, 28}`) or commits to `chainId`.
-/
def signingPayload (chainId : ℕ) (T : Transaction) : Except Exception 𝕋 :=
  let accessEntryRLP : AccountAddress × Array UInt256 → 𝕋
    | ⟨a, s⟩ => .𝕃 [.𝔹 a.toByteArray, .𝕃 (s.map (.𝔹 ∘ UInt256.toByteArray)).toList]
  let accessEntriesRLP (aEs : List (AccountAddress × Array UInt256)) : 𝕋 :=
    .𝕃 (aEs.map accessEntryRLP)
  match T with
    | /- 0 -/ .legacy t =>
      if t.w.toNat ∈ [27, 28] then
        .ok ∘ .𝕃 ∘ List.map .𝔹 <|
          [ BE t.nonce.toNat -- Tₙ
          , BE t.gasPrice.toNat -- Tₚ
          , BE t.gasLimit.toNat -- T_g
          , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
            t.recipient.option .empty AccountAddress.toByteArray -- Tₜ
          , BE t.value.toNat -- Tᵥ
          , t.data
          ]
      else
        if t.w = .ofNat (35 + chainId * 2) ∨ t.w = .ofNat (36 + chainId * 2) then
          .ok ∘ .𝕃 ∘ List.map .𝔹 <|
            [ BE t.nonce.toNat -- Tₙ
            , BE t.gasPrice.toNat -- Tₚ
            , BE t.gasLimit.toNat -- T_g
            , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
              t.recipient.option .empty AccountAddress.toByteArray -- Tₜ
            , BE t.value.toNat -- Tᵥ
            , t.data -- p
            , BE chainId
            , .empty
            , .empty
            ]
        else
          throw <| .TransactionException .IllFormedRLP

    | /- 1 -/ .access t =>
      .ok ∘ .𝕃 <|
        [ .𝔹 (BE t.chainId.toNat) -- T_c
        , .𝔹 (BE t.nonce.toNat) -- Tₙ
        , .𝔹 (BE t.gasPrice.toNat) -- Tₚ
        , .𝔹 (BE t.gasLimit.toNat) -- T_g
        , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
          .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
        , .𝔹 (BE t.value.toNat) -- T_v
        , .𝔹 t.data  -- p
        , accessEntriesRLP t.accessList -- T_A
        ]
    | /- 2 -/ .dynamic t =>
      .ok ∘ .𝕃 <|
        [ .𝔹 (BE t.chainId.toNat) -- T_c
        , .𝔹 (BE t.nonce.toNat) -- Tₙ
        , .𝔹 (BE t.maxPriorityFeePerGas.toNat) -- T_f
        , .𝔹 (BE t.maxFeePerGas.toNat) -- Tₘ
        , .𝔹 (BE t.gasLimit.toNat) -- T_g
        , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
          .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
        , .𝔹 (BE t.value.toNat) -- Tᵥ
        , .𝔹 t.data -- p
        , accessEntriesRLP t.accessList -- T_A
        ]
    | /- 3 -/ .blob t =>
      .ok ∘ .𝕃 <|
        [ .𝔹 (BE t.chainId.toNat) -- T_c
        , .𝔹 (BE t.nonce.toNat) -- Tₙ
        , .𝔹 (BE t.maxPriorityFeePerGas.toNat) -- T_f
        , .𝔹 (BE t.maxFeePerGas.toNat) -- Tₘ
        , .𝔹 (BE t.gasLimit.toNat) -- T_g
        , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
          .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
        , .𝔹 (BE t.value.toNat) -- Tᵥ
        , .𝔹 t.data -- p
        , accessEntriesRLP t.accessList -- T_A
        , .𝔹 (BE t.maxFeePerBlobGas.toNat)
        , .𝕃 (t.blobVersionedHashes.map .𝔹)
        ]
    | /- 4 -/ .setCode t =>
      let authorizationRLP (a : Authorization) : 𝕋 :=
        .𝕃
          [ .𝔹 (BE a.chainId.toNat)
          , .𝔹 a.address.toByteArray
          , .𝔹 (BE a.nonce.toNat)
          , .𝔹 (BE a.yParity.toNat)
          , .𝔹 a.r
          , .𝔹 a.s
          ]
      .ok ∘ .𝕃 <|
        [ .𝔹 (BE t.chainId.toNat) -- T_c
        , .𝔹 (BE t.nonce.toNat) -- Tₙ
        , .𝔹 (BE t.maxPriorityFeePerGas.toNat) -- T_f
        , .𝔹 (BE t.maxFeePerGas.toNat) -- Tₘ
        , .𝔹 (BE t.gasLimit.toNat) -- T_g
        , .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
        , .𝔹 (BE t.value.toNat) -- Tᵥ
        , .𝔹 t.data -- p
        , accessEntriesRLP t.accessList -- T_A
        , .𝕃 (t.authorizationList.map authorizationRLP)
        ]

/--
The sender `S(T)` of a transaction (Yellow Paper, Appendix F): checks the
signature values and recovers the signer from the signing payload.
-/
def recoverSender (chainId : ℕ) (T : Transaction) : Except Exception AccountAddress := do
  let r : ℕ := fromByteArrayBigEndian T.base.r
  let s : ℕ := fromByteArrayBigEndian T.base.s
  if 0 ≥ r ∨ r ≥ secp256k1n then throw <| .TransactionException .INVALID_SIGNATURE_VRS
  if 0 ≥ s ∨ s > secp256k1n / 2 then throw <| .TransactionException .INVALID_SIGNATURE_VRS
  let v : ℕ := -- (324)
    match T with
      | .legacy t =>
        let w := t.w.toNat
        if w ∈ [27, 28] then
          w - 27
        else
          if w = 35 + chainId * 2 ∨ w = 36 + chainId * 2 then
            (w - 35) % 2
          else
            w
      | .access t | .dynamic t | .blob t | .setCode t => t.yParity.toNat
  if v ∉ [0, 1] then throw <| .TransactionException .INVALID_SIGNATURE_VRS

  let some T_RLP := RLP (← signingPayload chainId T) | throw <| .TransactionException .IllFormedRLP

  let h_T := -- (318)
    match T with
      | .legacy _ => KEC T_RLP
      | _ => KEC <| ByteArray.mk #[T.type] ++ T_RLP

  let (S_T : AccountAddress) ← -- (323)
    match ECDSARECOVER h_T (ByteArray.mk #[.ofNat v]) T.base.r T.base.s with
      | .ok s =>
        pure <| Fin.ofNat _ <| fromByteArrayBigEndian <|
          (KEC s).extract 12 32 /- 160 bits = 20 bytes -/
      -- A signature from which no sender can be recovered is invalid.
      | .error _ => throw <| .TransactionException .INVALID_SIGNATURE_VRS
  pure S_T

/--
Transaction validity (Yellow Paper, Section 6.2, and the EIPs that extend it),
given the state `σ` before the transaction and the gas and blob gas the block
has used so far. Returns the sender.

`Υ` assumes this check passed: it reads the sender's account unconditionally.
-/
def validateTransaction
  (fork : Fork)
  (σ : AccountMap)
  (chainId : ℕ)
  (header : BlockHeader)
  (totalGasUsedInBlock : ℕ)
  (blobGasUsedInBlock : ℕ)
  (T : Transaction)
  : Except Exception AccountAddress
:= do
  let H_f := header.baseFeePerGas
  if T.base.gasLimit.toNat + totalGasUsedInBlock > header.gasLimit then
    throw <| .TransactionException .GAS_ALLOWANCE_EXCEEDED
  -- The blob gas of the block so far, with this transaction, must fit.
  -- Before Osaka the per-transaction blob limit is the block maximum, so a
  -- transaction over it alone breaks both caps; that is reported as the count
  -- error (see `Conform.selectReportedException`). From Osaka on the block
  -- allowance takes precedence.
  if blobGasUsedInBlock + getTotalBlobGas T > fork.spec.blobSchedule.maxBlobGas then
    if ¬fork.spec.eip7594 ∧ T.blobVersionedHashes.length > fork.spec.blobSchedule.maxBlobs then
      throw <| .TransactionException .TYPE_3_TX_BLOB_COUNT_EXCEEDED
    throw <| .TransactionException .TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED
  if T.base.nonce.toNat ≥ 2^64-1 then
    throw <| .TransactionException .NONCE_IS_MAX

  -- Legacy and access-list transactions pay `gasPrice`, which is therefore
  -- their maximum fee per gas.
  let maxFeePerGas :=
    match T with
      | .dynamic t | .blob t | .setCode t => t.maxFeePerGas
      | .legacy t | .access t => t.gasPrice
  if H_f > maxFeePerGas.toNat then
    throw <| .TransactionException .INSUFFICIENT_MAX_FEE_PER_GAS

  match T with
    | .legacy t =>
      -- EIP-155 signatures commit to a chain id, which is a 64-bit number: a
      -- `w` that encodes a larger one is an invalid signature.
      let w := t.w.toNat
      if w ≥ 35 then
        if (w - 35) / 2 ≥ 2 ^ 64 then
          throw <| .TransactionException .INVALID_SIGNATURE_VRS
        if (w - 35) / 2 ≠ chainId then
          throw <| .TransactionException .INVALID_CHAINID
    | .access t | .dynamic t | .blob t | .setCode t =>
      if t.chainId.toNat ≠ chainId then
        throw <| .TransactionException .INVALID_CHAINID

  -- EIP-7825 (Osaka): transaction gas limit cap.
  if fork.spec.eip7825 ∧ T.base.gasLimit.toNat > 2 ^ 24 then
    throw <| .TransactionException .GAS_LIMIT_EXCEEDS_MAXIMUM

  let g₀ : ℕ := EVM.intrinsicGas fork T
  if T.base.gasLimit.toNat < g₀ then
    throw <| .TransactionException .INTRINSIC_GAS_TOO_LOW
  -- EIP-7623 (Prague)
  if T.base.gasLimit.toNat < EVM.calldataFloorGas fork T then
    throw <| .TransactionException .INTRINSIC_GAS_BELOW_FLOOR_GAS_COST
  match T with
    | .dynamic t | .setCode t =>
      if t.maxPriorityFeePerGas > t.maxFeePerGas then
        throw <| .TransactionException .PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS
    | .blob bt => do
      if bt.maxPriorityFeePerGas > bt.maxFeePerGas then
        throw <| .TransactionException .PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS
      if T.base.recipient = none then
        throw <| .TransactionException .TYPE_3_TX_CONTRACT_CREATION
      if bt.maxFeePerBlobGas.toNat < header.getBlobGasprice fork then
        .error (.TransactionException .INSUFFICIENT_MAX_FEE_PER_BLOB_GAS)
      -- Per-transaction blob limit: the block maximum until Osaka, where
      -- EIP-7594 caps it at 6.
      let blobLimit := if fork.spec.eip7594 then 6 else fork.spec.blobSchedule.maxBlobs
      if bt.blobVersionedHashes.length > blobLimit then
        throw <| .TransactionException .TYPE_3_TX_BLOB_COUNT_EXCEEDED
      if bt.blobVersionedHashes.length = 0 then
        throw <| .TransactionException .TYPE_3_TX_ZERO_BLOBS
      if bt.blobVersionedHashes.any (λ h ↦ h[0]? != .some VERSIONED_HASH_VERSION_KZG) then
        throw <| .TransactionException .TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH
    | _ => pure ()

  match T.base.recipient with
    | none => do
      let MAX_CODE_SIZE := 24576
      let MAX_INITCODE_SIZE := 2 * MAX_CODE_SIZE
      if T.base.data.size > MAX_INITCODE_SIZE then
        throw <| .TransactionException .INITCODE_SIZE_EXCEEDED
    | some _ => pure ()

  let S_T ← recoverSender chainId T

  -- The signature is checked first: a set-code transaction with invalid
  -- signature values is reported as such (`test_bad_v_r_s`).
  match T with
    | .setCode t =>
      if ¬fork.spec.eip7702 then
        throw <| .TransactionException .TYPE_4_TX_PRE_FORK
      if t.authorizationList.isEmpty then
        throw <| .TransactionException .TYPE_4_EMPTY_AUTHORIZATION_LIST
      if t.recipient.isNone then
        throw <| .TransactionException .TYPE_4_TX_CONTRACT_CREATION
    | _ => pure ()

  -- "Also, with a slight abuse of notation ... "
  let (senderCode, senderNonce, senderBalance) :=
    match σ.get? S_T with
      | some sender => (sender.code, sender.nonce, sender.balance)
      | none => (.empty, ⟨0⟩, ⟨0⟩)

  -- EIP-7702 (Prague): a delegated account still originates transactions.
  if senderCode ≠ .empty ∧ ¬(fork.spec.eip7702 ∧ isDelegationDesignation senderCode) then
    throw <| .TransactionException .SENDER_NOT_EOA
  if T.base.nonce < senderNonce then
    throw <| .TransactionException .NONCE_MISMATCH_TOO_LOW
  if T.base.nonce > senderNonce then
    throw <| .TransactionException .NONCE_MISMATCH_TOO_HIGH
  -- Upfront cost is unbounded. A product that does not fit in 256 bits is
  -- still more than any balance, and Cancun clients report that as
  -- insufficient funds (`HighGasPriceParis` expects `TR_NoFundsX`).
  let v₀ : ℕ :=
    match T with
      | .legacy t | .access t =>
        t.gasLimit.toNat * t.gasPrice.toNat + t.value.toNat
      | .dynamic t | .setCode t =>
        t.gasLimit.toNat * t.maxFeePerGas.toNat + t.value.toNat
      | .blob t =>
        t.gasLimit.toNat * t.maxFeePerGas.toNat
          + t.value.toNat
          + getTotalBlobGas T * t.maxFeePerBlobGas.toNat
  if v₀ > senderBalance.toNat then
    throw <| .TransactionException .INSUFFICIENT_ACCOUNT_FUNDS

  pure S_T

/--
Executes a valid transaction `T` from `sender` and records it in the block:
its gas, its receipt, and its logs, which accumulate over the block for the
bloom filter and the EIP-6110 deposit requests.
-/
def executeTransaction
  (fork : Fork)
  (transaction : Transaction)
  (sender : AccountAddress)
  (s : State)
  (header : BlockHeader)
  : Except Exception State
:= do
  let (ypState, substate, statusCode, totalGasUsed) ←
    Υ fork s.accountMap header.baseFeePerGas header s.executionEnv.blocks transaction sender
  let cumulativeGasUsed := s.totalGasUsedInBlock + totalGasUsed.toNat
  pure
    { s with
      accountMap := ypState
      totalGasUsedInBlock := cumulativeGasUsed
      transactionReceipts :=
        s.transactionReceipts.push
          ⟨ transaction.type
          , statusCode
          , cumulativeGasUsed
          , bloomFilter substate.joinLogs
          , substate.logSeries
          ⟩
      substate := { substate with logSeries := s.substate.logSeries ++ substate.logSeries }
    }

/--
Validates a transaction of a block and executes it on `s`. `blobGasUsedInBlock`
is the blob gas of the block's earlier transactions.
-/
def applyTransaction
  (fork : Fork)
  (chainId : ℕ)
  (header : BlockHeader)
  (blobGasUsedInBlock : ℕ)
  (T : Transaction)
  (s : State)
  : Except Exception State
:= do
  let S_T ←
    validateTransaction fork s.accountMap chainId header s.totalGasUsedInBlock blobGasUsedInBlock T
  executeTransaction fork T S_T s header

end EVM

end Ethereum
