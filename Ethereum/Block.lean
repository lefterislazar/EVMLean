import Ethereum.Transaction
import Ethereum.Requests
import Ethereum.State.Withdrawal

/-!
# Blocks

The block-level state transition (the Yellow Paper's `Π`): header validity,
the system calls, the transactions, withdrawals and requests of a block, and
block validity. `applyBlock` is the entry point: it applies an RLP-encoded
block to the state and appends it to the chain history.
-/

namespace Ethereum

namespace EVM

/--
A system call (EIP-4788, EIP-2935, EIP-7002, EIP-7251): a message call from
`SYSTEM_ADDRESS` to `contract` that is not charged to the block. A checked call
(the request contracts) invalidates the block when the contract has no code or
the call fails. An unchecked call to an account without code does nothing.
-/
def executeSystemCall
  (fork : Fork)
  (s : State)
  (header : BlockHeader)
  (contract : AccountAddress)
  (input : ByteArray)
  (checked : Bool)
  : Except Exception (State × ByteArray)
:= do
  let code := s.accountMap.get? contract |>.option .empty (·.code)
  if code.isEmpty then
    if checked then throw <| .BlockException .SYSTEM_CONTRACT_EMPTY
    return (s, .empty)
  let (σ, _, _, success, output) :=
    Θ fork
      s.accountMap
      s.accountMap
      default
      SYSTEM_ADDRESS
      SYSTEM_ADDRESS
      contract
      (.Code code)
      (.ofNat SYSTEM_TRANSACTION_GAS)
      (.ofNat header.baseFeePerGas)
      ⟨0⟩
      ⟨0⟩
      input
      0
      header
      []
      s.executionEnv.blocks
      true
  if checked ∧ ¬success then throw <| .BlockException .SYSTEM_CONTRACT_CALL_FAILED
  pure ({ s with accountMap := σ }, output)

/-- EIP-7934 (Osaka): the maximum RLP size of a block. -/
def MAX_RLP_BLOCK_SIZE : ℕ := 10485760 - 2097152

/--
Header validity that does not depend on executing the block, checked before
its transactions: transaction validity uses the header's `baseFeePerGas`,
`gasLimit` and `excessBlobGas`. Returns the parent block.
-/
def validateHeader
  (fork : Fork)
  (blocks : ProcessedBlocks)
  (header : BlockHeader)
  : Except Exception ProcessedBlock
:= do
  if header.parentHash = ⟨0⟩ then
    throw <| .BlockException .UNKNOWN_PARENT_ZERO

  let (some parent : Option ProcessedBlock) :=
    -- Usually the parent is the last processed block
    blocks.findRev? λ b ↦ b.hash = header.parentHash
    | throw <| .BlockException .UNKNOWN_PARENT

  let P_Hₗ := parent.blockHeader.gasLimit

  let ρ := 2; let τ := P_Hₗ / ρ; let ε := 8
  let νStar :=
    if parent.blockHeader.gasUsed < τ then
      (parent.blockHeader.baseFeePerGas * (τ - parent.blockHeader.gasUsed)) / τ
    else
      (parent.blockHeader.baseFeePerGas * (parent.blockHeader.gasUsed - τ)) / τ
  let ν :=
    if parent.blockHeader.gasUsed < τ then νStar / ε else max (νStar / ε) 1
  let expectedBaseFeePerGas :=
    if parent.blockHeader.gasUsed = τ then parent.blockHeader.baseFeePerGas else
    if parent.blockHeader.gasUsed < τ then parent.blockHeader.baseFeePerGas - ν else
      parent.blockHeader.baseFeePerGas + ν
  if
    header.gasLimit < 5000
      ∨ header.gasLimit ≥ P_Hₗ + P_Hₗ / 1024
      ∨ header.gasLimit ≤ P_Hₗ - P_Hₗ / 1024
  then
    throw <| .BlockException .INVALID_GASLIMIT
  if header.baseFeePerGas ≠ expectedBaseFeePerGas then
    throw <| .BlockException .INVALID_BASEFEE_PER_GAS
  if calcExcessBlobGas fork parent.blockHeader != header.excessBlobGas then
    throw <| .BlockException .INCORRECT_EXCESS_BLOB_GAS
  -- EIP-7685: Prague headers, and only those, commit to the requests.
  if fork.spec.eip7685 != header.requestsHash.isSome then
    throw <| .BlockException .INVALID_REQUESTS
  /-
    Cancun `validate_header` rejects a block before applying its transactions
    when the header's gas used exceeds its gas limit (`GAS_USED_OVERFLOW`).
    This is distinct from `GAS_ALLOWANCE_EXCEEDED`, which is raised later when
    an individual transaction's gas limit does not fit in the gas still
    available in the block.
    Keep this after the gas-limit bounds check: `GasLimitIsZero` also has
    gas used above the limit, and that block is `INVALID_GASLIMIT`.
  -/
  if header.gasUsed > header.gasLimit then
    throw <| .BlockException .GAS_USED_OVERFLOW
  pure parent

/--
Block validity after executing the block: the remaining header checks and
the header's commitments to the resulting state, logs, transactions,
withdrawals and receipts.
-/
def validateBlock
  (fork : Fork)
  (state : State)
  (parentHeader : BlockHeader)
  (block : DeserializedBlock)
  : Except Exception Unit
:= do

  let MAX_BLOB_GAS_PER_BLOCK := fork.spec.blobSchedule.maxBlobGas
  let blobGasUsed ← block.transactions.array.foldlM (init := 0) λ blobSum t ↦ do
    let blobSum := blobSum + getTotalBlobGas t
    if blobSum > MAX_BLOB_GAS_PER_BLOCK then
      throw <| .TransactionException .TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED
    pure blobSum

  if state.totalGasUsedInBlock ≠ block.blockHeader.gasUsed then
    throw <| .BlockException .INVALID_GAS_USED
  if block.blockHeader.timestamp ≤ parentHeader.timestamp then
    throw <| .BlockException .INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT
  if block.blockHeader.number ≠ parentHeader.number + 1 then
    throw <| .BlockException .INVALID_BLOCK_NUMBER
  if block.blockHeader.extraData.size > 32 then
    throw <| .BlockException .EXTRA_DATA_TOO_BIG
  if block.blockHeader.gasLimit > 0x7fffffffffffffff then
    throw <| .BlockException .GASLIMIT_TOO_BIG
  if block.blockHeader.difficulty != 0 then
    throw <| .BlockException .IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS
  -- KEC (RLP []) = 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347
  if
    0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347
      != block.blockHeader.ommersHash.toNat
  then
    throw <| .BlockException .IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS

  if blobGasUsed != block.blockHeader.blobGasUsed.toNat then
      throw <| .BlockException .INCORRECT_BLOB_GAS_USED

  if blobGasUsed > MAX_BLOB_GAS_PER_BLOCK then
    throw <| .BlockException .BLOB_GAS_USED_ABOVE_LIMIT

  if block.withdrawals.trieRoot ≠ block.blockHeader.withdrawalsRoot then
    throw <| .BlockException .INVALID_WITHDRAWALS_ROOT

  let computedStateHash : UInt256 :=
    stateTrieRoot state.accountMap.toPersistentAccountMap
    |>.option 0 fromByteArrayBigEndian
    |> .ofNat
  if block.blockHeader.stateRoot ≠ computedStateHash then
    throw <| .BlockException .INVALID_STATE_ROOT

  let expectedBloom := block.blockHeader.logsBloom
  let actualBloom := bloomFilter state.substate.joinLogs
  if expectedBloom ≠ actualBloom then
    throw <| .BlockException .INVALID_LOG_BLOOM
  if block.transactions.trieRoot ≠ block.blockHeader.transRoot then
    throw <| .BlockException .INVALID_TRANSACTIONS_ROOT

  let receiptsRoot :=
    TransactionReceipt.computeTrieRoot <|
      state.transactionReceipts.map TransactionReceipt.toTrieValue
  if receiptsRoot ≠ some block.blockHeader.receiptRoot then
    throw <| .BlockException .INVALID_RECEIPTS_ROOT

  pure ()

/--
The state effects of a block's body on `s₀`, the state after its parent:
the EIP-4788 and EIP-2935 system calls, the transactions, the withdrawals
and, from Prague, the EIP-7685 requests, which must match the header's
`requestsHash`.
-/
def applyBody
  (fork : Fork)
  (s₀ : State)
  (block : DeserializedBlock)
  : Except Exception State
:= do
  let header := block.blockHeader
  -- Receipts and logs are per block.
  let s₀ := { s₀ with totalGasUsedInBlock := 0, transactionReceipts := .empty, substate := default }
  -- EIP-4788 beacon block root
  let (s, _) ←
    executeSystemCall fork s₀ header BEACON_ROOTS_ADDRESS header.parentBeaconBlockRoot false
  -- EIP-2935 (Prague): parent block hash
  let (s, _) ←
    if fork.spec.eip2935 then
      executeSystemCall fork s header HISTORY_STORAGE_ADDRESS header.parentHash.toByteArray false
    else pure (s, .empty)

  -- Transactions execution
  let (s, _) ←
    block.transactions.array.foldlM
      (λ (s', blobGasUsed) trans ↦ do
        pure
          ( ← applyTransaction fork chainId header blobGasUsed trans s'
          , blobGasUsed + getTotalBlobGas trans
          )
      )
      (s, 0)

  -- Withdrawals execution
  let σ := applyWithdrawals s.accountMap block.withdrawals.array
  let s := { s with accountMap := σ }

  -- EIP-7685 (Prague): requests
  if fork.spec.eip7685 then
    let deposits ←
      (depositRequests s.substate.logSeries).mapError λ _ ↦
        .BlockException .INVALID_DEPOSIT_EVENT_LAYOUT
    let (s, withdrawalRequests) ←
      executeSystemCall fork s header WITHDRAWAL_REQUEST_ADDRESS .empty true
    let (s, consolidationRequests) ←
      executeSystemCall fork s header CONSOLIDATION_REQUEST_ADDRESS .empty true
    let requestsHash ←
      (computeRequestsHash [(0, deposits), (1, withdrawalRequests), (2, consolidationRequests)]).mapError
        λ _ ↦ .BlockException .INVALID_REQUESTS
    if header.requestsHash ≠ some requestsHash then
      throw <| .BlockException .INVALID_REQUESTS
    pure s
  else
    pure s

/--
Applies the RLP-encoded block `rlp` to `s`, whose `executionEnv.blocks` is the
chain history the block extends. The block's fork follows from `config` and
its timestamp. The block executes on the state after its parent, and the
result is the state after the block, with the block appended to the history.
-/
def applyBlock (config : ChainConfig) (s : State) (rlp : ByteArray) : Except Exception State := do
  let (hash, blockHeader, transactions, withdrawals) ← deserializeBlock rlp
  let block : DeserializedBlock := ⟨hash, blockHeader, transactions, withdrawals⟩
  let fork := config.activeFork blockHeader.timestamp
  if fork.spec.eip7934 ∧ rlp.size > MAX_RLP_BLOCK_SIZE then
    throw <| .BlockException .RLP_BLOCK_LIMIT_EXCEEDED
  let parent ← validateHeader fork s.executionEnv.blocks blockHeader
  let s ← applyBody fork { s with accountMap := parent.σ } block
  validateBlock fork s parent.blockHeader block
  pure
    { s with
        executionEnv.blocks :=
          s.executionEnv.blocks.push ⟨hash, blockHeader, s.accountMap⟩
    }

end EVM

end Ethereum
