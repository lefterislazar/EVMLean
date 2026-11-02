import Ethereum.State
import Ethereum.Semantics
import Ethereum.Transaction
import Ethereum.Gas
import Ethereum.Wheels
import Ethereum.Requests

import Ethereum.State.TransactionOps
import Ethereum.State.Withdrawal

import Ethereum.Maps.AccountMap

import Ethereum.Pretty
import Ethereum.Wheels

import Conform.Exception
import Conform.Model
import Conform.TestParser

namespace Ethereum

namespace Conform

def VerySlowTests : Array String := #[]

def GlobalBlacklist : Array String := VerySlowTests

abbrev TestId : Type := System.FilePath × String

def PersistentAccountMap.toAccountMap (self : PersistentAccountMap) : AccountMap :=
  self.foldl addAccount default
  where addAccount s addr acc :=
    let account : Account :=
      {
        tstorage := ∅
        nonce    := acc.nonce
        balance  := acc.balance
        code     := acc.code
        storage  := acc.storage
      }
    s.insert addr account

def PersistentAccountMap.toEVMState (self : PersistentAccountMap) : State :=
  self.foldl addAccount default
  where addAccount s addr acc :=
    let account : Account :=
      {
        tstorage := ∅
        nonce    := acc.nonce
        balance  := acc.balance
        code     := acc.code
        storage  := acc.storage
      }
    s.setAccount addr account

def Pre.toEVMState : Pre → State := PersistentAccountMap.toEVMState

def TestMap.toTests (self : TestMap) : List (String × TestEntry) := self.toList

def Post.toEVMState : Post → State := PersistentAccountMap.toEVMState

local instance : Inhabited EVM.Transformer where
  default := λ _ ↦ default

private def compareWithEVMdefaults (s₁ s₂ : Ethereum.Storage) : Bool :=
  withDefault s₁ == withDefault s₂
  where
    withDefault (s : Ethereum.Storage) : Ethereum.Storage := if s.contains ⟨0⟩ then s else s.insert ⟨0⟩ ⟨0⟩

/--
TODO - This should be a generic map complement, but we are not trying to write a library here.

Now that this is not a `Finmap`, this is probably defined somewhere in the API, fix later.
-/
def storageComplement (m₁ m₂ : PersistentAccountMap) : PersistentAccountMap := Id.run do
  let mut result : PersistentAccountMap := m₁
  for ⟨k₂, v₂⟩ in m₂.toList do
    match m₁.get? k₂ with
    | .none => continue
    | .some v₁ => if v₁ == v₂ then result := result.erase k₂ else continue
  return result

/--
Difference between `m₁` and `m₂`.
Effectively `m₁ / m₂ × m₂ / m₁`.

- if the `Δ = (∅, ∅)`, then `m₁ = m₂`
- used for reporting delta between expected post state and the actual state post execution

Now that this is not a `Finmap`, this is probably defined somewhere in the API, fix later.
-/
def storageΔ (m₁ m₂ : PersistentAccountMap) : PersistentAccountMap × PersistentAccountMap :=
  (storageComplement m₁ m₂, storageComplement m₂ m₁)

section

/--
This section exists for debugging / testing mostly. It's somewhat ad-hoc.
-/

private def almostBEqButNotQuiteEthereumState (s₁ s₂ : PersistentAccountMap) : Except String Bool := do
  if s₁ == s₂ then .ok true else throw "state mismatch"

/--
NB it is ever so slightly more convenient to be in `Except String Bool` here rather than `Option String`.

This is morally `s₁ == s₂` except we get a convenient way to both tune what is being compared
as well as report fine grained errors.
-/
private def almostBEqButNotQuite (s₁ s₂ : PersistentAccountMap) : Except String Bool := do
  discard <| almostBEqButNotQuiteEthereumState s₁ s₂
  pure true -- Yes, we never return false, because we throw along the way. Yes, this is `Option`.

end

/-
  `baseFeePerGas`, `gasLimit` and `excessBlobGas` are used in transaction
  validation, so have to validated before.
-/
def validateHeaderBeforeTransactions
  (fork : Fork)
  (blocks : ProcessedBlocks)
  (header : BlockHeader)
  : Except EVM.Exception ProcessedBlock
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

def validateBlock
  (fork : Fork)
  (state : State)
  (parentHeader : BlockHeader)
  (block : DeserializedBlock)
  : Except EVM.Exception Unit
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
Older fillers in `ethereum/tests` v17.2 use `TR_*` and short labels for the
same condition as the `TransactionException.*` / `BlockException.*` names.
A reported exception is accepted when the fixture lists either form.
-/
def legacyExceptionNames (reported : String) : List String :=
  match reported with
  -- The execution specs raise one error for both intrinsic gas bounds
  -- (EIP-7623); some fixtures name it after the regular bound.
  | "TransactionException.INTRINSIC_GAS_BELOW_FLOOR_GAS_COST" =>
      ["TransactionException.INTRINSIC_GAS_TOO_LOW"]
  | "TransactionException.INTRINSIC_GAS_TOO_LOW" =>
      ["TR_IntrinsicGas", "IntrinsicGas", "TR_NoFundsOrGas"]
  | "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS" =>
      ["TR_NoFunds", "TR_NoFundsX", "TR_NoFundsOrGas", "SenderNotEOAorNoCASH",
        "TR_FeeCapLessThanBlocksORNoFunds"]
  | "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS" =>
      ["TR_FeeCapLessThanBlocks", "TR_FeeCapLessThanBlocksORGasLimitReached",
        "TR_FeeCapLessThanBlocksORNoFunds"]
  | "TransactionException.GAS_ALLOWANCE_EXCEEDED" =>
      ["TR_GasLimitReached", "TR_FeeCapLessThanBlocksORGasLimitReached"]
  | "TransactionException.NONCE_IS_MAX" => ["TR_NonceHasMaxValue"]
  | "TransactionException.NONCE_MISMATCH_TOO_HIGH" => ["TR_NonceTooHigh"]
  | "TransactionException.NONCE_MISMATCH_TOO_LOW" => ["TR_NonceTooLow"]
  | "TransactionException.PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS" => ["TR_TipGtFeeCap"]
  | "TransactionException.INITCODE_SIZE_EXCEEDED" => ["TR_InitCodeLimitExceeded"]
  | "TransactionException.TYPE_3_TX_ZERO_BLOBS" => ["TR_EMPTYBLOB"]
  | "TransactionException.TYPE_3_TX_CONTRACT_CREATION" => ["TR_BLOBCREATE"]
  | "TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH" => ["TR_BLOBVERSION_INVALID"]
  | "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED" => ["TR_BLOBLIST_OVERSIZE"]
  | "TransactionException.SENDER_NOT_EOA" => ["SenderNotEOA", "SenderNotEOAorNoCASH"]
  | "TransactionException.RLP_INVALID_VALUE" => ["TR_RLP_WRONGVALUE"]
  | "BlockException.IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS" => ["PostParisUncleHashIsNotEmpty"]
  | "BlockException.INVALID_GASLIMIT" => ["InvalidGasLimit", "InvalidGasLimit2"]
  | "BlockException.GASLIMIT_TOO_BIG" => ["InvalidGasLimit"]
  | "BlockException.INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT" => ["InvalidTimestampOlderParent"]
  | "BlockException.EXTRA_DATA_TOO_BIG" => ["ExtraDataTooBig"]
  | "BlockException.INVALID_WITHDRAWALS_ROOT" => ["InvalidWithdrawals"]
  | "BlockException.INVALID_BLOCK_NUMBER" => ["InvalidNumber"]
  | "BlockException.INVALID_STATE_ROOT" => ["InvalidStateRoot"]
  | "BlockException.INVALID_BASEFEE_PER_GAS" => ["1559BlockImportImpossible_BaseFeeWrong"]
  | "BlockException.GAS_USED_OVERFLOW" => ["TooMuchGasUsed"]
  | "BlockException.INVALID_RECEIPTS_ROOT" => ["InvalidReceiptsStateRoot"]
  | "BlockException.INVALID_TRANSACTIONS_ROOT" => ["InvalidTransactionsRoot"]
  | "BlockException.UNKNOWN_PARENT" => ["UnknownParent"]
  | "BlockException.UNKNOWN_PARENT_ZERO" => ["UnknownParent2"]
  | "BlockException.INVALID_LOG_BLOOM" => ["InvalidLogBloom"]
  | "BlockException.IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS" => ["PostParisDifficultyIsNot0"]
  | "BlockException.INVALID_GAS_USED" => ["InvalidGasUsed"]
  | "BlockException.RLP_STRUCTURES_ENCODING" => ["RLP_ExpectedAsList"]
  | _ => []

/--
Before Osaka, a transaction with more blobs than the block maximum breaks both
caps: the per-transaction blob count and the block blob-gas allowance.
Validation reports the count error first. When the fixture instead names the block allowance, report that name.
The two errors stay distinct for every other case, including several transactions
whose blob counts are each at most six but sum past the block cap.
-/
def selectReportedException (expected : List String) (e : EVM.Exception) : EVM.Exception :=
  match e with
  | .TransactionException .TYPE_3_TX_BLOB_COUNT_EXCEEDED =>
    if expected.contains "TransactionException.TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED" then
      .TransactionException .TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED
    else
      e
  | _ => e

def acceptsExpectedException (expected : List String) (e : EVM.Exception) : Bool :=
  let reported := (repr e).pretty
  expected.contains reported || (legacyExceptionNames reported).any expected.contains

def deserializeRawBlock (rawBlock : RawBlock)
  : Except EVM.Exception DeserializedBlock
:= do
  let (blockHash, blockHeader, transactions, withdrawals) ← deserializeBlock rawBlock.rlp
  pure <| .mk blockHash blockHeader transactions withdrawals rawBlock.exception

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
  : Except EVM.Exception (State × ByteArray)
:= do
  let code := s.accountMap.get? contract |>.option .empty (·.code)
  if code.isEmpty then
    if checked then throw <| .BlockException .SYSTEM_CONTRACT_EMPTY
    return (s, .empty)
  let (σ, _, _, success, output) :=
    EVM.Θ fork
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
This assumes that the `transactions` are ordered, as they should be in the test suit.
-/
def processBlocks
  (config : ChainConfig)
  (pre : Pre)
  (blocks : RawBlocks)
  (genesisRLP : ByteArray)
  : Except EVM.Exception State
:= do
  let (genesisHash, genesisBlockHeader, _) ← deserializeBlock genesisRLP
  let state₀ :=
    { pre.toEVMState with
        executionEnv.blocks :=
          #[
            ⟨ genesisHash
            , genesisBlockHeader
            , PersistentAccountMap.toAccountMap pre
            ⟩
          ]
    }
  let state ←
    blocks.foldlM (init := state₀)
      λ accState rawBlock ↦ do
        try
          let block ← deserializeRawBlock rawBlock
          let fork := config.activeFork block.blockHeader.timestamp
          if fork.spec.eip7934 ∧ rawBlock.rlp.size > MAX_RLP_BLOCK_SIZE then
            throw <| .BlockException .RLP_BLOCK_LIMIT_EXCEEDED
          let parent ←
            validateHeaderBeforeTransactions fork accState.executionEnv.blocks block.blockHeader
          let accState ← processBlock fork {accState with accountMap := parent.σ} block
          validateBlock fork accState parent.blockHeader block
          if ¬block.exception.isEmpty then
            throw <| .MissedExpectedException block.exception
          pure
            { accState with
                executionEnv.blocks :=
                  accState.executionEnv.blocks.push
                    ⟨block.hash, block.blockHeader, accState.accountMap⟩
            }
        catch e =>
          match e with
            | .MissedExpectedException _  => throw e
            | _ =>
              let e := selectReportedException rawBlock.exception e
              if acceptsExpectedException rawBlock.exception e then
                pure accState
              else
                throw e
  pure state
 where
  processBlock
    (fork : Fork)
    (s₀ : State)
    (block : DeserializedBlock)
    : Except EVM.Exception State
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
            ( ← EVM.applyTransaction fork chainId header blobGasUsed trans s'
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
- `.none` on success
- `.some endState` on failure

NB we can throw away the final state if it coincided with the expected one, hence `.none`.
-/
def preImpliesPost (entry : TestEntry)
  : Except EVM.Exception (Option (PersistentAccountMap))
:= do
    let resultState ← processBlocks entry.config entry.pre entry.blocks entry.genesisRLP
    let lastAccountMap :=
      resultState.executionEnv.blocks.findRev? (·.hash == entry.lastblockhash)
      |>.option resultState.accountMap ProcessedBlock.σ
    let result : PersistentAccountMap := lastAccountMap.toPersistentAccountMap
    let persistentAccountMap := resultState.accountMap.toPersistentAccountMap
    match entry.postState with
      | .Map post =>
        match almostBEqButNotQuite post result with
          | .error e =>
            dbg_trace e
            pure (.some persistentAccountMap) -- Feel free to inspect this error from `almostBEqButNotQuite`.
          | .ok _ => pure .none
      | .Hash h =>
        if stateTrieRoot persistentAccountMap ≠ h then
          dbg_trace "state hash mismatch"
          pure (.some persistentAccountMap)
        else
          pure .none

instance (priority := high) : Repr (PersistentAccountMap) := ⟨λ m _ ↦
  Id.run do
    let mut result := ""
    for (k, v) in m do
      result := result ++ s!"\nAccount[...{(Ethereum.toHex k.toByteArray) /-|>.takeRight 5-/}]\n"
      result := result ++ s!"balance: {v.balance}\nnonce: {v.nonce}\nstorage: \n"
      for (sk, sv) in v.storage do
        result := result ++ s!"{sk} → {sv}\n"
    return result⟩
 
def processTest (entry : TestEntry) (isTimed : Option (Nat × TestId) := .none) (verbose := true) : IO TestResult := do
  let tα ← if isTimed.isSome then IO.monoMsNow else pure 0
  let result := preImpliesPost entry
  let tω ← if isTimed.isSome then IO.monoMsNow else pure 0
  if let .some (thread, filepath, testname) := isTimed then
    IO.eprint s!"#{if thread / 10 == 1 then "" else " "}{thread} "
    IO.eprint s!"{testname} FROM {System.FilePath.mk (filepath.components.drop 3 |>.intersperse "/" |>.foldl (·++·) "")} "
    IO.eprintln s!"took: {(tω - tα).toFloat / 1000.0}s"
  pure <|
    match result with
    | .error err => .mkFailed s!"{repr err}"
    | .ok result => errorF <$> result
  where discardError : PersistentAccountMap → String := λ _ ↦ "ERROR."
        verboseError : PersistentAccountMap → String := λ σ ↦
          match entry.postState with
            | .Map post =>
              let (postSubActual, actualSubPost) := storageΔ post σ
              s!"\npost / actual: {repr postSubActual} \nactual / post: {repr actualSubPost}"
            | .Hash h =>
              s!"\npost: {Ethereum.toHex h} \nactual: {Ethereum.toHex <$> stateTrieRoot σ}"
        errorF := if verbose then verboseError else discardError

/--
Run `tests`, parsing each fixture file once. Every result comes with the
test's running time in milliseconds.
-/
def processTests (tests : Array TestId) (isTimed : Option Nat := .none) :
                 IO (Array TestId × Array (TestId × TestResult × Nat)) := do
  let mut groups : Array (System.FilePath × Array String) := #[]
  let mut idx : Std.HashMap System.FilePath Nat := ∅
  for (path, name) in tests do
    match idx.get? path with
    | some i =>
        groups := groups.modify i fun (p, names) => (p, names.push name)
    | none =>
        idx := idx.insert path groups.size
        groups := groups.push (path, #[name])
  -- `CONFORM_PROGRESS` names a file that records each test as it starts and
  -- finishes, to see which tests are running.
  let progress := (← IO.getEnv "CONFORM_PROGRESS").map System.FilePath.mk
  let mut discarded : Array TestId := .empty
  let mut results : Array (TestId × TestResult × Nat) := .empty
  for (path, names) in groups do
    let file ← Lean.Json.fromFile path
    for testName in names do
      let testId := (path, testName)
      let test := Except.mapError Conform.Exception.CannotParse <| file.getObjValAs? TestEntry testName
      match test with
      | .error _ => IO.eprintln s!"Cannot parse: {testId}"
                    discarded := discarded.push testId
      | .ok test =>
          if (ForkNetwork.parse? test.network).isSome then
            let start ← IO.monoMsNow
            if let some progress := progress then
              IO.FS.withFile progress .append (·.putStrLn s!"start {testName} FROM {path}")
            let res ← processTest test <| isTimed <&> (·, testId)
            let elapsed := (← IO.monoMsNow) - start
            if let some progress := progress then
              IO.FS.withFile progress .append (·.putStrLn s!"done {elapsed}ms {testName}")
            results := results.push (testId, res, elapsed)
  return (discarded, results)

end Conform

end Ethereum
