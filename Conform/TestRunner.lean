import Ethereum.State
import Ethereum.Semantics
import Ethereum.Block
import Ethereum.Gas
import Ethereum.Wheels
import Ethereum.Requests

import Ethereum.State.TransactionOps
import Ethereum.State.Withdrawal

import Ethereum.Maps.AccountMap

import Ethereum.Pretty
import Ethereum.Wheels

import Conform.Model
import Conform.TestParser

namespace Ethereum

namespace Conform

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

/--
Applies the fixture's blocks in order. A block that the fixture expects to be
invalid must fail with one of the expected exceptions, and leaves the state
unchanged.
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
  blocks.foldlM (init := state₀)
    λ accState rawBlock ↦ do
      try
        let accState ← EVM.applyBlock config accState rawBlock.rlp
        if ¬rawBlock.exception.isEmpty then
          throw <| .MissedExpectedException rawBlock.exception
        pure accState
      catch e =>
        match e with
          | .MissedExpectedException _  => throw e
          | _ =>
            let e := selectReportedException rawBlock.exception e
            if acceptsExpectedException rawBlock.exception e then
              pure accState
            else
              throw e

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
 
def processTest (entry : TestEntry) : IO TestResult := do
  let result := preImpliesPost entry
  pure <|
    match result with
    | .error err => .mkFailed s!"{repr err}"
    | .ok result => describe <$> result
  where describe : PersistentAccountMap → String := λ σ ↦
          match entry.postState with
            | .Map post =>
              let (postSubActual, actualSubPost) := storageΔ post σ
              s!"\npost / actual: {repr postSubActual} \nactual / post: {repr actualSubPost}"
            | .Hash h =>
              s!"\npost: {Ethereum.toHex h} \nactual: {Ethereum.toHex <$> stateTrieRoot σ}"

/--
Run `tests`, parsing each fixture file once. Every result comes with the
test's running time in milliseconds. A test that cannot be parsed is reported
on stderr and left out.
-/
def processTests (tests : Array TestId) : IO (Array (TestId × TestResult × Nat)) := do
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
  let mut results : Array (TestId × TestResult × Nat) := .empty
  for (path, names) in groups do
    let file ← Lean.Json.fromFile path
    for testName in names do
      let testId := (path, testName)
      match file.getObjValAs? TestEntry testName with
      | .error _ => IO.eprintln s!"Cannot parse: {testId}"
      | .ok test =>
          if (ForkNetwork.parse? test.network).isSome then
            let start ← IO.monoMsNow
            if let some progress := progress then
              IO.FS.withFile progress .append (·.putStrLn s!"start {testName} FROM {path}")
            let res ← processTest test
            let elapsed := (← IO.monoMsNow) - start
            if let some progress := progress then
              IO.FS.withFile progress .append (·.putStrLn s!"done {elapsed}ms {testName}")
            results := results.push (testId, res, elapsed)
  return results

end Conform

end Ethereum
