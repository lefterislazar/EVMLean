import Ethereum.Block
import Ethereum.Maps.AccountMap
import Ethereum.Pretty

import Conform.Exceptions
import Conform.Fixture
import Conform.Network

/-!
# Running a blockchain test

`run` applies a test's blocks to its pre-state and compares the result with
the expected post-state. It does not depend on where the test comes from.
-/

namespace Ethereum

namespace Conform

def accountOf (acc : PersistentAccountState) : Account :=
  {
    tstorage := ∅
    nonce    := acc.nonce
    balance  := acc.balance
    code     := acc.code
    storage  := acc.storage
  }

def accountMapOf (σ : PersistentAccountMap) : AccountMap :=
  σ.foldl (fun s addr acc => s.insert addr (accountOf acc)) default

def stateOf (σ : PersistentAccountMap) : State :=
  σ.foldl (fun s addr acc => s.setAccount addr (accountOf acc)) default

/-- The accounts of `m₁` that are not in `m₂`, or that differ there. -/
def storageComplement (m₁ m₂ : PersistentAccountMap) : PersistentAccountMap := Id.run do
  let mut result : PersistentAccountMap := m₁
  for ⟨k₂, v₂⟩ in m₂.toList do
    match m₁.get? k₂ with
    | .none => continue
    | .some v₁ => if v₁ == v₂ then result := result.erase k₂ else continue
  return result

/--
Difference between `m₁` and `m₂`, effectively `m₁ / m₂ × m₂ / m₁`: if it is
`(∅, ∅)`, then `m₁ = m₂`.
-/
def storageΔ (m₁ m₂ : PersistentAccountMap) : PersistentAccountMap × PersistentAccountMap :=
  (storageComplement m₁ m₂, storageComplement m₂ m₁)

instance (priority := high) : Repr (PersistentAccountMap) := ⟨λ m _ ↦
  Id.run do
    let mut result := ""
    for (k, v) in m do
      result := result ++ s!"\nAccount[...{(Ethereum.toHex k.toByteArray) /-|>.takeRight 5-/}]\n"
      result := result ++ s!"balance: {v.balance}\nnonce: {v.nonce}\nstorage: \n"
      for (sk, sv) in v.storage do
        result := result ++ s!"{sk} → {sv}\n"
    return result⟩

/-- Why a test failed. -/
inductive Failure where
  /-- The fixture of the test does not decode. -/
  | undecodable : String → Failure
  /-- The model does not support the test's chain configuration. -/
  | unsupportedConfig : String → Failure
  /-- The state root of the genesis block is not the root of the pre-state. -/
  | genesisStateRootMismatch (expected actual : UInt256) : Failure
  /-- A block was rejected with an exception that the test does not expect. -/
  | unexpectedException : EVM.Exception → Failure
  /-- A block that the test expects to be rejected was accepted. -/
  | missedExpectedException : List String → Failure
  /-- The last block applied is not the block `lastblockhash`. -/
  | lastBlockMismatch (expected actual : UInt256) : Failure
  /-- The resulting state differs from the expected one, as described. -/
  | postStateMismatch : String → Failure
  /-- The hash of the logs differs from the expected one. -/
  | logsMismatch (expected : ByteArray) (actual : Option ByteArray) : Failure

instance : ToString Failure where
  toString
    | .undecodable reason => s!"Cannot decode: {reason}"
    | .unsupportedConfig reason => reason
    | .genesisStateRootMismatch expected actual =>
      s!"genesis state root: {hex expected}, root of the pre-state: {hex actual}"
    | .unexpectedException e => s!"{repr e}"
    | .missedExpectedException expected =>
      "Missed expected exception: " ++ String.intercalate "|" expected
    | .lastBlockMismatch expected actual =>
      s!"last block: {hex expected}, last block applied: {hex actual}"
    | .postStateMismatch description => description
    | .logsMismatch expected actual =>
      s!"logs hash: {Ethereum.toHex expected}, actual: {Ethereum.toHex <$> actual}"
  where hex (n : UInt256) : String := Ethereum.toHex n.toByteArray

/--
Applies the test's blocks in order, from the genesis block, whose state root
must be that of the pre-state. A block that the test expects to be invalid
must fail with one of the expected exceptions, and leaves the state unchanged.
-/
def processBlocks
  (config : ChainConfig)
  (pre : PersistentAccountMap)
  (blocks : Array FixtureBlock)
  (genesisRLP : ByteArray)
  : Except Failure State
:= do
  let (genesisHash, genesisBlockHeader, _) ←
    deserializeBlock genesisRLP |>.mapError .unexpectedException
  let preStateRoot : UInt256 := .ofNat <| (stateTrieRoot pre).option 0 fromByteArrayBigEndian
  if preStateRoot ≠ genesisBlockHeader.stateRoot then
    throw <| .genesisStateRootMismatch genesisBlockHeader.stateRoot preStateRoot
  let state₀ :=
    { stateOf pre with
        executionEnv.blocks := #[⟨genesisHash, genesisBlockHeader, accountMapOf pre⟩]
    }
  blocks.foldlM (init := state₀) fun accState block =>
    let expected := block.expectException
    match EVM.applyBlock config accState block.rlp with
    | .ok accState' =>
      if expected.isEmpty then pure accState'
      else throw <| .missedExpectedException expected
    | .error e =>
      let e := selectReportedException expected e
      if acceptsExpectedException expected e then pure accState
      else throw <| .unexpectedException e

/--
Runs `test`: applies its blocks, checks that the last block applied (or the
genesis block, when none is) is the block `lastblockhash`, and compares the
resulting state with the expected post-state.
-/
def run (test : BlockchainTest) : Except Failure Unit := do
  let config ← chainConfig test.network test.config |>.mapError .unsupportedConfig
  let state ← processBlocks config test.pre test.blocks test.genesisRLP
  let lastHash := state.executionEnv.blocks.back?.option ⟨0⟩ (·.hash)
  if lastHash ≠ test.lastblockhash then
    throw <| .lastBlockMismatch test.lastblockhash lastHash
  let actual := state.accountMap.toPersistentAccountMap
  match test.postState with
  | .Map post =>
    unless post == actual do
      let (postSubActual, actualSubPost) := storageΔ post actual
      throw <| .postStateMismatch
        s!"\npost / actual: {repr postSubActual} \nactual / post: {repr actualSubPost}"
  | .Hash h =>
    let root := stateTrieRoot actual
    unless root == some h do
      throw <| .postStateMismatch s!"\npost: {Ethereum.toHex h} \nactual: {Ethereum.toHex <$> root}"

/-! ## State tests -/

/--
The header of the block in which a state test runs its transaction. The fields
that the environment does not give, such as the roots and the parent hash, are
not read by transaction execution.
-/
def StateTestEnv.header (env : StateTestEnv) (fork : Fork) : BlockHeader :=
  { (default : BlockHeader) with
    beneficiary   := env.coinbase
    gasLimit      := env.gasLimit
    number        := env.number
    timestamp     := env.timestamp
    difficulty    := env.difficulty
    prevRandao    := env.prevRandao
    baseFeePerGas := env.baseFee
    excessBlobGas := .ofNat env.excessBlobGas
    slotNumber    := if fork.spec.eip7843 then UInt64.ofNat <$> env.slotNumber else none }

/--
A transaction from its encoding in a block body: the RLP list of a legacy
transaction, or the type byte and RLP payload of a typed one.
-/
def decodeTransaction (bytes : ByteArray) : Except EVM.Exception Transaction := do
  let malformed : EVM.Exception := .TransactionException .RLP_INVALID_VALUE
  let item ←
    if bytes.size > 0 ∧ bytes[0]! ≥ 0xc0 then
      (deserializeRLP bytes).elim (throw malformed) pure
    else pure (.𝔹 bytes)
  match ← deserializeBlock.parseTransactions (.𝕃 [item]) with
  | [transaction] => pure transaction
  | _ => throw malformed

/--
Runs a case of a state test on the fork `forkName`: applies its transaction
to the pre-state in the test's block environment, or checks that it is
rejected with one of the expected exceptions, and compares the resulting
state and logs with the expected ones.
-/
def runStateCase (test : StateTest) (forkName : String) (case : StateTestCase) :
    Except Failure Unit := do
  let config ← chainConfig forkName test.config |>.mapError .unsupportedConfig
  let fork := config.activeFork test.env.timestamp
  let pre := stateOf test.pre
  let expected := case.expectException
  let applied :=
    decodeTransaction case.txbytes >>= fun transaction =>
      EVM.applyTransaction fork config.chainId (test.env.header fork) 0 transaction pre
  let state ←
    match applied with
    | .ok state =>
      if expected.isEmpty then pure state else throw <| .missedExpectedException expected
    | .error e =>
      let e := selectReportedException expected e
      if acceptsExpectedException expected e then pure pre else throw <| .unexpectedException e
  let actual := state.accountMap.toPersistentAccountMap
  if let some post := case.postState then
    unless post == actual do
      let (postSubActual, actualSubPost) := storageΔ post actual
      throw <| .postStateMismatch
        s!"\npost / actual: {repr postSubActual} \nactual / post: {repr actualSubPost}"
  let root := stateTrieRoot actual
  unless root == some case.stateRoot do
    throw <| .postStateMismatch
      s!"\nstate root: {Ethereum.toHex case.stateRoot} \nactual: {Ethereum.toHex <$> root}"
  let logs := if state.transactionReceipts.isEmpty then #[] else
    state.transactionReceipts.back!.logSeries
  let logsHash := KEC <$> RLP (LogSeries.to𝕋 logs)
  unless logsHash == some case.logsHash do
    throw <| .logsMismatch case.logsHash logsHash

end Conform

end Ethereum
