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
  /-- The model does not support the test's chain configuration. -/
  | unsupportedConfig : String → Failure
  /-- A block was rejected with an exception that the test does not expect. -/
  | unexpectedException : EVM.Exception → Failure
  /-- A block that the test expects to be rejected was accepted. -/
  | missedExpectedException : List String → Failure
  /-- The resulting state differs from the expected one, as described. -/
  | postStateMismatch : String → Failure

instance : ToString Failure where
  toString
    | .unsupportedConfig reason => reason
    | .unexpectedException e => s!"{repr e}"
    | .missedExpectedException expected =>
      "Missed expected exception: " ++ String.intercalate "|" expected
    | .postStateMismatch description => description

/--
Applies the test's blocks in order. A block that the test expects to be
invalid must fail with one of the expected exceptions, and leaves the state
unchanged.
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
Runs `test`: applies its blocks, and compares the state after the block
`lastblockhash` (or after the last block, when there is no such block) with
the expected post-state.
-/
def run (test : BlockchainTest) : Except Failure Unit := do
  let config ← chainConfig test.network test.config |>.mapError .unsupportedConfig
  let state ← processBlocks config test.pre test.blocks test.genesisRLP
  let lastAccountMap :=
    state.executionEnv.blocks.findRev? (·.hash == test.lastblockhash)
    |>.option state.accountMap ProcessedBlock.σ
  let actual := lastAccountMap.toPersistentAccountMap
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

end Conform

end Ethereum
