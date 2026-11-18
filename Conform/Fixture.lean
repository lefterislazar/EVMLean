import Ethereum.State

import Conform.Json

/-!
# Test fixtures

Two fixture formats, which `_info.fixture-format` names:

- `blockchain_test`: the blockchain test format of `ethereum/tests`
  (`BlockchainTests`), which `execution-spec-tests` emits as well. A test is a
  chain of blocks from a genesis block, and the expected state after them.
- `state_test`: a single transaction, run in a block environment on a
  pre-state, and for each fork the expected state root and logs, or the
  exception that rejects the transaction.

A fixture file is a JSON object from test names to tests. Only the fields that
the runner reads are decoded. `config` and `postStateHash` are optional: the
older blockchain tests filled by retesteth have no `config`, and some give the
hash of the post state instead of the state.
-/

namespace Ethereum

namespace Conform

open Lean (FromJson Json)

/-- The expected state after the test's blocks: the accounts, or the state root. -/
inductive PostState where
  | Hash : ByteArray → PostState
  | Map : PersistentAccountMap → PostState
  deriving Inhabited

/--
A block of a fixture: its RLP encoding, and the names of the exceptions with
which it may be rejected. A block is expected to be valid when there are none.
-/
structure FixtureBlock where
  rlp             : ByteArray
  expectException : List String
deriving Inhabited

structure BlockchainTest where
  /-- The fork, or fork transition, such as `PragueToOsakaAtTime15k`. -/
  network       : String
  /-- The `config` object; `{}` when absent. -/
  config        : Json
  pre           : PersistentAccountMap
  genesisRLP    : ByteArray
  blocks        : Array FixtureBlock
  lastblockhash : UInt256
  postState     : PostState
  deriving Inhabited

/-- The block environment in which a state test runs its transaction. -/
structure StateTestEnv where
  coinbase      : AccountAddress
  gasLimit      : ℕ
  number        : ℕ
  timestamp     : ℕ
  difficulty    : ℕ
  /-- `currentRandom`, the `PREVRANDAO` of the block. -/
  prevRandao    : UInt256
  baseFee       : ℕ
  excessBlobGas : ℕ
  /-- EIP-7843 (Amsterdam). -/
  slotNumber    : Option ℕ
  deriving Inhabited

/--
An expected outcome of a state test on a fork: the transaction, encoded as in
a block body, and the state root, logs hash and post-state after it. When
`expectException` is not empty, the transaction is invalid, and the state is
the pre-state.
-/
structure StateTestCase where
  txbytes         : ByteArray
  stateRoot       : ByteArray
  logsHash        : ByteArray
  postState       : Option PersistentAccountMap
  expectException : List String
  deriving Inhabited

structure StateTest where
  env    : StateTestEnv
  /-- The `config` object; `{}` when absent. -/
  config : Json
  pre    : PersistentAccountMap
  /-- The cases of each fork, by fork name, such as `Amsterdam`. -/
  post   : List (String × Array StateTestCase)
  deriving Inhabited

section FromJson

/-
The storage trie has no entries for zero-valued slots, but some fixtures list
such slots explicitly. They are dropped so that they cannot affect the state
root.
-/
instance : FromJson Storage where
  fromJson? json := do
    let storage : Storage ← getObjMap? hexUInt256? json
    pure <| storage.filter fun _ value => value ≠ ⟨0⟩

-- From the fields `balance`, `nonce`, `code` and `storage`.
deriving instance FromJson for PersistentAccountState

instance : FromJson PersistentAccountMap where
  fromJson? := getObjMap? hexAddress?

instance : FromJson FixtureBlock where
  fromJson? json := do
    let exception ← json.getObjValAs? (Option String) "expectException"
    pure {
      rlp             := ← json.getObjValAs? ByteArray "rlp"
      expectException := exception.option [] (·.splitOn "|")
    }

/-- The fixture formats that `_info.fixture-format` names. -/
def blockchainTestFormat : String := "blockchain_test"
def stateTestFormat : String := "state_test"

/-- The format of the fixture test `json`: a blockchain test when it names none. -/
def fixtureFormat (json : Json) : String :=
  (json.getObjVal? "_info" >>= (·.getObjValAs? String "fixture-format")).toOption.getD
    blockchainTestFormat

instance : FromJson BlockchainTest where
  fromJson? json := do
    let format := fixtureFormat json
    if format ≠ blockchainTestFormat then
      throw s!"fixture format {format}, not {blockchainTestFormat}"
    let postState ←
      match json.getObjVal? "postStateHash" with
      | .ok hash => .Hash <$> FromJson.fromJson? hash
      | .error _ => .Map <$> json.getObjValAs? PersistentAccountMap "postState"
    pure {
      network       := ← json.getObjValAs? String "network"
      config        := (·.getD (.obj {})) (← json.getObjValAs? (Option Json) "config")
      pre           := ← json.getObjValAs? PersistentAccountMap "pre"
      genesisRLP    := ← json.getObjValAs? ByteArray "genesisRLP"
      blocks        := ← json.getObjValAs? (Array FixtureBlock) "blocks"
      lastblockhash := ← json.getObjValAs? UInt256 "lastblockhash"
      postState
    }

instance : FromJson StateTestEnv where
  fromJson? json := do
    pure {
      coinbase      := ← json.getObjValAs? String "currentCoinbase" >>= hexAddress?
      gasLimit      := ← getHexNat? json "currentGasLimit"
      number        := ← getHexNat? json "currentNumber"
      timestamp     := ← getHexNat? json "currentTimestamp"
      difficulty    := ← (·.getD 0) <$> optionalHexNat json "currentDifficulty"
      prevRandao    := ← (·.getD ⟨0⟩) <$> json.getObjValAs? (Option UInt256) "currentRandom"
      baseFee       := ← getHexNat? json "currentBaseFee"
      excessBlobGas := ← (·.getD 0) <$> optionalHexNat json "currentExcessBlobGas"
      slotNumber    := ← optionalHexNat json "slotNumber"
    }
  where
    optionalHexNat (json : Json) (k : String) : Except String (Option ℕ) := do
      match ← json.getObjValAs? (Option String) k with
      | some s => some <$> hexNat? s
      | none => pure none

instance : FromJson StateTestCase where
  fromJson? json := do
    let exception ← json.getObjValAs? (Option String) "expectException"
    pure {
      txbytes         := ← json.getObjValAs? ByteArray "txbytes"
      stateRoot       := ← json.getObjValAs? ByteArray "hash"
      logsHash        := ← json.getObjValAs? ByteArray "logs"
      postState       := ← json.getObjValAs? (Option PersistentAccountMap) "state"
      expectException := exception.option [] (·.splitOn "|")
    }

instance : FromJson StateTest where
  fromJson? json := do
    let format := fixtureFormat json
    if format ≠ stateTestFormat then
      throw s!"fixture format {format}, not {stateTestFormat}"
    let post ← (← json.getObjValAs? Json "post").getObj?
    pure {
      env    := ← json.getObjValAs? StateTestEnv "env"
      config := (·.getD (.obj {})) (← json.getObjValAs? (Option Json) "config")
      pre    := ← json.getObjValAs? PersistentAccountMap "pre"
      post   := ← post.toList.mapM fun (fork, cases) => do
        pure (fork, ← Lean.fromJson? cases)
    }

end FromJson

end Conform

end Ethereum
