import Ethereum.State

import Conform.Json

/-!
# Blockchain test fixtures

The blockchain test format of `ethereum/tests` (`BlockchainTests`), which
`execution-spec-tests` emits as the `blockchain_test` fixture format. A fixture
file is a JSON object from test names to tests.

Only the fields that the runner reads are decoded. `config` and
`postStateHash` are optional: the older fixtures filled by retesteth have no
`config`, and some give the hash of the post state instead of the state.
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

/-- The format that `_info.fixture-format` names, when present. -/
def blockchainTestFormat : String := "blockchain_test"

instance : FromJson BlockchainTest where
  fromJson? json := do
    if let .ok format := json.getObjVal? "_info" >>= (·.getObjValAs? String "fixture-format") then
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

end FromJson

end Conform

end Ethereum
