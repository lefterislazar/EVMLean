import Lean.Data.Json

import Ethereum.Wheels
import Ethereum.Operations
import Ethereum.Semantics
import Ethereum.Wheels
import Ethereum.State.Withdrawal

import Conform.Model
import Conform.Network
import Conform.Wheels

namespace Ethereum

namespace Conform

namespace Parser

section FromJson

open Lean (FromJson Json)

@[reducible] private def fromBlobString {α} (f : Blob → Except String α) : FromJson α :=
  {
    fromJson? := λ json ↦ json.getStr? >>= (getBlob? · >>= f)
  }

instance : FromJson UInt256 := fromBlobString UInt256.fromBlob?
instance : FromJson ℕ := fromBlobString Nat.fromBlob?

instance : FromJson AccountAddress := fromBlobString AccountAddress.fromBlob?

private def getObjValsExt?
    (json : Json) (α β : Type) [Ord α]
    [Std.TransCmp (compare : α → α → Ordering)] [FromJson α] [FromJson β] :
    Except String (Std.ExtTreeMap α β compare) := do
  let vals ← json.getObjVals? α β
  pure <| vals.toList.foldl (fun acc (key, value) => acc.insert key value) ∅

/-
The storage trie has no entries for zero-valued slots, but some fixtures list
such slots explicitly. They are dropped so that they cannot affect the state
root.
-/
instance : FromJson Storage where
  fromJson? json := do
    let storage ← getObjValsExt? json UInt256 UInt256
    pure <| storage.filter fun _ value => value ≠ ⟨0⟩

instance : FromJson ByteArray := fromBlobString (ByteArray.ofBlob)

instance : FromJson (PersistentAccountState) where
  fromJson? json := do
    pure {
      balance := ← json.getObjValAs? UInt256 "balance"
      nonce   := ← json.getObjValAs? UInt256 "nonce"
      code    := ← json.getObjValAs? Code    "code"
      storage := ← json.getObjValAs? Storage "storage"
    }

instance : FromJson Pre where
  fromJson? json := getObjValsExt? json AccountAddress PersistentAccountState

/--
- Format₀: `EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json`
- Format₁: `EthereumTests/BlockchainTests/GeneralStateTests/Pyspecs/cancun/eip4844_blobs/invalid_static_excess_blob_gas.json`
-/
private def blockOfJson (json : Json) : Except String FixtureBlock := do
  -- The exception, if exists, is always in the outermost object regardless of the `<Format>` (see this function's docs).
  let exception ← json.getObjValAsD! (Option String) "expectException"
  let rlp ← json.getObjValAsD! ByteArray "rlp"
  pure {
    rlp
    expectException := exception.option [] (·.splitOn "|")
  }

instance : FromJson FixtureBlock := ⟨blockOfJson⟩

/--
The chain configuration of a fixture. The model fixes the blob schedule of
each fork, so a fixture whose `config.blobSchedule` disagrees is rejected.
-/
def parseChainConfig (json : Json) (networkName : String) : Except String ChainConfig := do
  let some network := parseNetwork? networkName
    | throw s!"unsupported network: {networkName}"
  let config ← json.getObjValAsD Json "config" (.obj {})
  let chainId ←
    match config.getObjVal? "chainid" with
    | .ok value => FromJson.fromJson? value
    | .error _ => pure 1
  if chainId ≠ Ethereum.chainId then
    throw s!"unsupported chain id: {chainId}"
  let schedules ← config.getObjValAsD Json "blobSchedule" (.obj {})
  for fork in Fork.all do
    if let .ok entry := schedules.getObjVal? fork.name then
      let schedule : BlobSchedule := {
        targetBlobs := ← entry.getObjValAs? ℕ "target"
        maxBlobs := ← entry.getObjValAs? ℕ "max"
        baseFeeUpdateFraction := ← entry.getObjValAs? ℕ "baseFeeUpdateFraction"
      }
      if schedule ≠ fork.spec.blobSchedule then
        throw s!"blob schedule of {fork.name} differs from the model"
  pure { network, chainId }

instance : FromJson TestEntry where
  fromJson? json := do
    let post : PostState ←
      match json.getObjVal? "postStateHash" with
        | .error _ =>
          .Map <$> json.getObjValAsD! (PersistentAccountMap) "postState"
        | .ok postStateHash =>
          .Hash <$> FromJson.fromJson? postStateHash
    pure {
      info               := ← json.getObjValAs? Json "info"
      blocks             := ← json.getObjValAs? (Array FixtureBlock) "blocks"
      genesisRLP         := ← json.getObjValAs? ByteArray "genesisRLP"
      lastblockhash      := ← json.getObjValAs? UInt256 "lastblockhash"
      network            := ← json.getObjValAs? String "network"
      config             := ← parseChainConfig json (← json.getObjValAs? String "network")
      postState          := post
      pre                := ← json.getObjValAs? Pre "pre"
      sealEngine         := ← json.getObjValAs? Json "sealEngine"
    }

instance : FromJson TestMap where
  fromJson? json := json.getObjVals? String TestEntry

end FromJson

end Parser

end Conform

end Ethereum
