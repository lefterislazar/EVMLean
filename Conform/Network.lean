import Ethereum.Fork

import Conform.Json

/-!
# Fixture networks

The chain configuration of a fixture, from its `network` name and its optional
`config` object.
-/

namespace Ethereum

namespace Conform

open Lean (Json)

/-- The fork named `s` in a fixture, such as `Prague`. -/
def parseFork? (s : String) : Option Fork := Fork.all.find? (·.name == s)

/--
The network named `s` in a fixture: a fork, such as `Prague`, or a transition
between forks at timestamp 15000, such as `PragueToOsakaAtTime15k`.
-/
def parseNetwork? (s : String) : Option ForkNetwork :=
  match parseFork? s with
  | some fork => some (.fixed fork)
  | none => Id.run do
    for before in Fork.all do
      for after in Fork.all do
        if s == before.name ++ "To" ++ after.name ++ "AtTime15k" then
          return some (.transition before after 15000)
    return none

/--
The chain configuration of a fixture with the network `networkName` and the
`config` object `config`. The model fixes the chain id and the blob schedule
of each fork, so a fixture whose `config` disagrees is rejected.
-/
def chainConfig (networkName : String) (config : Json) : Except String ChainConfig := do
  let some network := parseNetwork? networkName
    | throw s!"unsupported network: {networkName}"
  let chainId ←
    match config.getObjVal? "chainid" with
    | .ok _ => getHexNat? config "chainid"
    | .error _ => pure 1
  if chainId ≠ Ethereum.chainId then
    throw s!"unsupported chain id: {chainId}"
  let schedules := (·.getD (.obj {})) (← config.getObjValAs? (Option Json) "blobSchedule")
  for fork in Fork.all do
    if let .ok entry := schedules.getObjVal? fork.name then
      let schedule : BlobSchedule := {
        targetBlobs := ← getHexNat? entry "target"
        maxBlobs := ← getHexNat? entry "max"
        baseFeeUpdateFraction := ← getHexNat? entry "baseFeeUpdateFraction"
      }
      if schedule ≠ fork.spec.blobSchedule then
        throw s!"blob schedule of {fork.name} differs from the model"
  pure { network, chainId }

end Conform

end Ethereum
