import Ethereum.Fork

namespace Ethereum

namespace Conform

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

end Conform

end Ethereum
