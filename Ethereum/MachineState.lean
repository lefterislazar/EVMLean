import Batteries

import Ethereum.Data.Stack
import Ethereum.Maps.ByteMap
import Ethereum.UInt256
import Ethereum.Sat256
import Batteries.Data.HashMap

namespace Ethereum

open Batteries

instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue  h₁ => isTrue <| congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse <| λ h ↦ by cases h; exact (h₂ rfl)


/--
The partial shared `MachineState` `μ`. Section 9.4.1.
- `gasAvailable` `g`
- `memory`       `m`
- `activeWords`  `i` - # active words.
- `returnData`   `o` - Data from the previous call from the current environment.
-/
structure MachineState where
  pc                  : UInt256
  stack       : Stack UInt256
  execLength          : ℕ
  gasAvailable        : Sat256
  activeWords         : UInt256
  memory              : ByteArray
  returnData          : ByteArray
  H_return            : ByteArray
  deriving Inhabited


-- inductive WordSize := | Standard | Single

-- def WordSize.toNat (this : WordSize) : ℕ :=
--   match this with
--     | WordSize.Standard => 32
--     | WordSize.Single   => 1

-- instance : Coe WordSize Nat := ⟨WordSize.toNat⟩

end Ethereum
