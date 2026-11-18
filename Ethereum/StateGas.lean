import Ethereum.State.Substate

/-!
# The state-gas meter (EIP-8037, Amsterdam)

From Amsterdam, creating state is charged in a second dimension, state gas,
priced per byte of state it creates. A transaction's gas beyond the execution
gas it can spend (`GasConstants.TX_MAX_GAS_LIMIT`) is a reservoir of state gas.
A state charge draws from the reservoir first, then from the frame's execution
gas: that part is the frame's *spill*.

The reservoir and the spill are in the substate (`Substate.stateGasReservoir`,
`Substate.stateGasSpilled`), which a child frame receives and a failed one
gives back. This gives the execution specs' frame protocol (`vm/gas.py`,
`GasMeter`): a child receives the whole reservoir, a failed child returns the
reservoir it received, and a successful one returns its reservoir and adds its
spill to its parent's. What the substate does not give, the frames do: a
reverted frame returns its own spill as execution gas, and a parent repays its
spill from the reservoir after a successful child.

The functions here are those of the specs, on the execution gas `gas` of a
frame and its substate. A frame's own spill is the substate's spill less its
value at the frame's entry, `spillBaseline`.
-/

namespace Ethereum

namespace StateGas

/-- The state-gas price of a byte of state. -/
def COST_PER_STATE_BYTE : ℕ := 1530
/-- A storage slot set from zero: 64 bytes. -/
def STORAGE_SET : ℕ := 64 * COST_PER_STATE_BYTE
/-- A new account: 120 bytes. -/
def NEW_ACCOUNT : ℕ := 120 * COST_PER_STATE_BYTE
/-- A delegation set by an authorization: 23 bytes. -/
def AUTH_BASE : ℕ := 23 * COST_PER_STATE_BYTE

/-- The reservoir of a system call: enough for the storage slots that a
    system contract sets in one call, at most 16. -/
def SYSTEM_RESERVOIR : ℕ := STORAGE_SET * 16

/--
Charges `amount` of state gas (`charge_state_gas`): from the reservoir, and
what it does not cover from the execution gas `gas`, as spill. `none`, with
nothing charged, when the two do not cover it.
-/
def charge (gas : ℕ) (A : Substate) (amount : ℕ) : Option (ℕ × Substate) :=
  if amount ≤ A.stateGasReservoir then
    some (gas, { A with stateGasReservoir := A.stateGasReservoir - amount })
  else
    let spill := amount - A.stateGasReservoir
    if spill ≤ gas then
      some (gas - spill,
        { A with stateGasReservoir := 0, stateGasSpilled := A.stateGasSpilled + spill })
    else none

/-- The spill of the frame whose spill at entry was `spillBaseline`. -/
def ownSpill (A : Substate) (spillBaseline : ℕ) : ℕ :=
  A.stateGasSpilled - spillBaseline

/--
Credits back `amount` of state gas charged earlier in the frame
(`credit_state_gas_refund`): to the frame's spill first, last in first out,
whose execution gas is returned, then to the reservoir. Unlike a refund, it is
not capped.
-/
def credit (gas : ℕ) (A : Substate) (spillBaseline amount : ℕ) : ℕ × Substate :=
  let x := min amount (ownSpill A spillBaseline)
  (gas + x,
    { A with
      stateGasSpilled := A.stateGasSpilled - x
      stateGasReservoir := A.stateGasReservoir + (amount - x) })

/--
Repays the frame's spill from the reservoir (`repay_state_gas_spill`), after
a child returned successfully with what is left of the reservoir.
-/
def repaySpill (gas : ℕ) (A : Substate) (spillBaseline : ℕ) : ℕ × Substate :=
  let r := min A.stateGasReservoir (ownSpill A spillBaseline)
  (gas + r,
    { A with
      stateGasReservoir := A.stateGasReservoir - r
      stateGasSpilled := A.stateGasSpilled - r })

end StateGas

end Ethereum
