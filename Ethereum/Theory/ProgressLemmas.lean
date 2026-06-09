import Ethereum.Semantics
import Ethereum.UInt256
import Ethereum.Data.Stack

namespace Ethereum

namespace EVM

lemma Xstep_env_unchanged : ∀ state state' validJumps o,
  Xstep validJumps state = .ok (state', o)
  → state.executionEnv = state'.executionEnv := by
    intro state state' validJumps o hstep
    simp [Xstep] at hstep
    split at hstep
    · contradiction
    · rename_i hZ evmState' cost2 x
      split at hstep
      · simp [bind, Except.bind] at hstep
        split at hstep
        · contradiction
        · split at hstep <;>
            (simp at hstep ; apply And.left at hstep ; rw [← hstep])
      · rename_i hdecode
        simp [bind, Except.bind] at hstep
        split at hstep
        · contradiction
        · split at hstep
          · simp at hstep
            apply And.left at hstep
            rw [← hstep]
          · split at hstep <;>
              (simp at hstep; apply And.left at hstep ; rw [← hstep])

lemma Xstep_X_X_continue : ∀ f state istate validJumps xres,
  Xstep validJumps state = .ok (istate, .none)
  → X f validJumps istate = xres
  → X (f + 1) validJumps state = xres := by
    intros f state istate validJumps xres hstep0 hXf
    simp [X, hstep0, bind, Except.bind]
    rw [← hXf]
    rw [Xstep_env_unchanged state istate validJumps .none hstep0]

lemma Xstep_X_X_halt_success : ∀ f state state' validJumps o,
  Xstep validJumps state = .ok (state', .some (true, o))
  → X (f + 1) validJumps state = .ok (.success state' o) := by
    intros f state state' validJumps o hstep
    unfold X
    simp [hstep, bind, Except.bind]

lemma Xstep_X_X_halt_revert : ∀ f state state' validJumps o,
  Xstep validJumps state = .ok (state', .some (false,o))
  → X (f + 1) validJumps state = .ok (.revert state'.machineState.gasAvailable.toUInt256 o) := by
    intros f state state' validJumps o hstep
    unfold X
    simp [hstep, bind, Except.bind]

lemma Xstep_X_X_except : ∀ f state validJumps e,
  Xstep validJumps state = .error e
  → X (f + 1) validJumps state = .error e := by
    intros f state validJumps e hstep
    unfold X
    simp [hstep, bind, Except.bind]

