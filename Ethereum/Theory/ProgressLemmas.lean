import Ethereum.Semantics
import Ethereum.UInt256
import Ethereum.Data.Stack

import Ethereum.Theory.NoOutOfFuel

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
  Xstep validJumps state = .ok (state', .some (HaltCause.success, o))
  → X (f + 1) validJumps state = .ok (.success state' o) := by
    intros f state state' validJumps o hstep
    unfold X
    simp [hstep, bind, Except.bind]

lemma Xstep_X_X_halt_revert : ∀ f state state' validJumps o,
  Xstep validJumps state = .ok (state', .some (HaltCause.revert,o))
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

-- inductive Xstep_rel validJumps :  State → Except ExecutionException (State × Option (HaltCause × ByteArray)) → Prop where
--   | intro {s} :
--     Xstep_rel validJumps s (Xstep validJumps s)

  
inductive XstepN validJumps : State → Except ExecutionException (State × Option (HaltCause × ByteArray)) → ℕ → Prop where
  | step : ∀ s s',
    -- Xstep_rel validJumps s s' →
    Xstep validJumps s = s' →
    XstepN validJumps s s' 1
  | trans : ∀ s s' x' n,
    -- Xstep_rel validJumps s (.ok (s', .none)) →
    Xstep validJumps s = .ok (s', .none) →
    XstepN validJumps s' x' n →
    XstepN validJumps s x' (n + 1)

lemma XstepN_X_continue {s s' n f xres} validJumps :
    XstepN validJumps s (.ok (s', .none)) n →
    X f validJumps s' = xres →
    X (f + n) validJumps s = xres := by
    intro hstepN hX
    generalize hxi : (Except.ok (s', none)) = xi
    rw [hxi] at hstepN
    induction hstepN with
    | step s is hstep =>
      rw [← hxi] at hstep
      exact Xstep_X_X_continue f s s' validJumps xres hstep hX
    | trans s s' x' n hstep hnsucc ih =>
      unfold X  
      simp [bind, Except.bind, hstep]
      apply ih at hxi
      simp [← hxi]
      rw [Xstep_env_unchanged s s' validJumps .none hstep]

lemma XstepN_X_halt_success {s s' o n f} validJumps :
    XstepN validJumps s (.ok (s', .some (.success, o))) n →
    X (f + n) validJumps s = .ok (.success s' o) := by
    intro hstepN
    generalize hxi : (Except.ok (s', Option.some (HaltCause.success, o))) = xi
    rw [hxi] at hstepN
    induction hstepN with
    | step s is hstep =>
      rw [← hxi] at hstep
      exact Xstep_X_X_halt_success f s s' validJumps o hstep
    | trans s s' x' n hstep hnsucc ih =>
      unfold X  
      simp [bind, Except.bind, hstep]
      apply ih at hxi
      simp [← hxi]
      rw [Xstep_env_unchanged s s' validJumps .none hstep]

lemma XstepN_X_halt_revert {s s' o n f} validJumps :
    XstepN validJumps s (.ok (s', .some (.revert, o))) n →
    X (f + n) validJumps s = .ok (.revert s'.machineState.gasAvailable.toUInt256 o) := by
    intro hstepN
    generalize hxi : (Except.ok (s', Option.some (HaltCause.revert, o))) = xi
    rw [hxi] at hstepN
    induction hstepN with
    | step s is hstep =>
      rw [← hxi] at hstep
      exact Xstep_X_X_halt_revert f s s' validJumps o hstep
    | trans s s' x' n hstep hnsucc ih =>
      unfold X  
      simp [bind, Except.bind, hstep]
      apply ih at hxi
      simp [← hxi]
      rw [Xstep_env_unchanged s s' validJumps .none hstep]

lemma XstepN_XstepN_add { s s' n x m} validJumps :
    XstepN validJumps s (.ok (s', .none)) n →
    XstepN validJumps s' x m →
    XstepN validJumps s x (n + m) := by
  intro hstepn hstepm
  generalize hxi : (Except.ok (s', none)) = xi
  rw [hxi] at hstepn
  induction hstepn with
  | step s is hstep =>
    rw [← hxi] at hstep
    rw [Nat.add_comm]
    exact XstepN.trans s s' x m hstep hstepm
  | trans s is x' n hstep hnsucc ih =>
    apply ih at hxi
    rw [Nat.add_comm]
    rw [Nat.add_comm] at hxi
    exact XstepN.trans s is x (m + n) hstep hxi

lemma XstepN_gas_lt_fuel_of_Xstep_ret_none {s s' n f} validJumps :
    s.machineState.gasAvailable.toNat < f + n →
    XstepN validJumps s (.ok (s', .none)) n →
    s'.machineState.gasAvailable.toNat < f := by
  intro hgas0 hstep
  generalize hxi : (Except.ok (s', Option.none)) = xs'
  rw [hxi] at hstep
  induction hstep with
  | step h _ hstep =>
    rw [←  hxi] at hstep
    apply Xstep_gas_decreases_of_continues at hstep
    omega
  | trans is is' ixs n' hstep1 hstep' ih =>
    apply Xstep_gas_decreases_of_continues at hstep1
    have h := Nat.lt_of_le_of_lt hstep1 hgas0
    rw [← Nat.add_assoc] at h
    apply Nat.lt_of_add_lt_add_right at h
    apply ih h hxi

