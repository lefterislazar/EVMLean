import Ethereum.Semantics

/-!
# The state-gas operations of a frame (EIP-8037)

`creditStateGas`, `repayStateGasSpill` and `settleChildStateGas` change only
the execution gas and the state-gas meter of a frame (`Substate.stateGasReservoir`,
`Substate.stateGasSpilled`); a state charge that succeeds
(`chargeStateGas`, `sstoreStateGas`) also changes nothing else.
-/

namespace Ethereum
namespace EVM

/-- `s'` is `s` but for the execution gas and the state-gas meter. -/
structure SameButGas (s s' : State) : Prop where
  accountMap : s'.accountMap = s.accountMap
  σ₀ : s'.σ₀ = s.σ₀
  totalGasUsedInBlock : s'.totalGasUsedInBlock = s.totalGasUsedInBlock
  transactionReceipts : s'.transactionReceipts = s.transactionReceipts
  executionEnv : s'.executionEnv = s.executionEnv
  executionGasUsedInBlock : s'.executionGasUsedInBlock = s.executionGasUsedInBlock
  stateGasUsedInBlock : s'.stateGasUsedInBlock = s.stateGasUsedInBlock
  machineState_pc : s'.machineState.pc = s.machineState.pc
  machineState_stack : s'.machineState.stack = s.machineState.stack
  machineState_execLength : s'.machineState.execLength = s.machineState.execLength
  machineState_activeWords : s'.machineState.activeWords = s.machineState.activeWords
  machineState_memory : s'.machineState.memory = s.machineState.memory
  machineState_returnData : s'.machineState.returnData = s.machineState.returnData
  machineState_H_return : s'.machineState.H_return = s.machineState.H_return
  substate_selfDestructSet : s'.substate.selfDestructSet = s.substate.selfDestructSet
  substate_touchedAccounts : s'.substate.touchedAccounts = s.substate.touchedAccounts
  substate_refundBalance : s'.substate.refundBalance = s.substate.refundBalance
  substate_accessedAccounts : s'.substate.accessedAccounts = s.substate.accessedAccounts
  substate_accessedStorageKeys : s'.substate.accessedStorageKeys = s.substate.accessedStorageKeys
  substate_logSeries : s'.substate.logSeries = s.substate.logSeries
  substate_createdAccounts : s'.substate.createdAccounts = s.substate.createdAccounts

namespace SameButGas

theorem refl (s : State) : SameButGas s s := by
  constructor <;> rfl

theorem trans {s s' s'' : State} (h : SameButGas s s') (h' : SameButGas s' s'') :
    SameButGas s s'' := by
  constructor <;> simp only [h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13,
    h.14, h.15, h.16, h.17, h.18, h.19, h.20, h.21, h'.1, h'.2, h'.3, h'.4, h'.5, h'.6, h'.7, h'.8,
    h'.9, h'.10, h'.11, h'.12, h'.13, h'.14, h'.15, h'.16, h'.17, h'.18, h'.19, h'.20, h'.21]

end SameButGas

@[simp] theorem creditStateGas_accountMap (s : State) (a : ℕ) : (creditStateGas s a).accountMap = s.accountMap := rfl
@[simp] theorem creditStateGas_σ₀ (s : State) (a : ℕ) : (creditStateGas s a).σ₀ = s.σ₀ := rfl
@[simp] theorem creditStateGas_totalGasUsedInBlock (s : State) (a : ℕ) : (creditStateGas s a).totalGasUsedInBlock = s.totalGasUsedInBlock := rfl
@[simp] theorem creditStateGas_transactionReceipts (s : State) (a : ℕ) : (creditStateGas s a).transactionReceipts = s.transactionReceipts := rfl
@[simp] theorem creditStateGas_executionEnv (s : State) (a : ℕ) : (creditStateGas s a).executionEnv = s.executionEnv := rfl
@[simp] theorem creditStateGas_executionGasUsedInBlock (s : State) (a : ℕ) : (creditStateGas s a).executionGasUsedInBlock = s.executionGasUsedInBlock := rfl
@[simp] theorem creditStateGas_stateGasUsedInBlock (s : State) (a : ℕ) : (creditStateGas s a).stateGasUsedInBlock = s.stateGasUsedInBlock := rfl
@[simp] theorem creditStateGas_machineState_pc (s : State) (a : ℕ) : (creditStateGas s a).machineState.pc = s.machineState.pc := rfl
@[simp] theorem creditStateGas_machineState_stack (s : State) (a : ℕ) : (creditStateGas s a).machineState.stack = s.machineState.stack := rfl
@[simp] theorem creditStateGas_machineState_execLength (s : State) (a : ℕ) : (creditStateGas s a).machineState.execLength = s.machineState.execLength := rfl
@[simp] theorem creditStateGas_machineState_activeWords (s : State) (a : ℕ) : (creditStateGas s a).machineState.activeWords = s.machineState.activeWords := rfl
@[simp] theorem creditStateGas_machineState_memory (s : State) (a : ℕ) : (creditStateGas s a).machineState.memory = s.machineState.memory := rfl
@[simp] theorem creditStateGas_machineState_returnData (s : State) (a : ℕ) : (creditStateGas s a).machineState.returnData = s.machineState.returnData := rfl
@[simp] theorem creditStateGas_machineState_H_return (s : State) (a : ℕ) : (creditStateGas s a).machineState.H_return = s.machineState.H_return := rfl
@[simp] theorem creditStateGas_substate_selfDestructSet (s : State) (a : ℕ) : (creditStateGas s a).substate.selfDestructSet = s.substate.selfDestructSet := rfl
@[simp] theorem creditStateGas_substate_touchedAccounts (s : State) (a : ℕ) : (creditStateGas s a).substate.touchedAccounts = s.substate.touchedAccounts := rfl
@[simp] theorem creditStateGas_substate_refundBalance (s : State) (a : ℕ) : (creditStateGas s a).substate.refundBalance = s.substate.refundBalance := rfl
@[simp] theorem creditStateGas_substate_accessedAccounts (s : State) (a : ℕ) : (creditStateGas s a).substate.accessedAccounts = s.substate.accessedAccounts := rfl
@[simp] theorem creditStateGas_substate_accessedStorageKeys (s : State) (a : ℕ) : (creditStateGas s a).substate.accessedStorageKeys = s.substate.accessedStorageKeys := rfl
@[simp] theorem creditStateGas_substate_logSeries (s : State) (a : ℕ) : (creditStateGas s a).substate.logSeries = s.substate.logSeries := rfl
@[simp] theorem creditStateGas_substate_createdAccounts (s : State) (a : ℕ) : (creditStateGas s a).substate.createdAccounts = s.substate.createdAccounts := rfl

theorem creditStateGas_sameButGas (s : State) (a : ℕ) : SameButGas s (creditStateGas s a) := by
  constructor <;> rfl

@[simp] theorem repayStateGasSpill_accountMap (s : State) : (repayStateGasSpill s).accountMap = s.accountMap := rfl
@[simp] theorem repayStateGasSpill_σ₀ (s : State) : (repayStateGasSpill s).σ₀ = s.σ₀ := rfl
@[simp] theorem repayStateGasSpill_totalGasUsedInBlock (s : State) : (repayStateGasSpill s).totalGasUsedInBlock = s.totalGasUsedInBlock := rfl
@[simp] theorem repayStateGasSpill_transactionReceipts (s : State) : (repayStateGasSpill s).transactionReceipts = s.transactionReceipts := rfl
@[simp] theorem repayStateGasSpill_executionEnv (s : State) : (repayStateGasSpill s).executionEnv = s.executionEnv := rfl
@[simp] theorem repayStateGasSpill_executionGasUsedInBlock (s : State) : (repayStateGasSpill s).executionGasUsedInBlock = s.executionGasUsedInBlock := rfl
@[simp] theorem repayStateGasSpill_stateGasUsedInBlock (s : State) : (repayStateGasSpill s).stateGasUsedInBlock = s.stateGasUsedInBlock := rfl
@[simp] theorem repayStateGasSpill_machineState_pc (s : State) : (repayStateGasSpill s).machineState.pc = s.machineState.pc := rfl
@[simp] theorem repayStateGasSpill_machineState_stack (s : State) : (repayStateGasSpill s).machineState.stack = s.machineState.stack := rfl
@[simp] theorem repayStateGasSpill_machineState_execLength (s : State) : (repayStateGasSpill s).machineState.execLength = s.machineState.execLength := rfl
@[simp] theorem repayStateGasSpill_machineState_activeWords (s : State) : (repayStateGasSpill s).machineState.activeWords = s.machineState.activeWords := rfl
@[simp] theorem repayStateGasSpill_machineState_memory (s : State) : (repayStateGasSpill s).machineState.memory = s.machineState.memory := rfl
@[simp] theorem repayStateGasSpill_machineState_returnData (s : State) : (repayStateGasSpill s).machineState.returnData = s.machineState.returnData := rfl
@[simp] theorem repayStateGasSpill_machineState_H_return (s : State) : (repayStateGasSpill s).machineState.H_return = s.machineState.H_return := rfl
@[simp] theorem repayStateGasSpill_substate_selfDestructSet (s : State) : (repayStateGasSpill s).substate.selfDestructSet = s.substate.selfDestructSet := rfl
@[simp] theorem repayStateGasSpill_substate_touchedAccounts (s : State) : (repayStateGasSpill s).substate.touchedAccounts = s.substate.touchedAccounts := rfl
@[simp] theorem repayStateGasSpill_substate_refundBalance (s : State) : (repayStateGasSpill s).substate.refundBalance = s.substate.refundBalance := rfl
@[simp] theorem repayStateGasSpill_substate_accessedAccounts (s : State) : (repayStateGasSpill s).substate.accessedAccounts = s.substate.accessedAccounts := rfl
@[simp] theorem repayStateGasSpill_substate_accessedStorageKeys (s : State) : (repayStateGasSpill s).substate.accessedStorageKeys = s.substate.accessedStorageKeys := rfl
@[simp] theorem repayStateGasSpill_substate_logSeries (s : State) : (repayStateGasSpill s).substate.logSeries = s.substate.logSeries := rfl
@[simp] theorem repayStateGasSpill_substate_createdAccounts (s : State) : (repayStateGasSpill s).substate.createdAccounts = s.substate.createdAccounts := rfl

theorem repayStateGasSpill_sameButGas (s : State) : SameButGas s (repayStateGasSpill s) := by
  constructor <;> rfl

@[simp] theorem settleChildStateGas_accountMap (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).accountMap = s.accountMap := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_σ₀ (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).σ₀ = s.σ₀ := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_totalGasUsedInBlock (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).totalGasUsedInBlock = s.totalGasUsedInBlock := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_transactionReceipts (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).transactionReceipts = s.transactionReceipts := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_executionEnv (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).executionEnv = s.executionEnv := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_executionGasUsedInBlock (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).executionGasUsedInBlock = s.executionGasUsedInBlock := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_stateGasUsedInBlock (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).stateGasUsedInBlock = s.stateGasUsedInBlock := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_machineState_pc (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).machineState.pc = s.machineState.pc := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_machineState_stack (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).machineState.stack = s.machineState.stack := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_machineState_execLength (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).machineState.execLength = s.machineState.execLength := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_machineState_activeWords (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).machineState.activeWords = s.machineState.activeWords := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_machineState_memory (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).machineState.memory = s.machineState.memory := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_machineState_returnData (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).machineState.returnData = s.machineState.returnData := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_machineState_H_return (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).machineState.H_return = s.machineState.H_return := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_substate_selfDestructSet (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_substate_touchedAccounts (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).substate.touchedAccounts = s.substate.touchedAccounts := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_substate_refundBalance (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).substate.refundBalance = s.substate.refundBalance := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_substate_accessedAccounts (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).substate.accessedAccounts = s.substate.accessedAccounts := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_substate_accessedStorageKeys (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).substate.accessedStorageKeys = s.substate.accessedStorageKeys := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_substate_logSeries (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).substate.logSeries = s.substate.logSeries := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl
@[simp] theorem settleChildStateGas_substate_createdAccounts (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).substate.createdAccounts = s.substate.createdAccounts := by
  unfold settleChildStateGas; split <;> (try split) <;> rfl

theorem settleChildStateGas_sameButGas (fork : Fork) (z c : Bool) (s : State) :
    SameButGas s (settleChildStateGas fork z c s) := by
  constructor <;> simp

/-- A state charge changes only the substate's state-gas meter. -/
theorem StateGas.charge_substate {gas gas' amount : ℕ} {A A' : Substate}
    (h : StateGas.charge gas A amount = some (gas', A')) :
    A'.selfDestructSet = A.selfDestructSet ∧ A'.touchedAccounts = A.touchedAccounts ∧
      A'.refundBalance = A.refundBalance ∧ A'.accessedAccounts = A.accessedAccounts ∧
      A'.accessedStorageKeys = A.accessedStorageKeys ∧ A'.logSeries = A.logSeries ∧
      A'.createdAccounts = A.createdAccounts := by
  unfold StateGas.charge at h
  split at h
  · cases h; simp
  · dsimp only at h
    split at h
    · cases h; simp
    · cases h

theorem chargeStateGas_sameButGas {s s' : State} {a : ℕ}
    (h : chargeStateGas s a = .ok s') : SameButGas s s' := by
  unfold chargeStateGas at h
  split at h
  · cases h; exact SameButGas.refl s
  · split at h
    · cases h
    · rename_i hc
      cases h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := StateGas.charge_substate hc
      constructor <;> simp_all

theorem sstoreStateGas_sameButGas {s s' : State}
    (h : sstoreStateGas s = .ok s') : SameButGas s s' := by
  unfold sstoreStateGas at h
  split at h
  · cases h; exact SameButGas.refl s
  · dsimp only at h
    split at h
    · exact chargeStateGas_sameButGas h
    · split at h
      · cases h; exact creditStateGas_sameButGas s _
      · cases h; exact SameButGas.refl s

/-- A call's state charge changes only the substate's state-gas meter. -/
theorem callStateCharge_substate {c : Bool} {gas spill : ℕ} {A A' : Substate}
    (h : callStateCharge c gas A = .ok (spill, A')) :
    A'.selfDestructSet = A.selfDestructSet ∧ A'.touchedAccounts = A.touchedAccounts ∧
      A'.refundBalance = A.refundBalance ∧ A'.accessedAccounts = A.accessedAccounts ∧
      A'.accessedStorageKeys = A.accessedStorageKeys ∧ A'.logSeries = A.logSeries ∧
      A'.createdAccounts = A.createdAccounts := by
  unfold callStateCharge at h
  split at h
  · split at h
    · cases h
    · rename_i hc
      cases h
      exact StateGas.charge_substate hc
  · cases h; simp

/-- Before EIP-8037, a call's state charge charges nothing. -/
theorem callStateCharge_false {gas : ℕ} {A : Substate} :
    callStateCharge false gas A = .ok (0, A) := rfl

end EVM
end Ethereum
