import Ethereum.Theory.OpcodeLemmas

import Mathlib.Tactic

namespace Ethereum

namespace EVM

/--
The largest number of EVM memory words whose Yellow-Paper memory cost can be paid with a
`UInt256` amount of gas.

It is the greatest `w` satisfying `Cₘ w < UInt256.size`, equivalently
`3 * w + w^2 / 512 < 2^256`.
-/
def maxReturnDataWordsByGas : Nat :=
  7699711013376144369441080719284001820899

/--
The corresponding byte bound for return data.  Return data is read from memory, so the byte
length is at most `32` times the number of active memory words that gas can pay for.
-/
def maxReturnDataSizeByGas : Nat :=
  32 * maxReturnDataWordsByGas

lemma maxReturnDataWordsByGas_spec :
    Cₘ (.ofNat maxReturnDataWordsByGas) < UInt256.size ∧
      ¬ Cₘ (.ofNat (maxReturnDataWordsByGas + 1)) < UInt256.size := by
  decide

lemma maxReturnDataSizeByGas_lt_uint256 :
    maxReturnDataSizeByGas < UInt256.size := by
  norm_num [maxReturnDataSizeByGas, maxReturnDataWordsByGas, UInt256.size]

lemma pow_two_64_le_maxReturnDataSizeByGas :
    2 ^ 64 ≤ maxReturnDataSizeByGas := by
  norm_num [maxReturnDataSizeByGas, maxReturnDataWordsByGas]

def memoryPaidByGas (state : State) : Prop :=
  Cₘ state.machineState.activeWords + state.machineState.gasAvailable.toNat < UInt256.size

def memoryExpansionWords (state : State) (instr : Operation) : Nat :=
  match instr with
  | .KECCAK256 =>
      MachineState.M state.machineState.activeWords.toNat
        state.machineState.stack[0]!.toNat state.machineState.stack[1]!.toNat
  | .CALLDATACOPY | .CODECOPY =>
      MachineState.M state.machineState.activeWords.toNat
        state.machineState.stack[0]!.toNat state.machineState.stack[2]!.toNat
  | .MCOPY =>
      MachineState.M state.machineState.activeWords.toNat
        (max state.machineState.stack[0]!.toNat state.machineState.stack[1]!.toNat)
        state.machineState.stack[2]!.toNat
  | .EXTCODECOPY =>
      MachineState.M state.machineState.activeWords.toNat
        state.machineState.stack[1]!.toNat state.machineState.stack[3]!.toNat
  | .RETURNDATACOPY =>
      MachineState.M state.machineState.activeWords.toNat
        state.machineState.stack[0]!.toNat state.machineState.stack[2]!.toNat
  | .MLOAD | .MSTORE =>
      MachineState.M state.machineState.activeWords.toNat state.machineState.stack[0]!.toNat 32
  | .MSTORE8 =>
      MachineState.M state.machineState.activeWords.toNat state.machineState.stack[0]!.toNat 1
  | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 =>
      MachineState.M state.machineState.activeWords.toNat
        state.machineState.stack[0]!.toNat state.machineState.stack[1]!.toNat
  | .CREATE | .CREATE2 =>
      MachineState.M state.machineState.activeWords.toNat
        state.machineState.stack[1]!.toNat state.machineState.stack[2]!.toNat
  | .CALL | .CALLCODE =>
      let m := MachineState.M state.machineState.activeWords.toNat
        state.machineState.stack[3]!.toNat state.machineState.stack[4]!.toNat
      MachineState.M m state.machineState.stack[5]!.toNat state.machineState.stack[6]!.toNat
  | .DELEGATECALL | .STATICCALL =>
      let m := MachineState.M state.machineState.activeWords.toNat
        state.machineState.stack[2]!.toNat state.machineState.stack[3]!.toNat
      MachineState.M m state.machineState.stack[4]!.toNat state.machineState.stack[5]!.toNat
  | .RETURN | .REVERT =>
      MachineState.M state.machineState.activeWords.toNat
        state.machineState.stack[0]!.toNat state.machineState.stack[1]!.toNat
  | _ => state.machineState.activeWords.toNat

lemma Cₘ_monotone_of_lt {a b : Nat} (hab : a ≤ b) (hb : b < UInt256.size) :
    Cₘ (.ofNat a) ≤ Cₘ (.ofNat b) := by
  unfold Cₘ
  rw [UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt hab hb),
    UInt256.toNat_ofNat_of_lt hb]
  unfold GasConstants.Gmemory
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left 3 hab
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul hab hab

lemma maxReturnDataWordsByGas_ge_of_Cₘ_lt {w : Nat}
    (hwlt : w < UInt256.size)
    (hcost : Cₘ (.ofNat w) < UInt256.size) :
    w ≤ maxReturnDataWordsByGas := by
  by_contra hnot
  have hsucc : maxReturnDataWordsByGas + 1 ≤ w :=
    Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
  have hmono :
      Cₘ (.ofNat (maxReturnDataWordsByGas + 1)) ≤ Cₘ (.ofNat w) :=
    Cₘ_monotone_of_lt hsucc hwlt
  exact maxReturnDataWordsByGas_spec.2 (Nat.lt_of_le_of_lt hmono hcost)

lemma MachineState.M_ge_active (s f l : Nat) :
    s ≤ MachineState.M s f l := by
  unfold MachineState.M
  cases l <;> simp

lemma MachineState.M_lt_uint256_size {s f l : Nat}
    (hs : s < UInt256.size) (hf : f < UInt256.size) (hl : l < UInt256.size) :
    MachineState.M s f l < UInt256.size := by
  unfold MachineState.M
  cases l with
  | zero => simpa using hs
  | succ l' =>
      apply max_lt hs
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
      have hsize_pos : 0 < UInt256.size := by simp [UInt256.size]
      have hl' : l' + 1 < UInt256.size := hl
      nlinarith [hf, hl', hsize_pos]

lemma MachineState.M_M_ge_active (s f l f' l' : Nat) :
    s ≤ MachineState.M (MachineState.M s f l) f' l' := by
  exact Nat.le_trans (MachineState.M_ge_active s f l)
    (MachineState.M_ge_active (MachineState.M s f l) f' l')

lemma MachineState.M_M_lt_uint256_size {s f l f' l' : Nat}
    (hs : s < UInt256.size) (hf : f < UInt256.size) (hl : l < UInt256.size)
    (hf' : f' < UInt256.size) (hl' : l' < UInt256.size) :
    MachineState.M (MachineState.M s f l) f' l' < UInt256.size := by
  exact MachineState.M_lt_uint256_size
    (MachineState.M_lt_uint256_size hs hf hl) hf' hl'

lemma Z_memoryExpansionCost_le {validJumps : Array UInt256} {w : Operation}
    {state state' : State} {cost : Nat}
    (h : Z validJumps w state = .ok (state', cost)) :
    memoryExpansionCost state w ≤ state.machineState.gasAvailable.toNat := by
  unfold Z at h
  by_cases hδ : δ w = none
  · rw [if_pos hδ] at h
    contradiction
  rw [if_neg hδ] at h
  by_cases hstack : state.machineState.stack.length < (δ w).getD 0
  · rw [if_pos hstack] at h
    contradiction
  rw [if_neg hstack] at h
  by_cases hcost₁ : state.machineState.gasAvailable.toNat < memoryExpansionCost state w
  · rw [if_pos hcost₁] at h
    contradiction
  exact Nat.le_of_not_gt hcost₁

lemma Z_stack_active_eq {validJumps : Array UInt256} {w : Operation}
    {state stateZ : State} {cost : Nat}
    (h : Z validJumps w state = .ok (stateZ, cost)) :
    stateZ.machineState.stack = state.machineState.stack ∧
      stateZ.machineState.activeWords = state.machineState.activeWords ∧
      stateZ.machineState.memory = state.machineState.memory := by
  unfold Z at h
  by_cases hδ : δ w = none
  · rw [if_pos hδ] at h
    contradiction
  rw [if_neg hδ] at h
  by_cases hstack : state.machineState.stack.length < (δ w).getD 0
  · rw [if_pos hstack] at h
    contradiction
  rw [if_neg hstack] at h
  by_cases hcost₁ : state.machineState.gasAvailable.toNat < memoryExpansionCost state w
  · rw [if_pos hcost₁] at h
    contradiction
  rw [if_neg hcost₁] at h
  by_cases hcost₂ :
      (state.subtractGas (memoryExpansionCost state w)).machineState.gasAvailable.toNat <
        C' (state.subtractGas (memoryExpansionCost state w)) w
  · rw [if_pos (by simpa [State.subtractGas] using hcost₂)] at h
    contradiction
  rw [if_neg (by simpa [State.subtractGas] using hcost₂)] at h
  set state₁ : State := state.subtractGas (memoryExpansionCost state w)
  by_cases hjump :
      w = Operation.JUMP ∧ Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjump)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hjump)] at h
  by_cases hjumpi :
      w = Operation.JUMPI ∧
        state₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
        Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjumpi)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hjumpi)] at h
  by_cases hreturndata :
      w = Operation.RETURNDATACOPY ∧
        (state₁.machineState.stack.getD 1 (⟨0⟩ : UInt256)).toNat +
            (state₁.machineState.stack.getD 2 (⟨0⟩ : UInt256)).toNat >
          state₁.machineState.returnData.size
  · rw [if_pos (by simpa [state₁] using hreturndata)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hreturndata)] at h
  by_cases hoverflow :
      state₁.machineState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024
  · rw [if_pos (by simpa [state₁] using hoverflow)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hoverflow)] at h
  by_cases hstatic :
      ¬state₁.executionEnv.perm ∧
        (w ∈ ([.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2,
            .LOG3, .LOG4, .TSTORE] : List Operation) ∨
          (w = .CALL ∧ ¬state₁.machineState.stack[2]? = some (⟨0⟩ : UInt256)))
  · rw [if_pos (by simpa [state₁] using hstatic)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hstatic)] at h
  by_cases hsstore :
      w = Operation.SSTORE ∧ state₁.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [state₁] using hsstore)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hsstore)] at h
  by_cases hcreate :
      w.isCreate ∧ state₁.machineState.stack[2]?.getD (⟨0⟩ : UInt256) > ⟨49152⟩
  · rw [if_pos (by simpa [state₁] using hcreate)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hcreate)] at h
  injection h with hp
  have hstate : state₁ = stateZ := congrArg Prod.fst hp
  subst stateZ
  simp [state₁, State.subtractGas]

lemma Z_gasAvailable_eq {validJumps : Array UInt256} {w : Operation}
    {state stateZ : State} {cost : Nat}
    (h : Z validJumps w state = .ok (stateZ, cost)) :
    stateZ.machineState.gasAvailable.toNat =
      state.machineState.gasAvailable.toNat - memoryExpansionCost state w := by
  unfold Z at h
  by_cases hδ : δ w = none
  · rw [if_pos hδ] at h
    contradiction
  rw [if_neg hδ] at h
  by_cases hstack : state.machineState.stack.length < (δ w).getD 0
  · rw [if_pos hstack] at h
    contradiction
  rw [if_neg hstack] at h
  by_cases hcost₁ : state.machineState.gasAvailable.toNat < memoryExpansionCost state w
  · rw [if_pos hcost₁] at h
    contradiction
  rw [if_neg hcost₁] at h
  by_cases hcost₂ :
      (state.subtractGas (memoryExpansionCost state w)).machineState.gasAvailable.toNat <
        C' (state.subtractGas (memoryExpansionCost state w)) w
  · rw [if_pos (by simpa [State.subtractGas] using hcost₂)] at h
    contradiction
  rw [if_neg (by simpa [State.subtractGas] using hcost₂)] at h
  set state₁ : State := state.subtractGas (memoryExpansionCost state w)
  by_cases hjump :
      w = Operation.JUMP ∧ Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjump)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hjump)] at h
  by_cases hjumpi :
      w = Operation.JUMPI ∧
        state₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
        Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjumpi)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hjumpi)] at h
  by_cases hreturndata :
      w = Operation.RETURNDATACOPY ∧
        (state₁.machineState.stack.getD 1 (⟨0⟩ : UInt256)).toNat +
            (state₁.machineState.stack.getD 2 (⟨0⟩ : UInt256)).toNat >
          state₁.machineState.returnData.size
  · rw [if_pos (by simpa [state₁] using hreturndata)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hreturndata)] at h
  by_cases hoverflow :
      state₁.machineState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024
  · rw [if_pos (by simpa [state₁] using hoverflow)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hoverflow)] at h
  by_cases hstatic :
      ¬state₁.executionEnv.perm ∧
        (w ∈ ([.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2,
            .LOG3, .LOG4, .TSTORE] : List Operation) ∨
          (w = .CALL ∧ ¬state₁.machineState.stack[2]? = some (⟨0⟩ : UInt256)))
  · rw [if_pos (by simpa [state₁] using hstatic)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hstatic)] at h
  by_cases hsstore :
      w = Operation.SSTORE ∧ state₁.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [state₁] using hsstore)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hsstore)] at h
  by_cases hcreate :
      w.isCreate ∧ state₁.machineState.stack[2]?.getD (⟨0⟩ : UInt256) > ⟨49152⟩
  · rw [if_pos (by simpa [state₁] using hcreate)] at h
    contradiction
  rw [if_neg (by simpa [state₁] using hcreate)] at h
  injection h with hp
  have hstate : state₁ = stateZ := congrArg Prod.fst hp
  subst stateZ
  simp [state₁, State.subtractGas]

private lemma UInt256.ofNat_toNat (u : UInt256) :
    UInt256.ofNat u.toNat = u := by
  cases u with
  | mk v =>
      cases v with
      | mk n hn =>
          apply congrArg UInt256.mk
          apply Fin.ext
          simp [UInt256.toNat, Nat.mod_eq_of_lt hn]

private lemma UInt256.toNat_lt_size (u : UInt256) :
    u.toNat < UInt256.size := u.val.isLt

private lemma UInt256.max_toNat_lt_size (a b : UInt256) :
    max a.toNat b.toNat < UInt256.size := by
  exact Nat.max_lt.2 ⟨UInt256.toNat_lt_size a, UInt256.toNat_lt_size b⟩

lemma memoryExpansionCost_eq (state : State) (w : Operation) :
    memoryExpansionCost state w =
      Cₘ (.ofNat (memoryExpansionWords state w)) - Cₘ state.machineState.activeWords := by
  cases w <;> rename_i op <;> cases op <;>
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', memoryExpansionWords, UInt256.ofNat_toNat]

lemma memoryExpansionWords_ge_active (state : State) (w : Operation) :
    state.machineState.activeWords.toNat ≤ memoryExpansionWords state w := by
  cases w <;> rename_i op <;> cases op <;>
    simp [memoryExpansionWords, MachineState.M_ge_active, MachineState.M_M_ge_active]

lemma memoryExpansionWords_lt_uint256_size (state : State) (w : Operation) :
    memoryExpansionWords state w < UInt256.size := by
  cases w <;> rename_i op <;> cases op <;>
    simp [memoryExpansionWords]
  all_goals
    first
    | exact UInt256.toNat_lt_size _
    | exact (MachineState.M_lt_uint256_size (UInt256.toNat_lt_size _)
        (UInt256.max_toNat_lt_size _ _)
        (UInt256.toNat_lt_size _))
    | exact (MachineState.M_lt_uint256_size (UInt256.toNat_lt_size _)
        (UInt256.toNat_lt_size _) (by decide : 32 < UInt256.size))
    | exact (MachineState.M_lt_uint256_size (UInt256.toNat_lt_size _)
        (UInt256.toNat_lt_size _) (by decide : 1 < UInt256.size))
    | exact (MachineState.M_M_lt_uint256_size (UInt256.toNat_lt_size _)
        (UInt256.toNat_lt_size _) (UInt256.toNat_lt_size _)
        (UInt256.toNat_lt_size _) (UInt256.toNat_lt_size _))
    | exact (MachineState.M_lt_uint256_size (UInt256.toNat_lt_size _)
        (UInt256.toNat_lt_size _) (UInt256.toNat_lt_size _))

lemma memoryPaidByGas_after_Z_target {validJumps : Array UInt256} {w : Operation}
    {state stateZ : State} {cost : Nat}
    (hpaid : memoryPaidByGas state)
    (hZ : Z validJumps w state = .ok (stateZ, cost)) :
    Cₘ (.ofNat (memoryExpansionWords state w)) +
        stateZ.machineState.gasAvailable.toNat < UInt256.size := by
  have hwords_lt := memoryExpansionWords_lt_uint256_size state w
  have hactive_le := memoryExpansionWords_ge_active state w
  have hmono : Cₘ state.machineState.activeWords ≤
      Cₘ (.ofNat (memoryExpansionWords state w)) := by
    rw [← UInt256.ofNat_toNat state.machineState.activeWords]
    exact Cₘ_monotone_of_lt hactive_le hwords_lt
  have hmem := Z_memoryExpansionCost_le hZ
  have hgas := Z_gasAvailable_eq hZ
  rw [memoryExpansionCost_eq] at hmem hgas
  rw [hgas]
  have hle :
      Cₘ (.ofNat (memoryExpansionWords state w)) +
          (state.machineState.gasAvailable.toNat -
            (Cₘ (.ofNat (memoryExpansionWords state w)) -
              Cₘ state.machineState.activeWords)) ≤
        Cₘ state.machineState.activeWords + state.machineState.gasAvailable.toNat := by
    omega
  exact Nat.lt_of_le_of_lt hle hpaid

private lemma UInt256.toNat_ofNat_M (a b c : UInt256) :
    (UInt256.ofNat (MachineState.M a.toNat b.toNat c.toNat)).toNat =
      MachineState.M a.toNat b.toNat c.toNat := by
  rw [UInt256.toNat_ofNat_of_lt]
  exact MachineState.M_lt_uint256_size a.val.isLt b.val.isLt c.val.isLt

private lemma UInt256.toNat_ofNat_M_M (a b c d e : UInt256) :
    (UInt256.ofNat
      (MachineState.M (MachineState.M a.toNat b.toNat c.toNat) d.toNat e.toNat)).toNat =
      MachineState.M (MachineState.M a.toNat b.toNat c.toNat) d.toNat e.toNat := by
  rw [UInt256.toNat_ofNat_of_lt]
  exact MachineState.M_M_lt_uint256_size a.val.isLt b.val.isLt c.val.isLt d.val.isLt e.val.isLt

private lemma UInt256.toNat_ofNat_M_nat (a b : UInt256) {c : Nat} (hc : c < UInt256.size) :
    (UInt256.ofNat (MachineState.M a.toNat b.toNat c)).toNat =
      MachineState.M a.toNat b.toNat c := by
  rw [UInt256.toNat_ofNat_of_lt]
  exact MachineState.M_lt_uint256_size a.val.isLt b.val.isLt hc

private lemma MachineState.M_idem (s f l : Nat) :
    MachineState.M (MachineState.M s f l) f l = MachineState.M s f l := by
  unfold MachineState.M
  cases l <;> simp

set_option linter.unusedSimpArgs false in
lemma call_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {state : State} {x : UInt256} {state' : State}
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission state = .ok (x, state')) :
    state'.machineState.activeWords.toNat ≤
      MachineState.M
        (MachineState.M state.machineState.activeWords.toNat inOffset.toNat inSize.toNat)
        outOffset.toNat outSize.toNat := by
  rw [call.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure, writeBytes] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [UInt256.toNat_ofNat_M, UInt256.toNat_ofNat_M_M]

private lemma Stack.pop7_get!3456_active {s stack : Stack UInt256}
    {x0 x1 x2 x3 x4 x5 x6 : UInt256}
    (h : s.pop7 = some (stack, x0, x1, x2, x3, x4, x5, x6)) :
    s[3]! = x3 ∧ s[4]! = x4 ∧ s[5]! = x5 ∧ s[6]! = x6 := by
  cases s with
  | nil => simp [Stack.pop7] at h
  | cons y0 ys0 =>
      cases ys0 with
      | nil => simp [Stack.pop7] at h
      | cons y1 ys1 =>
          cases ys1 with
          | nil => simp [Stack.pop7] at h
          | cons y2 ys2 =>
              cases ys2 with
              | nil => simp [Stack.pop7] at h
              | cons y3 ys3 =>
                  cases ys3 with
                  | nil => simp [Stack.pop7] at h
                  | cons y4 ys4 =>
                      cases ys4 with
                      | nil => simp [Stack.pop7] at h
                      | cons y5 ys5 =>
                          cases ys5 with
                          | nil => simp [Stack.pop7] at h
                          | cons y6 ys6 =>
                              simp [Stack.pop7] at h
                              rcases h with ⟨_, _, _, _, h3, h4, h5, h6⟩
                              exact ⟨h3, h4, h5, h6⟩

private lemma Stack.pop6_get!2345_active {s stack : Stack UInt256}
    {x0 x1 x2 x3 x4 x5 : UInt256}
    (h : s.pop6 = some (stack, x0, x1, x2, x3, x4, x5)) :
    s[2]! = x2 ∧ s[3]! = x3 ∧ s[4]! = x4 ∧ s[5]! = x5 := by
  cases s with
  | nil => simp [Stack.pop6] at h
  | cons y0 ys0 =>
      cases ys0 with
      | nil => simp [Stack.pop6] at h
      | cons y1 ys1 =>
          cases ys1 with
          | nil => simp [Stack.pop6] at h
          | cons y2 ys2 =>
              cases ys2 with
              | nil => simp [Stack.pop6] at h
              | cons y3 ys3 =>
                  cases ys3 with
                  | nil => simp [Stack.pop6] at h
                  | cons y4 ys4 =>
                      cases ys4 with
                      | nil => simp [Stack.pop6] at h
                      | cons y5 ys5 =>
                          simp [Stack.pop6] at h
                          rcases h with ⟨_, _, _, h2, h3, h4, h5⟩
                          exact ⟨h2, h3, h4, h5⟩

private lemma Stack.pop2_get!01 {s stack : Stack UInt256} {a b : UInt256}
    (h : s.pop2 = some (stack, a, b)) :
    s[0]! = a ∧ s[1]! = b := by
  cases s with
  | nil => simp [Stack.pop2] at h
  | cons x xs =>
      cases xs with
      | nil => simp [Stack.pop2] at h
      | cons y ys =>
          simp [Stack.pop2] at h
          rcases h with ⟨_, rfl, rfl⟩
          simp

private lemma Stack.pop_get!0 {s stack : Stack UInt256} {a : UInt256}
    (h : s.pop = some (stack, a)) :
    s[0]! = a := by
  cases s with
  | nil => simp [Stack.pop] at h
  | cons x xs =>
      simp [Stack.pop] at h
      rcases h with ⟨_, rfl⟩
      simp

private lemma Stack.pop3_get!012 {s stack : Stack UInt256} {a b c : UInt256}
    (h : s.pop3 = some (stack, a, b, c)) :
    s[0]! = a ∧ s[1]! = b ∧ s[2]! = c := by
  cases s with
  | nil => simp [Stack.pop3] at h
  | cons x xs =>
      cases xs with
      | nil => simp [Stack.pop3] at h
      | cons y ys =>
          cases ys with
          | nil => simp [Stack.pop3] at h
          | cons z zs =>
              simp [Stack.pop3] at h
              rcases h with ⟨_, rfl, rfl, rfl⟩
              simp

private lemma Stack.pop4_get!013 {s stack : Stack UInt256} {a b c d : UInt256}
    (h : s.pop4 = some (stack, a, b, c, d)) :
    s[0]! = a ∧ s[1]! = b ∧ s[3]! = d := by
  cases s with
  | nil => simp [Stack.pop4] at h
  | cons x xs =>
      cases xs with
      | nil => simp [Stack.pop4] at h
      | cons y ys =>
          cases ys with
          | nil => simp [Stack.pop4] at h
          | cons z zs =>
              cases zs with
              | nil => simp [Stack.pop4] at h
              | cons q qs =>
                  simp [Stack.pop4] at h
                  rcases h with ⟨_, rfl, rfl, _, rfl⟩
                  simp

private lemma Stack.pop5_get!01 {s stack : Stack UInt256} {a b c d e : UInt256}
    (h : s.pop5 = some (stack, a, b, c, d, e)) :
    s[0]! = a ∧ s[1]! = b := by
  cases s with
  | nil => simp [Stack.pop5] at h
  | cons x xs =>
      cases xs with
      | nil => simp [Stack.pop5] at h
      | cons y ys =>
          cases ys with
          | nil => simp [Stack.pop5] at h
          | cons z zs =>
              cases zs with
              | nil => simp [Stack.pop5] at h
              | cons q qs =>
                  cases qs with
                  | nil => simp [Stack.pop5] at h
                  | cons r rs =>
                      simp [Stack.pop5] at h
                      rcases h with ⟨_, rfl, rfl, _, _, _⟩
                      simp

private lemma Stack.pop6_get!01_active {s stack : Stack UInt256} {a b c d e f : UInt256}
    (h : s.pop6 = some (stack, a, b, c, d, e, f)) :
    s[0]! = a ∧ s[1]! = b := by
  cases s with
  | nil => simp [Stack.pop6] at h
  | cons x xs =>
      cases xs with
      | nil => simp [Stack.pop6] at h
      | cons y ys =>
          cases ys with
          | nil => simp [Stack.pop6] at h
          | cons z zs =>
              cases zs with
              | nil => simp [Stack.pop6] at h
              | cons q qs =>
                  cases qs with
                  | nil => simp [Stack.pop6] at h
                  | cons r rs =>
                      cases rs with
                      | nil => simp [Stack.pop6] at h
                      | cons t ts =>
                          simp [Stack.pop6] at h
                          rcases h with ⟨_, rfl, rfl, _, _, _, _⟩
                          simp

private lemma step_log_activeWords_norm (state : State) (offset len : UInt256) :
    (UInt256.ofNat
      (MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat)).toNat =
      MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat := by
  rw [UInt256.toNat_ofNat_of_lt]
  exact MachineState.M_lt_uint256_size state.machineState.activeWords.val.isLt
    offset.val.isLt len.val.isLt

set_option linter.unusedSimpArgs false in
lemma step_call_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.CALL, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.CALL := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    rename_i _ popped hLift _ callResult hCall
    have hpop := option_liftM_eq_some hLift
    have hcallActive := call_activeWords_le_memoryExpansionWords hCall
    rw [← h]
    have hidx := Stack.pop7_get!3456_active hpop
    simpa [memoryExpansionWords, hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2] using hcallActive

set_option linter.unusedSimpArgs false in
lemma step_callcode_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.CALLCODE, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.CALLCODE := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    rename_i _ popped hLift _ callResult hCall
    have hpop := option_liftM_eq_some hLift
    have hcallActive := call_activeWords_le_memoryExpansionWords hCall
    rw [← h]
    have hidx := Stack.pop7_get!3456_active hpop
    simpa [memoryExpansionWords, hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2] using hcallActive

set_option linter.unusedSimpArgs false in
lemma step_delegatecall_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.DELEGATECALL, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.DELEGATECALL := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    rename_i _ popped hLift _ callResult hCall
    have hpop := option_liftM_eq_some hLift
    have hcallActive := call_activeWords_le_memoryExpansionWords hCall
    rw [← h]
    have hidx := Stack.pop6_get!2345_active hpop
    simpa [memoryExpansionWords, hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2] using hcallActive

set_option linter.unusedSimpArgs false in
lemma step_staticcall_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.STATICCALL, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.STATICCALL := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    rename_i _ popped hLift _ callResult hCall
    have hpop := option_liftM_eq_some hLift
    have hcallActive := call_activeWords_le_memoryExpansionWords hCall
    rw [← h]
    have hidx := Stack.pop6_get!2345_active hpop
    simpa [memoryExpansionWords, hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2] using hcallActive

set_option linter.unusedSimpArgs false in
lemma step_create_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.CREATE, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.CREATE := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    rw [← h]
    cases hs : state.machineState.stack with
    | nil => simp_all [memoryExpansionWords, UInt256.toNat_ofNat_M, Stack.pop3]
    | cons x xs =>
        cases xs with
        | nil => simp_all [memoryExpansionWords, UInt256.toNat_ofNat_M, Stack.pop3]
        | cons y ys =>
            cases ys with
            | nil => simp_all [memoryExpansionWords, UInt256.toNat_ofNat_M, Stack.pop3]
            | cons z zs => simp_all [memoryExpansionWords, UInt256.toNat_ofNat_M, Stack.pop3]

set_option linter.unusedSimpArgs false in
lemma step_create2_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.CREATE2, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.CREATE2 := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    rw [← h]
    cases hs : state.machineState.stack with
    | nil => simp_all [memoryExpansionWords, UInt256.toNat_ofNat_M, Stack.pop4]
    | cons x xs =>
        cases xs with
        | nil => simp_all [memoryExpansionWords, UInt256.toNat_ofNat_M, Stack.pop4]
        | cons y ys =>
            cases ys with
            | nil => simp_all [memoryExpansionWords, UInt256.toNat_ofNat_M, Stack.pop4]
            | cons z zs =>
                cases zs with
                | nil => simp_all [memoryExpansionWords, UInt256.toNat_ofNat_M, Stack.pop4]
                | cons w ws => simp_all [memoryExpansionWords, UInt256.toNat_ofNat_M, Stack.pop4]

lemma step_return_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.RETURN, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.RETURN := by
  unfold step at h
  simp [binaryMachineStateOp] at h
  cases hpop : state.machineState.stack.pop2 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, len⟩
      simp [hpop, MachineState.evmReturn, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop2_get!01 hpop
      simp [memoryExpansionWords, hidx.1, hidx.2, UInt256.toNat_ofNat_M]

lemma step_revert_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.REVERT, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.REVERT := by
  unfold step at h
  simp [binaryMachineStateOp] at h
  cases hpop : state.machineState.stack.pop2 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, len⟩
      simp [hpop, MachineState.evmRevert, MachineState.evmReturn,
        Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop2_get!01 hpop
      simp [memoryExpansionWords, hidx.1, hidx.2, UInt256.toNat_ofNat_M, MachineState.M_idem]

set_option linter.unusedSimpArgs false in
lemma step_mload_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.MLOAD, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.MLOAD := by
  unfold step at h
  simp [MachineState.mload, MachineState.lookupMemory, Ethereum.State.replaceStackAndIncrPC,
    Ethereum.State.incrPC] at h
  cases hpop : state.machineState.stack.pop with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset⟩
      simp [hpop, MachineState.mload, MachineState.lookupMemory, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop_get!0 hpop
      simp [memoryExpansionWords, hidx, UInt256.toNat_ofNat_M_nat,
        (by decide : 32 < UInt256.size)]

set_option linter.unusedSimpArgs false in
lemma step_mstore_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.MSTORE, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.MSTORE := by
  unfold step at h
  simp [binaryMachineStateOp] at h
  cases hpop : state.machineState.stack.pop2 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, val⟩
      simp [hpop, MachineState.mstore, MachineState.writeWord, writeBytes,
        Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := (Stack.pop2_get!01 hpop).1
      simp [memoryExpansionWords, hidx, UInt256.toNat_ofNat_M_nat,
        (by decide : 32 < UInt256.size)]

set_option linter.unusedSimpArgs false in
lemma step_mstore8_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.MSTORE8, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.MSTORE8 := by
  unfold step at h
  simp [binaryMachineStateOp] at h
  cases hpop : state.machineState.stack.pop2 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, val⟩
      simp [hpop, MachineState.mstore8, writeBytes, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := (Stack.pop2_get!01 hpop).1
      simp [memoryExpansionWords, hidx, UInt256.toNat_ofNat_M_nat,
        (by decide : 1 < UInt256.size)]

set_option linter.unusedSimpArgs false in
lemma step_keccak_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.KECCAK256, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.KECCAK256 := by
  unfold step at h
  simp [binaryMachineStateOp'] at h
  cases hpop : state.machineState.stack.pop2 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, len⟩
      simp [hpop, MachineState.keccak256, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop2_get!01 hpop
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat)).toNat ≤
        memoryExpansionWords state Operation.KECCAK256
      have hnorm :
          (UInt256.ofNat
            (MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat)).toNat =
            MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat := by
        rw [UInt256.toNat_ofNat_of_lt]
        exact MachineState.M_lt_uint256_size state.machineState.activeWords.val.isLt
          offset.val.isLt len.val.isLt
      rw [hnorm]
      simp [memoryExpansionWords, hidx.1, hidx.2]

set_option linter.unusedSimpArgs false in
lemma step_calldatacopy_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.CALLDATACOPY, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.CALLDATACOPY := by
  unfold step at h
  simp [ternaryCopyOp] at h
  cases hpop : state.machineState.stack.pop3 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, mstart, datastart, size⟩
      simp [hpop, calldatacopy, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop3_get!012 hpop
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat)).toNat ≤
        memoryExpansionWords state Operation.CALLDATACOPY
      have hnorm :
          (UInt256.ofNat
            (MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat)).toNat =
            MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat := by
        rw [UInt256.toNat_ofNat_of_lt]
        exact MachineState.M_lt_uint256_size state.machineState.activeWords.val.isLt
          mstart.val.isLt size.val.isLt
      rw [hnorm]
      simp [memoryExpansionWords, hidx.1, hidx.2.2]

set_option linter.unusedSimpArgs false in
lemma step_codecopy_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.CODECOPY, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.CODECOPY := by
  unfold step at h
  simp [ternaryCopyOp] at h
  cases hpop : state.machineState.stack.pop3 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, mstart, cstart, size⟩
      simp [hpop, codeCopy, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop3_get!012 hpop
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat)).toNat ≤
        memoryExpansionWords state Operation.CODECOPY
      have hnorm :
          (UInt256.ofNat
            (MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat)).toNat =
            MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat := by
        rw [UInt256.toNat_ofNat_of_lt]
        exact MachineState.M_lt_uint256_size state.machineState.activeWords.val.isLt
          mstart.val.isLt size.val.isLt
      rw [hnorm]
      simp [memoryExpansionWords, hidx.1, hidx.2.2]

set_option linter.unusedSimpArgs false in
lemma step_returndatacopy_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.RETURNDATACOPY, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.RETURNDATACOPY := by
  unfold step at h
  cases hpop : state.machineState.stack.pop3 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, mstart, rstart, size⟩
      simp [hpop, MachineState.returndatacopy, writeBytes, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      rw [← h]
      have hidx := Stack.pop3_get!012 hpop
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat)).toNat ≤
        memoryExpansionWords state Operation.RETURNDATACOPY
      have hnorm :
          (UInt256.ofNat
            (MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat)).toNat =
            MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat := by
        rw [UInt256.toNat_ofNat_of_lt]
        exact MachineState.M_lt_uint256_size state.machineState.activeWords.val.isLt
          mstart.val.isLt size.val.isLt
      rw [hnorm]
      simp [memoryExpansionWords, hidx.1, hidx.2.2]

set_option linter.unusedSimpArgs false in
lemma step_extcodecopy_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.EXTCODECOPY, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.EXTCODECOPY := by
  unfold step at h
  simp [quaternaryCopyOp] at h
  cases hpop : state.machineState.stack.pop4 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, acc, mstart, cstart, size⟩
      simp [hpop, extCodeCopy', Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop4_get!013 hpop
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat)).toNat ≤
        memoryExpansionWords state Operation.EXTCODECOPY
      have hnorm :
          (UInt256.ofNat
            (MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat)).toNat =
            MachineState.M state.machineState.activeWords.toNat mstart.toNat size.toNat := by
        rw [UInt256.toNat_ofNat_of_lt]
        exact MachineState.M_lt_uint256_size state.machineState.activeWords.val.isLt
          mstart.val.isLt size.val.isLt
      rw [hnorm]
      simp [memoryExpansionWords, hidx.2.1, hidx.2.2]

set_option linter.unusedSimpArgs false in
lemma step_mcopy_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.MCOPY, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.MCOPY := by
  unfold step at h
  simp [ternaryMachineStateOp] at h
  cases hpop : state.machineState.stack.pop3 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, writeStart, readStart, size⟩
      simp [hpop, MachineState.mcopy, writeBytes, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop3_get!012 hpop
      have hmax : max writeStart.toNat readStart.toNat < UInt256.size :=
        max_lt writeStart.val.isLt readStart.val.isLt
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat
            (max writeStart.toNat readStart.toNat) size.toNat)).toNat ≤
        memoryExpansionWords state Operation.MCOPY
      have hnorm :
          (UInt256.ofNat
            (MachineState.M state.machineState.activeWords.toNat
              (max writeStart.toNat readStart.toNat) size.toNat)).toNat =
            MachineState.M state.machineState.activeWords.toNat
              (max writeStart.toNat readStart.toNat) size.toNat := by
        rw [UInt256.toNat_ofNat_of_lt]
        exact MachineState.M_lt_uint256_size state.machineState.activeWords.val.isLt hmax
          size.val.isLt
      rw [hnorm]
      simp [memoryExpansionWords, hidx.1, hidx.2.1, hidx.2.2]

set_option linter.unusedSimpArgs false in
lemma step_log0_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.LOG0, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.LOG0 := by
  unfold step at h
  simp [log0Op] at h
  cases hpop : state.machineState.stack.pop2 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, len⟩
      simp [hpop, evmLogOp, logOp, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop2_get!01 hpop
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat)).toNat ≤
        memoryExpansionWords state Operation.LOG0
      rw [step_log_activeWords_norm]
      simp [memoryExpansionWords, hidx.1, hidx.2]

set_option linter.unusedSimpArgs false in
lemma step_log1_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.LOG1, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.LOG1 := by
  unfold step at h
  simp [log1Op] at h
  cases hpop : state.machineState.stack.pop3 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, len, t0⟩
      simp [hpop, evmLogOp, logOp, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop3_get!012 hpop
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat)).toNat ≤
        memoryExpansionWords state Operation.LOG1
      rw [step_log_activeWords_norm]
      simp [memoryExpansionWords, hidx.1, hidx.2.1]

set_option linter.unusedSimpArgs false in
lemma step_log2_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.LOG2, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.LOG2 := by
  unfold step at h
  simp [log2Op] at h
  cases hpop : state.machineState.stack.pop4 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, len, t0, t1⟩
      simp [hpop, evmLogOp, logOp, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop4_get!013 hpop
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat)).toNat ≤
        memoryExpansionWords state Operation.LOG2
      rw [step_log_activeWords_norm]
      simp [memoryExpansionWords, hidx.1, hidx.2.1]

set_option linter.unusedSimpArgs false in
lemma step_log3_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.LOG3, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.LOG3 := by
  unfold step at h
  simp [log3Op] at h
  cases hpop : state.machineState.stack.pop5 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, len, t0, t1, t2⟩
      simp [hpop, evmLogOp, logOp, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop5_get!01 hpop
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat)).toNat ≤
        memoryExpansionWords state Operation.LOG3
      rw [step_log_activeWords_norm]
      simp [memoryExpansionWords, hidx.1, hidx.2]

set_option linter.unusedSimpArgs false in
lemma step_log4_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.LOG4, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.LOG4 := by
  unfold step at h
  simp [log4Op] at h
  cases hpop : state.machineState.stack.pop6 with
  | none => simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, len, t0, t1, t2, t3⟩
      simp [hpop, evmLogOp, logOp, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      have hidx := Stack.pop6_get!01_active hpop
      change (UInt256.ofNat
          (MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat)).toNat ≤
        memoryExpansionWords state Operation.LOG4
      rw [step_log_activeWords_norm]
      simp [memoryExpansionWords, hidx.1, hidx.2]

private lemma State.sstore_activeWords (state : State) (spos sval : UInt256) :
    (state.sstore spos sval).machineState.activeWords = state.machineState.activeWords := by
  unfold State.sstore
  cases hlookup : state.lookupAccount state.executionEnv.codeOwner <;>
    simp [hlookup, Option.option, State.setAccount, State.addAccessedStorageKey]

private lemma State.tstore_activeWords (state : State) (spos sval : UInt256) :
    (state.tstore spos sval).machineState.activeWords = state.machineState.activeWords := by
  unfold State.tstore
  cases hlookup : state.lookupAccount state.executionEnv.codeOwner <;>
    simp [hlookup, Option.option, State.updateAccount]

set_option linter.unusedSimpArgs false in
lemma step_stoparith_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.SAOp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.StopArith op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.StopArith op) := by
  cases op <;>
    unfold step at h <;>
    simp [memoryExpansionWords, execBinOp, execTriOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC, MachineState.setReturnData] at h
  all_goals
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try cases h
      try simp [memoryExpansionWords]

set_option linter.unusedSimpArgs false in
lemma step_compbit_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.CBLOp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.CompBit op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.CompBit op) := by
  cases op <;>
    unfold step at h <;>
    simp [memoryExpansionWords, execUnOp, execBinOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
  all_goals
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try cases h
      try simp [memoryExpansionWords]

set_option linter.unusedSimpArgs false in
lemma step_env_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.EOp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.Env op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.Env op) := by
  cases op
  · unfold step at h
    simp [memoryExpansionWords, executionEnvOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    injection h with hstate
    subst state'
    simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, unaryStateOp, Ethereum.State.balance, Ethereum.State.addAccessedAccount,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, executionEnvOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    injection h with hstate
    subst state'
    simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, executionEnvOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    injection h with hstate
    subst state'
    simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, executionEnvOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    injection h with hstate
    subst state'
    simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, unaryStateOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, executionEnvOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    injection h with hstate
    subst state'
    simp [memoryExpansionWords]
  · exact step_calldatacopy_activeWords_le_memoryExpansionWords h
  · unfold step at h
    simp [memoryExpansionWords, executionEnvOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    injection h with hstate
    subst state'
    simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, executionEnvOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    injection h with hstate
    subst state'
    simp [memoryExpansionWords]
  · exact step_codecopy_activeWords_le_memoryExpansionWords h
  · unfold step at h
    simp [memoryExpansionWords, unaryStateOp, Ethereum.State.extCodeSize,
      Ethereum.State.addAccessedAccount, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try simp [memoryExpansionWords]
  · exact step_extcodecopy_activeWords_le_memoryExpansionWords h
  · unfold step at h
    simp [memoryExpansionWords, machineStateOp, MachineState.returndatasize,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    injection h with hstate
    subst state'
    simp [memoryExpansionWords]
  · exact step_returndatacopy_activeWords_le_memoryExpansionWords h
  · unfold step at h
    simp [memoryExpansionWords, unaryStateOp, Ethereum.State.extCodeHash,
      Ethereum.State.addAccessedAccount, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try simp [memoryExpansionWords]

set_option linter.unusedSimpArgs false in
lemma step_block_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.BOp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.Block op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.Block op) := by
  cases op <;>
    unfold step at h <;>
    simp [memoryExpansionWords, stateOp, executionEnvOp, unaryExecutionEnvOp, unaryStateOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try cases h
      try simp [memoryExpansionWords]

set_option linter.unusedSimpArgs false in
lemma step_stackmemflow_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.SMSFOp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.StackMemFlow op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.StackMemFlow op) := by
  cases op
  · unfold step at h
    simp [memoryExpansionWords, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try simp [memoryExpansionWords]
  · exact step_mload_activeWords_le_memoryExpansionWords h
  · exact step_mstore_activeWords_le_memoryExpansionWords h
  · unfold step at h
    simp [memoryExpansionWords, unaryStateOp, Ethereum.State.sload,
      Ethereum.State.addAccessedStorageKey, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, binaryStateOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try cases h
      try simp [memoryExpansionWords, State.sstore_activeWords]
  · exact step_mstore8_activeWords_le_memoryExpansionWords h
  · unfold step at h
    simp [memoryExpansionWords] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, machineStateOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    rw [← h]
    simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, machineStateOp, MachineState.msize,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    injection h with hstate
    subst state'
    simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, machineStateOp, MachineState.gas,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    injection h with hstate
    subst state'
    simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    rw [← h]
    simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, unaryStateOp, Ethereum.State.tload,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try simp [memoryExpansionWords]
  · unfold step at h
    simp [memoryExpansionWords, binaryStateOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try cases h
      try simp [memoryExpansionWords, State.tstore_activeWords]
  · exact step_mcopy_activeWords_le_memoryExpansionWords h

set_option linter.unusedSimpArgs false in
lemma step_push_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.POp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.Push op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.Push op) := by
  cases op <;>
    unfold step at h <;>
    simp [memoryExpansionWords, bind, Except.bind, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
  all_goals
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try cases h
      try simp [memoryExpansionWords]

set_option linter.unusedSimpArgs false in
lemma step_dup_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.DOp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.Dup op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.Dup op) := by
  cases op <;>
    unfold step at h <;>
    simp [memoryExpansionWords, dup, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
  all_goals
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try cases h
      try simp [memoryExpansionWords]

set_option linter.unusedSimpArgs false in
lemma step_exchange_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.ExOp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.Exchange op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.Exchange op) := by
  cases op <;>
    unfold step at h <;>
    simp [memoryExpansionWords, swap, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
  all_goals
    repeat' (split at h <;> try simp at h)
    all_goals
      try contradiction
      try injection h with hstate
      try subst state'
      try cases h
      try simp [memoryExpansionWords]

lemma step_keccak_group_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.KOp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.Keccak op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.Keccak op) := by
  cases op
  exact step_keccak_activeWords_le_memoryExpansionWords h

lemma step_log_group_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.LOp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.Log op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.Log op) := by
  cases op
  · exact step_log0_activeWords_le_memoryExpansionWords h
  · exact step_log1_activeWords_le_memoryExpansionWords h
  · exact step_log2_activeWords_le_memoryExpansionWords h
  · exact step_log3_activeWords_le_memoryExpansionWords h
  · exact step_log4_activeWords_le_memoryExpansionWords h

set_option linter.unusedSimpArgs false in
lemma step_selfdestruct_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.SELFDESTRUCT, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state Operation.SELFDESTRUCT := by
  unfold step at h
  simp [memoryExpansionWords, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    try injection h with hstate
    try subst state'
    try cases h
    try simp [memoryExpansionWords]

lemma step_system_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {op : Operation.SOp} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (Operation.System op, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state (Operation.System op) := by
  cases op
  · exact step_create_activeWords_le_memoryExpansionWords h
  · exact step_call_activeWords_le_memoryExpansionWords h
  · exact step_callcode_activeWords_le_memoryExpansionWords h
  · exact step_return_activeWords_le_memoryExpansionWords h
  · exact step_delegatecall_activeWords_le_memoryExpansionWords h
  · exact step_create2_activeWords_le_memoryExpansionWords h
  · exact step_staticcall_activeWords_le_memoryExpansionWords h
  · exact step_revert_activeWords_le_memoryExpansionWords h
  · unfold step at h
    simp at h
  · exact step_selfdestruct_activeWords_le_memoryExpansionWords h

lemma step_activeWords_le_memoryExpansionWords {gasCost : Nat}
    {w : Operation} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step gasCost (w, arg) state = .ok state') :
    state'.machineState.activeWords.toNat ≤ memoryExpansionWords state w := by
  cases w with
  | StopArith op => exact step_stoparith_activeWords_le_memoryExpansionWords h
  | CompBit op => exact step_compbit_activeWords_le_memoryExpansionWords h
  | Keccak op => exact step_keccak_group_activeWords_le_memoryExpansionWords h
  | Env op => exact step_env_activeWords_le_memoryExpansionWords h
  | Block op => exact step_block_activeWords_le_memoryExpansionWords h
  | StackMemFlow op => exact step_stackmemflow_activeWords_le_memoryExpansionWords h
  | Push op => exact step_push_activeWords_le_memoryExpansionWords h
  | Dup op => exact step_dup_activeWords_le_memoryExpansionWords h
  | Exchange op => exact step_exchange_activeWords_le_memoryExpansionWords h
  | Log op => exact step_log_group_activeWords_le_memoryExpansionWords h
  | System op => exact step_system_activeWords_le_memoryExpansionWords h

private lemma Stack.pop2_getD0 {s stack : Stack UInt256} {a b : UInt256}
    (h : s.pop2 = some (stack, a, b)) :
    (s[0]?.getD default).toNat = a.toNat := by
  cases s with
  | nil => simp [Stack.pop2] at h
  | cons x xs =>
      cases xs with
      | nil => simp [Stack.pop2] at h
      | cons y ys =>
          simp [Stack.pop2] at h
          rcases h with ⟨_, rfl, _⟩
          simp

private lemma Stack.pop2_getD1 {s stack : Stack UInt256} {a b : UInt256}
    (h : s.pop2 = some (stack, a, b)) :
    (s[1]?.getD default).toNat = b.toNat := by
  cases s with
  | nil => simp [Stack.pop2] at h
  | cons x xs =>
      cases xs with
      | nil => simp [Stack.pop2] at h
      | cons y ys =>
          simp [Stack.pop2] at h
          rcases h with ⟨_, _, rfl⟩
          simp

private lemma Stack.pop7_get!3456 {s stack : Stack UInt256}
    {x0 x1 x2 x3 x4 x5 x6 : UInt256}
    (h : s.pop7 = some (stack, x0, x1, x2, x3, x4, x5, x6)) :
    s[3]! = x3 ∧ s[4]! = x4 ∧ s[5]! = x5 ∧ s[6]! = x6 := by
  cases s with
  | nil => simp [Stack.pop7] at h
  | cons y0 ys0 =>
      cases ys0 with
      | nil => simp [Stack.pop7] at h
      | cons y1 ys1 =>
          cases ys1 with
          | nil => simp [Stack.pop7] at h
          | cons y2 ys2 =>
              cases ys2 with
              | nil => simp [Stack.pop7] at h
              | cons y3 ys3 =>
                  cases ys3 with
                  | nil => simp [Stack.pop7] at h
                  | cons y4 ys4 =>
                      cases ys4 with
                      | nil => simp [Stack.pop7] at h
                      | cons y5 ys5 =>
                          cases ys5 with
                          | nil => simp [Stack.pop7] at h
                          | cons y6 ys6 =>
                              simp [Stack.pop7] at h
                              rcases h with ⟨_, _, _, _, h3, h4, h5, h6⟩
                              exact ⟨h3, h4, h5, h6⟩

private lemma Stack.pop6_get!2345 {s stack : Stack UInt256}
    {x0 x1 x2 x3 x4 x5 : UInt256}
    (h : s.pop6 = some (stack, x0, x1, x2, x3, x4, x5)) :
    s[2]! = x2 ∧ s[3]! = x3 ∧ s[4]! = x4 ∧ s[5]! = x5 := by
  cases s with
  | nil => simp [Stack.pop6] at h
  | cons y0 ys0 =>
      cases ys0 with
      | nil => simp [Stack.pop6] at h
      | cons y1 ys1 =>
          cases ys1 with
          | nil => simp [Stack.pop6] at h
          | cons y2 ys2 =>
              cases ys2 with
              | nil => simp [Stack.pop6] at h
              | cons y3 ys3 =>
                  cases ys3 with
                  | nil => simp [Stack.pop6] at h
                  | cons y4 ys4 =>
                      cases ys4 with
                      | nil => simp [Stack.pop6] at h
                      | cons y5 ys5 =>
                          simp [Stack.pop6] at h
                          rcases h with ⟨_, _, _, h2, h3, h4, h5⟩
                          exact ⟨h2, h3, h4, h5⟩

lemma return_words_le_maxReturnDataWordsByGas_of_Z
    {validJumps : Array UInt256} {state stateZ : State} {cost : Nat}
    {stack : Stack UInt256} {offset len : UInt256}
    (hpaid : memoryPaidByGas state)
    (hpop : state.machineState.stack.pop2 = some (stack, offset, len))
    (hZ : Z validJumps Operation.RETURN state = .ok (stateZ, cost)) :
    MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat ≤
      maxReturnDataWordsByGas := by
  let words := MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat
  have hwords_lt : words < UInt256.size :=
    MachineState.M_lt_uint256_size state.machineState.activeWords.val.isLt
      offset.val.isLt len.val.isLt
  have hactive_le : state.machineState.activeWords.toNat ≤ words :=
    MachineState.M_ge_active _ _ _
  have hmono : Cₘ state.machineState.activeWords ≤ Cₘ (.ofNat words) := by
    rw [← UInt256.ofNat_toNat state.machineState.activeWords]
    exact Cₘ_monotone_of_lt hactive_le hwords_lt
  have hmem := Z_memoryExpansionCost_le hZ
  have hmem' :
      Cₘ (.ofNat words) - Cₘ state.machineState.activeWords ≤
        state.machineState.gasAvailable.toNat := by
    have h0 := Stack.pop2_getD0 hpop
    have h1 := Stack.pop2_getD1 hpop
    simpa [memoryExpansionCost, memoryExpansionCost.μᵢ', h0, h1, words] using hmem
  have hcost_lt : Cₘ (.ofNat words) < UInt256.size := by
    have hadd :
        Cₘ (.ofNat words) =
          Cₘ state.machineState.activeWords +
            (Cₘ (.ofNat words) - Cₘ state.machineState.activeWords) := by
      omega
    rw [hadd]
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hmem' _ ) hpaid
  exact maxReturnDataWordsByGas_ge_of_Cₘ_lt hwords_lt hcost_lt

lemma revert_words_le_maxReturnDataWordsByGas_of_Z
    {validJumps : Array UInt256} {state stateZ : State} {cost : Nat}
    {stack : Stack UInt256} {offset len : UInt256}
    (hpaid : memoryPaidByGas state)
    (hpop : state.machineState.stack.pop2 = some (stack, offset, len))
    (hZ : Z validJumps Operation.REVERT state = .ok (stateZ, cost)) :
    MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat ≤
      maxReturnDataWordsByGas := by
  let words := MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat
  have hwords_lt : words < UInt256.size :=
    MachineState.M_lt_uint256_size state.machineState.activeWords.val.isLt
      offset.val.isLt len.val.isLt
  have hactive_le : state.machineState.activeWords.toNat ≤ words :=
    MachineState.M_ge_active _ _ _
  have hmono : Cₘ state.machineState.activeWords ≤ Cₘ (.ofNat words) := by
    rw [← UInt256.ofNat_toNat state.machineState.activeWords]
    exact Cₘ_monotone_of_lt hactive_le hwords_lt
  have hmem := Z_memoryExpansionCost_le hZ
  have hmem' :
      Cₘ (.ofNat words) - Cₘ state.machineState.activeWords ≤
        state.machineState.gasAvailable.toNat := by
    have h0 := Stack.pop2_getD0 hpop
    have h1 := Stack.pop2_getD1 hpop
    simpa [memoryExpansionCost, memoryExpansionCost.μᵢ', h0, h1, words] using hmem
  have hcost_lt : Cₘ (.ofNat words) < UInt256.size := by
    have hadd :
        Cₘ (.ofNat words) =
          Cₘ state.machineState.activeWords +
            (Cₘ (.ofNat words) - Cₘ state.machineState.activeWords) := by
      omega
    rw [hadd]
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hmem' _ ) hpaid
  exact maxReturnDataWordsByGas_ge_of_Cₘ_lt hwords_lt hcost_lt

lemma ByteArray.readWithoutPadding_size_le (b : ByteArray) (addr len : Nat) :
    (b.readWithoutPadding addr len).size ≤ len := by
  unfold ByteArray.readWithoutPadding
  split
  · simp
  · rw [ByteArray.size_extract]
    omega

private lemma ByteArray.toList_loop_length (b : ByteArray) :
    ∀ i r, i ≤ b.size →
      (ByteArray.toList.loop b i r).length = r.length + (b.size - i) := by
  intro i
  induction h : b.size - i using Nat.strong_induction_on generalizing i with
  | h n ih =>
      intro r hi
      rw [ByteArray.toList.loop.eq_def]
      by_cases hlt : i < b.size
      · simp [hlt]
        have hi' : i + 1 ≤ b.size := Nat.succ_le_of_lt hlt
        have hn' : b.size - (i + 1) < n := by omega
        have hrec := ih (b.size - (i + 1)) hn' (i + 1) (by rfl) (b.get! i :: r) hi'
        rw [hrec]
        simp
        omega
      · simp [hlt]
        omega

private lemma ByteArray.toList_length (b : ByteArray) :
    b.toList.length = b.size := by
  unfold ByteArray.toList
  have h := ByteArray.toList_loop_length b 0 [] (Nat.zero_le _)
  simpa using h

lemma fromByteArrayBigEndian_lt (b : ByteArray) :
    fromByteArrayBigEndian b < 2 ^ (8 * b.size) := by
  unfold fromByteArrayBigEndian fromBytesBigEndian
  have h := Ethereum.fromBytes'_le (bs := b.toList.reverse)
  simpa [List.length_reverse, ByteArray.toList_length] using h

lemma nat_of_slice_lt (b : ByteArray) (start width : Nat) :
    nat_of_slice b start width < 2 ^ (8 * width) := by
  unfold nat_of_slice
  let slice := b.readWithoutPadding start width
  have hslice : slice.size ≤ width := ByteArray.readWithoutPadding_size_le b start width
  have hval := fromByteArrayBigEndian_lt slice
  change fromByteArrayBigEndian slice <<< (8 * (width - slice.size)) < 2 ^ (8 * width)
  rw [Nat.shiftLeft_eq]
  have hmul := Nat.mul_lt_mul_of_pos_right hval (Nat.two_pow_pos (8 * (width - slice.size)))
  rw [← Nat.pow_add] at hmul
  have hadd : 8 * slice.size + 8 * (width - slice.size) = 8 * width := by omega
  simpa [hadd] using hmul

private lemma USize.toNat_ofBitVec_sub_ofNat_le {a b : Nat} (h : b ≤ a) :
    (USize.ofBitVec ((a : BitVec System.Platform.numBits) -
      (b : BitVec System.Platform.numBits))).toNat ≤ a - b := by
  rw [USize.toNat]
  simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
  set M : Nat := 2 ^ System.Platform.numBits
  have hMpos : 0 < M := by
    dsimp [M]
    exact pow_pos (by decide : 0 < 2) _
  have hbmodle : b % M ≤ M := Nat.le_of_lt (Nat.mod_lt b hMpos)
  have hcomm : M - b % M + a = a + M - b % M := by omega
  rw [hcomm]
  change (a + M - b % M) % M ≤ a - b
  have hmod : (a + M - b % M) % M = (a - b) % M := by
    change (a + M - b % M) ≡ (a - b) [MOD M]
    have h₁ : a + M ≡ a [MOD M] := by
      unfold Nat.ModEq
      rw [Nat.add_mod_right]
    have h₂ : b % M ≡ b [MOD M] := by
      unfold Nat.ModEq
      rw [Nat.mod_mod]
    exact Nat.ModEq.sub (by omega) h h₁ h₂
  rw [hmod]
  exact Nat.mod_le _ _

private lemma USize.toNat_ofNat_le (n : Nat) :
    (USize.ofNat n).toNat ≤ n := by
  rw [USize.toNat]
  simp [USize.ofNat, BitVec.toNat_ofNat]
  exact Nat.mod_le _ _

lemma ByteArray.readWithPadding_size_le (b : ByteArray) (addr len : Nat) :
    (b.readWithPadding addr len).size ≤ len := by
  unfold ByteArray.readWithPadding
  rw [ByteArray.size_append, ByteArray_zeroes_size]
  have hread := ByteArray.readWithoutPadding_size_le b addr len
  omega

lemma ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas
    (b : ByteArray) (addr len : Nat) (hlen : len ≤ maxReturnDataSizeByGas) :
    (b.readWithPadding addr len).size ≤ maxReturnDataSizeByGas := by
  exact Nat.le_trans (ByteArray.readWithPadding_size_le b addr len) hlen

lemma ByteArray.readWithPadding_size_lt_uint256
    (b : ByteArray) (addr len : Nat) (hlen : len ≤ maxReturnDataSizeByGas) :
    (b.readWithPadding addr len).size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas b addr len hlen)
    maxReturnDataSizeByGas_lt_uint256

lemma MachineState.M_len_le_words_mul (s f l : Nat) :
    l ≤ 32 * MachineState.M s f l := by
  unfold MachineState.M
  cases l with
  | zero => simp
  | succ l =>
      simp only
      have hceil : f + (l + 1) ≤ 32 * ((f + (l + 1) + 31) / 32) := by
        have hdiv :
            (f + (l + 1) + 31) / 32 ≤ (f + (l + 1) + 31) / 32 := le_rfl
        rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)] at hdiv
        omega
      have hmax : (f + (l + 1) + 31) / 32 ≤
          max s ((f + (l + 1) + 31) / 32) := by
        exact Nat.le_max_right _ _
      nlinarith

lemma ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas_of_words
    (b : ByteArray) (active offset len : Nat)
    (hwords : MachineState.M active offset len ≤ maxReturnDataWordsByGas) :
    (b.readWithPadding offset len).size ≤ maxReturnDataSizeByGas := by
  have hread := ByteArray.readWithPadding_size_le b offset len
  have hlen_words := MachineState.M_len_le_words_mul active offset len
  unfold maxReturnDataSizeByGas
  exact Nat.le_trans hread (by nlinarith)

private lemma call_input_size_le_maxReturnDataSizeByGas_of_Z
    {validJumps : Array UInt256} {op : Operation}
    {state stateZ : State} {cost : Nat}
    {stack : Stack UInt256}
    {gas target value inOffset inSize outOffset outSize : UInt256}
    (hop : op = Operation.CALL ∨ op = Operation.CALLCODE)
    (hpaid : memoryPaidByGas state)
    (hpop : state.machineState.stack.pop7 =
      some (stack, gas, target, value, inOffset, inSize, outOffset, outSize))
    (hZ : Z validJumps op state = .ok (stateZ, cost)) :
    (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
      maxReturnDataSizeByGas := by
  have htarget := memoryPaidByGas_after_Z_target hpaid hZ
  have hcost_lt :
      Cₘ (.ofNat (memoryExpansionWords state op)) < UInt256.size := by
    omega
  have htarget_words :
      memoryExpansionWords state op ≤ maxReturnDataWordsByGas :=
    maxReturnDataWordsByGas_ge_of_Cₘ_lt
      (memoryExpansionWords_lt_uint256_size state op) hcost_lt
  have hidx := Stack.pop7_get!3456 hpop
  have hinput :
      MachineState.M state.machineState.activeWords.toNat inOffset.toNat inSize.toNat ≤
        memoryExpansionWords state op := by
    rcases hop with rfl | rfl
    · simpa [memoryExpansionWords, hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2]
        using MachineState.M_ge_active
          (MachineState.M state.machineState.activeWords.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat
    · simpa [memoryExpansionWords, hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2]
        using MachineState.M_ge_active
          (MachineState.M state.machineState.activeWords.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat
  exact ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas_of_words
    state.machineState.memory state.machineState.activeWords.toNat inOffset.toNat inSize.toNat
    (Nat.le_trans hinput htarget_words)

private lemma delegate_input_size_le_maxReturnDataSizeByGas_of_Z
    {validJumps : Array UInt256} {op : Operation}
    {state stateZ : State} {cost : Nat}
    {stack : Stack UInt256}
    {gas target inOffset inSize outOffset outSize : UInt256}
    (hop : op = Operation.DELEGATECALL ∨ op = Operation.STATICCALL)
    (hpaid : memoryPaidByGas state)
    (hpop : state.machineState.stack.pop6 =
      some (stack, gas, target, inOffset, inSize, outOffset, outSize))
    (hZ : Z validJumps op state = .ok (stateZ, cost)) :
    (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
      maxReturnDataSizeByGas := by
  have htarget := memoryPaidByGas_after_Z_target hpaid hZ
  have hcost_lt :
      Cₘ (.ofNat (memoryExpansionWords state op)) < UInt256.size := by
    omega
  have htarget_words :
      memoryExpansionWords state op ≤ maxReturnDataWordsByGas :=
    maxReturnDataWordsByGas_ge_of_Cₘ_lt
      (memoryExpansionWords_lt_uint256_size state op) hcost_lt
  have hidx := Stack.pop6_get!2345 hpop
  have hinput :
      MachineState.M state.machineState.activeWords.toNat inOffset.toNat inSize.toNat ≤
        memoryExpansionWords state op := by
    rcases hop with rfl | rfl
    · simpa [memoryExpansionWords, hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2]
        using MachineState.M_ge_active
          (MachineState.M state.machineState.activeWords.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat
    · simpa [memoryExpansionWords, hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2]
        using MachineState.M_ge_active
          (MachineState.M state.machineState.activeWords.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat
  exact ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas_of_words
    state.machineState.memory state.machineState.activeWords.toNat inOffset.toNat inSize.toNat
    (Nat.le_trans hinput htarget_words)

lemma MachineState.evmReturn_H_return_size_le_words_mul
    (machine : MachineState) (offset len : UInt256) :
    (machine.evmReturn offset len).H_return.size ≤
      32 * MachineState.M machine.activeWords.toNat offset.toNat len.toNat := by
  unfold MachineState.evmReturn
  have hread := ByteArray.readWithPadding_size_le
    machine.memory offset.toNat len.toNat
  have hwords := MachineState.M_len_le_words_mul
    machine.activeWords.toNat offset.toNat len.toNat
  simp
  exact Nat.le_trans hread hwords

lemma MachineState.evmRevert_H_return_size_le_words_mul
    (machine : MachineState) (offset len : UInt256) :
    (machine.evmRevert offset len).H_return.size ≤
      32 * MachineState.M machine.activeWords.toNat offset.toNat len.toNat := by
  unfold MachineState.evmRevert
  simpa [MachineState.evmReturn] using
    MachineState.evmReturn_H_return_size_le_words_mul machine offset len

lemma MachineState.evmReturn_H_return_size_le_maxReturnDataSizeByGas_of_words
    (machine : MachineState) (offset len : UInt256)
    (hwords :
      MachineState.M machine.activeWords.toNat offset.toNat len.toNat ≤
        maxReturnDataWordsByGas) :
    (machine.evmReturn offset len).H_return.size ≤ maxReturnDataSizeByGas := by
  unfold maxReturnDataSizeByGas
  exact Nat.le_trans
    (MachineState.evmReturn_H_return_size_le_words_mul machine offset len)
    (Nat.mul_le_mul_left 32 hwords)

lemma MachineState.evmRevert_H_return_size_le_maxReturnDataSizeByGas_of_words
    (machine : MachineState) (offset len : UInt256)
    (hwords :
      MachineState.M machine.activeWords.toNat offset.toNat len.toNat ≤
        maxReturnDataWordsByGas) :
    (machine.evmRevert offset len).H_return.size ≤ maxReturnDataSizeByGas := by
  unfold maxReturnDataSizeByGas
  exact Nat.le_trans
    (MachineState.evmRevert_H_return_size_le_words_mul machine offset len)
    (Nat.mul_le_mul_left 32 hwords)

lemma MachineState.evmReturn_H_return_size_le_maxReturnDataSizeByGas
    (machine : MachineState) (offset len : UInt256)
    (hwords :
      MachineState.M machine.activeWords.toNat offset.toNat len.toNat ≤
        maxReturnDataWordsByGas) :
    (machine.evmReturn offset len).H_return.size ≤ maxReturnDataSizeByGas := by
  exact MachineState.evmReturn_H_return_size_le_maxReturnDataSizeByGas_of_words
    machine offset len hwords

lemma MachineState.evmRevert_H_return_size_le_maxReturnDataSizeByGas
    (machine : MachineState) (offset len : UInt256)
    (hwords :
      MachineState.M machine.activeWords.toNat offset.toNat len.toNat ≤
        maxReturnDataWordsByGas) :
    (machine.evmRevert offset len).H_return.size ≤ maxReturnDataSizeByGas := by
  exact MachineState.evmRevert_H_return_size_le_maxReturnDataSizeByGas_of_words
    machine offset len hwords

lemma step_return_H_return_size_le_maxReturnDataSizeByGas {cost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (hwords : ∀ {stack : Stack UInt256} {offset len : UInt256},
      state.machineState.stack.pop2 = some (stack, offset, len) →
        MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat ≤
          maxReturnDataWordsByGas)
    (h : step cost (.RETURN, arg) state = .ok state') :
    state'.machineState.H_return.size ≤ maxReturnDataSizeByGas := by
  unfold step at h
  simp [binaryMachineStateOp] at h
  cases hpop : state.machineState.stack.pop2 with
  | none =>
      simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, len⟩
      simp [hpop, MachineState.evmReturn, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      exact MachineState.evmReturn_H_return_size_le_maxReturnDataSizeByGas
        { state.machineState with
          execLength := state.machineState.execLength + 1,
          gasAvailable := state.machineState.gasAvailable.subNat cost }
        offset len (hwords hpop)

lemma step_revert_H_return_size_le_maxReturnDataSizeByGas {cost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (hwords : ∀ {stack : Stack UInt256} {offset len : UInt256},
      state.machineState.stack.pop2 = some (stack, offset, len) →
        MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat ≤
          maxReturnDataWordsByGas)
    (h : step cost (.REVERT, arg) state = .ok state') :
    state'.machineState.H_return.size ≤ maxReturnDataSizeByGas := by
  unfold step at h
  simp [binaryMachineStateOp] at h
  cases hpop : state.machineState.stack.pop2 with
  | none =>
      simp [hpop] at h
  | some popped =>
      rcases popped with ⟨stack, offset, len⟩
      simp [hpop, MachineState.evmRevert, MachineState.evmReturn,
        Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
      injection h with hstate
      subst state'
      exact MachineState.evmRevert_H_return_size_le_maxReturnDataSizeByGas
        { state.machineState with
          execLength := state.machineState.execLength + 1,
          gasAvailable := state.machineState.gasAvailable.subNat cost }
        offset len (hwords hpop)

lemma MachineState.evmReturn_H_return_size_lt_uint256
    (machine : MachineState) (offset len : UInt256)
    (hwords :
      MachineState.M machine.activeWords.toNat offset.toNat len.toNat ≤
        maxReturnDataWordsByGas) :
    (machine.evmReturn offset len).H_return.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (MachineState.evmReturn_H_return_size_le_maxReturnDataSizeByGas machine offset len hwords)
    maxReturnDataSizeByGas_lt_uint256

lemma MachineState.evmRevert_H_return_size_lt_uint256
    (machine : MachineState) (offset len : UInt256)
    (hwords :
      MachineState.M machine.activeWords.toNat offset.toNat len.toNat ≤
        maxReturnDataWordsByGas) :
    (machine.evmRevert offset len).H_return.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (MachineState.evmRevert_H_return_size_le_maxReturnDataSizeByGas machine offset len hwords)
    maxReturnDataSizeByGas_lt_uint256

lemma step_return_H_return_size_lt_uint256 {cost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (hwords : ∀ {stack : Stack UInt256} {offset len : UInt256},
      state.machineState.stack.pop2 = some (stack, offset, len) →
        MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat ≤
          maxReturnDataWordsByGas)
    (h : step cost (.RETURN, arg) state = .ok state') :
    state'.machineState.H_return.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_return_H_return_size_le_maxReturnDataSizeByGas hwords h)
    maxReturnDataSizeByGas_lt_uint256

lemma step_revert_H_return_size_lt_uint256 {cost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (hwords : ∀ {stack : Stack UInt256} {offset len : UInt256},
      state.machineState.stack.pop2 = some (stack, offset, len) →
        MachineState.M state.machineState.activeWords.toNat offset.toNat len.toNat ≤
          maxReturnDataWordsByGas)
    (h : step cost (.REVERT, arg) state = .ok state') :
    state'.machineState.H_return.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_revert_H_return_size_le_maxReturnDataSizeByGas hwords h)
    maxReturnDataSizeByGas_lt_uint256

lemma Xstep_halt_output_size_le_maxReturnDataSizeByGas
    {validJumps : Array UInt256} {state state' : State}
    {cause : HaltCause} {out : ByteArray}
    (hpaid : memoryPaidByGas state)
    (h : Xstep validJumps state = .ok (state', some (cause, out))) :
    out.size ≤ maxReturnDataSizeByGas := by
  unfold Xstep at h
  simp [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i cost hZ
    split at h
    · contradiction
    · rename_i stepped hstep
      generalize hinstr :
        (decode state.executionEnv.code state.machineState.pc).getD (.STOP, none) = instr at hZ hstep h
      rcases instr with ⟨op, arg⟩
      cases op with
      | StopArith sop =>
          cases sop <;> simp at h
          · rcases h with ⟨_, _, hout⟩
            subst out
            simp [maxReturnDataSizeByGas]
      | CompBit op => cases op <;> simp at h
      | Keccak op =>
          cases op
          simp at h
      | Env op => cases op <;> simp at h
      | Block op => cases op <;> simp at h
      | StackMemFlow op => cases op <;> simp at h
      | Push op => cases op <;> simp at h
      | Dup op => cases op <;> simp at h
      | Exchange op => cases op <;> simp at h
      | Log op => cases op <;> simp at h
      | System sop =>
          cases sop <;> simp at h
          · rcases h with ⟨_, _, hout⟩
            subst out
            refine step_return_H_return_size_le_maxReturnDataSizeByGas ?_ hstep
            ·
                intro stack offset len hpop
                have hsame := Z_stack_active_eq (by simpa using hZ)
                have hpop0 :
                    state.machineState.stack.pop2 = some (stack, offset, len) := by
                  simpa [hsame.1] using hpop
                have hbound :=
                  return_words_le_maxReturnDataWordsByGas_of_Z hpaid hpop0 (by simpa using hZ)
                simpa [hsame.2.1] using hbound
          · rcases h with ⟨_, _, hout⟩
            subst out
            refine step_revert_H_return_size_le_maxReturnDataSizeByGas ?_ hstep
            ·
                intro stack offset len hpop
                have hsame := Z_stack_active_eq (by simpa using hZ)
                have hpop0 :
                    state.machineState.stack.pop2 = some (stack, offset, len) := by
                  simpa [hsame.1] using hpop
                have hbound :=
                  revert_words_le_maxReturnDataWordsByGas_of_Z hpaid hpop0 (by simpa using hZ)
                simpa [hsame.2.1] using hbound
          · rcases h with ⟨_, _, hout⟩
            subst out
            simp [maxReturnDataSizeByGas]

lemma Xstep_halt_output_size_lt_uint256 {validJumps : Array UInt256} {state state' : State}
    {cause : HaltCause} {out : ByteArray}
    (hpaid : memoryPaidByGas state)
    (h : Xstep validJumps state = .ok (state', some (cause, out))) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (Xstep_halt_output_size_le_maxReturnDataSizeByGas hpaid h)
    maxReturnDataSizeByGas_lt_uint256

lemma Xstep_memoryPaidByGas_of_none {validJumps : Array UInt256} {state state' : State}
    (hpaid : memoryPaidByGas state)
    (h : Xstep validJumps state = .ok (state', none)) :
    memoryPaidByGas state' := by
  unfold Xstep at h
  cases hinstr : (decode state.executionEnv.code state.machineState.pc).getD (Operation.STOP, none) with
  | mk w arg =>
      simp [hinstr, bind, Except.bind] at h
      cases hZ : Z validJumps w state <;> simp [hZ] at h
      rename_i z
      rcases z with ⟨stateZ, cost₂⟩
      cases hstep :
          step cost₂ (w, arg) { stateZ with executionEnv.depth := state.executionEnv.depth } <;>
        simp [hstep] at h
      rename_i stateStep
      repeat (first | split at h | cases h)
      all_goals
        try (by_cases hwrev : w = Operation.REVERT <;> simp [hwrev] at h)
        try cases h
      have htarget :=
        memoryPaidByGas_after_Z_target hpaid (by simpa using hZ)
      have hsame := Z_stack_active_eq (by simpa using hZ)
      have hactive :
          stateStep.machineState.activeWords.toNat ≤ memoryExpansionWords state w := by
        by_cases hcreate : w = Operation.CREATE
        · subst w
          have hstepActive :=
            step_create_activeWords_le_memoryExpansionWords
              (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
          simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
        · by_cases hcreate2 : w = Operation.CREATE2
          · subst w
            have hstepActive :=
              step_create2_activeWords_le_memoryExpansionWords
                (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
            simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
          · by_cases hcall : w = Operation.CALL
            · subst w
              have hstepActive :=
                step_call_activeWords_le_memoryExpansionWords
                  (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
              simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
            · by_cases hcallcode : w = Operation.CALLCODE
              · subst w
                have hstepActive :=
                  step_callcode_activeWords_le_memoryExpansionWords
                    (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
              · by_cases hdelegate : w = Operation.DELEGATECALL
                · subst w
                  have hstepActive :=
                    step_delegatecall_activeWords_le_memoryExpansionWords
                      (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                  simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                · by_cases hstatic : w = Operation.STATICCALL
                  · subst w
                    have hstepActive :=
                      step_staticcall_activeWords_le_memoryExpansionWords
                        (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                    simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                  · by_cases hreturn : w = Operation.RETURN
                    · subst w
                      have hstepActive :=
                        step_return_activeWords_le_memoryExpansionWords
                          (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                      simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                    · by_cases hrevert : w = Operation.REVERT
                      · subst w
                        have hstepActive :=
                          step_revert_activeWords_le_memoryExpansionWords
                            (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                        simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                      · by_cases hmload : w = Operation.MLOAD
                        · subst w
                          have hstepActive :=
                            step_mload_activeWords_le_memoryExpansionWords
                              (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                          simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                        · by_cases hmstore : w = Operation.MSTORE
                          · subst w
                            have hstepActive :=
                              step_mstore_activeWords_le_memoryExpansionWords
                                (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                            simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                          · by_cases hmstore8 : w = Operation.MSTORE8
                            · subst w
                              have hstepActive :=
                                step_mstore8_activeWords_le_memoryExpansionWords
                                  (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                              simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                            · by_cases hkeccak : w = Operation.KECCAK256
                              · subst w
                                have hstepActive :=
                                  step_keccak_activeWords_le_memoryExpansionWords
                                    (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                              · by_cases hcalldatacopy : w = Operation.CALLDATACOPY
                                · subst w
                                  have hstepActive :=
                                    step_calldatacopy_activeWords_le_memoryExpansionWords
                                      (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                  simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                                · by_cases hcodecopy : w = Operation.CODECOPY
                                  · subst w
                                    have hstepActive :=
                                      step_codecopy_activeWords_le_memoryExpansionWords
                                        (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                    simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                                  · by_cases hreturndatacopy : w = Operation.RETURNDATACOPY
                                    · subst w
                                      have hstepActive :=
                                        step_returndatacopy_activeWords_le_memoryExpansionWords
                                          (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                      simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                                    · by_cases hextcodecopy : w = Operation.EXTCODECOPY
                                      · subst w
                                        have hstepActive :=
                                          step_extcodecopy_activeWords_le_memoryExpansionWords
                                            (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                        simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                                      · by_cases hmcopy : w = Operation.MCOPY
                                        · subst w
                                          have hstepActive :=
                                            step_mcopy_activeWords_le_memoryExpansionWords
                                              (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                          simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                                        · by_cases hlog0 : w = Operation.LOG0
                                          · subst w
                                            have hstepActive :=
                                              step_log0_activeWords_le_memoryExpansionWords
                                                (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                            simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                                          · by_cases hlog1 : w = Operation.LOG1
                                            · subst w
                                              have hstepActive :=
                                                step_log1_activeWords_le_memoryExpansionWords
                                                  (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                              simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                                            · by_cases hlog2 : w = Operation.LOG2
                                              · subst w
                                                have hstepActive :=
                                                  step_log2_activeWords_le_memoryExpansionWords
                                                    (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                                simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                                              · by_cases hlog3 : w = Operation.LOG3
                                                · subst w
                                                  have hstepActive :=
                                                    step_log3_activeWords_le_memoryExpansionWords
                                                      (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                                  simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                                                · by_cases hlog4 : w = Operation.LOG4
                                                  · subst w
                                                    have hstepActive :=
                                                      step_log4_activeWords_le_memoryExpansionWords
                                                        (state := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
                                                    simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
                                                  · have hstepActive :=
                                                      step_activeWords_le_memoryExpansionWords (state := { stateZ with
                                                        executionEnv.depth := state.executionEnv.depth }) hstep
                                                    simpa [memoryExpansionWords, hsame.1, hsame.2.1] using hstepActive
      have hwords_lt := memoryExpansionWords_lt_uint256_size state w
      have hmono :
          Cₘ stateStep.machineState.activeWords ≤
            Cₘ (.ofNat (memoryExpansionWords state w)) := by
        rw [← UInt256.ofNat_toNat stateStep.machineState.activeWords]
        exact Cₘ_monotone_of_lt hactive hwords_lt
      have hgas :=
        step_gas_le (w := w) (arg := arg)
          (s := { stateZ with executionEnv.depth := state.executionEnv.depth }) hstep
      unfold memoryPaidByGas
      have hle :
          Cₘ stateStep.machineState.activeWords +
              stateStep.machineState.gasAvailable.toNat ≤
            Cₘ (.ofNat (memoryExpansionWords state w)) +
              stateZ.machineState.gasAvailable.toNat := by
        exact Nat.add_le_add hmono hgas
      exact Nat.lt_of_le_of_lt hle htarget

lemma X_success_output_size_le_maxReturnDataSizeByGas
    {fuel : Nat} {validJumps : Array UInt256}
    {state state' : State} {out : ByteArray}
    (hpaid : memoryPaidByGas state)
    (h : X fuel validJumps state = .ok (.success state' out)) :
    out.size ≤ maxReturnDataSizeByGas := by
  induction fuel generalizing state with
  | zero =>
      simp [X] at h
  | succ fuel ih =>
      unfold X at h
      simp [bind, Except.bind] at h
      cases hstep : Xstep validJumps state with
      | error e => simp [hstep] at h
      | ok res =>
          rcases res with ⟨state₁, ret⟩
          simp [hstep] at h
          cases ret with
          | none =>
              let stateCont : State :=
                { state₁ with executionEnv.depth := state.executionEnv.depth }
              have hpaidCont : memoryPaidByGas stateCont := by
                simpa [stateCont, memoryPaidByGas] using
                  Xstep_memoryPaidByGas_of_none hpaid hstep
              have hcont :
                  X fuel validJumps stateCont = .ok (.success state' out) := by
                simpa [stateCont] using h
              exact ih hpaidCont hcont
          | some halted =>
              rcases halted with ⟨cause, haltOut⟩
              cases cause <;> simp at h
              rcases h with ⟨_, hout⟩
              subst out
              exact Xstep_halt_output_size_le_maxReturnDataSizeByGas hpaid hstep

lemma X_success_output_size_lt_uint256 {fuel : Nat} {validJumps : Array UInt256}
    {state state' : State} {out : ByteArray}
    (hpaid : memoryPaidByGas state)
    (h : X fuel validJumps state = .ok (.success state' out)) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (X_success_output_size_le_maxReturnDataSizeByGas hpaid h)
    maxReturnDataSizeByGas_lt_uint256

lemma X_revert_output_size_le_maxReturnDataSizeByGas
    {fuel : Nat} {validJumps : Array UInt256}
    {state : State} {g : UInt256} {out : ByteArray}
    (hpaid : memoryPaidByGas state)
    (h : X fuel validJumps state = .ok (.revert g out)) :
    out.size ≤ maxReturnDataSizeByGas := by
  induction fuel generalizing state with
  | zero =>
      simp [X] at h
  | succ fuel ih =>
      unfold X at h
      simp [bind, Except.bind] at h
      cases hstep : Xstep validJumps state with
      | error e => simp [hstep] at h
      | ok res =>
          rcases res with ⟨state₁, ret⟩
          simp [hstep] at h
          cases ret with
          | none =>
              let stateCont : State :=
                { state₁ with executionEnv.depth := state.executionEnv.depth }
              have hpaidCont : memoryPaidByGas stateCont := by
                simpa [stateCont, memoryPaidByGas] using
                  Xstep_memoryPaidByGas_of_none hpaid hstep
              have hcont :
                  X fuel validJumps stateCont = .ok (.revert g out) := by
                simpa [stateCont] using h
              exact ih hpaidCont hcont
          | some halted =>
              rcases halted with ⟨cause, haltOut⟩
              cases cause <;> simp at h
              rcases h with ⟨_, hout⟩
              subst out
              exact Xstep_halt_output_size_le_maxReturnDataSizeByGas hpaid hstep

lemma X_revert_output_size_lt_uint256 {fuel : Nat} {validJumps : Array UInt256}
    {state : State} {g : UInt256} {out : ByteArray}
    (hpaid : memoryPaidByGas state)
    (h : X fuel validJumps state = .ok (.revert g out)) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (X_revert_output_size_le_maxReturnDataSizeByGas hpaid h)
    maxReturnDataSizeByGas_lt_uint256

lemma Xi_success_output_size_le_maxReturnDataSizeByGas
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {res : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate}
    {out : ByteArray}
    (h : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.success res out)) :
    out.size ≤ maxReturnDataSizeByGas := by
  unfold Ξ at h
  simp [bind, Except.bind] at h
  cases hx : X (g.toNat + 1) (D_J I.code 0)
      { (default : State) with
        accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
        createdAccounts := createdAccounts, machineState.gasAvailable := .ofUInt256 g,
        blocks := blocks, genesisBlockHeader := genesisBlockHeader } with
  | error e => simp [hx] at h
  | ok xres =>
      cases xres with
      | success state' xiOut =>
          have hpaid₀ :
              memoryPaidByGas
                { (default : State) with
                  accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
                  createdAccounts := createdAccounts, machineState.gasAvailable := .ofUInt256 g,
                  blocks := blocks, genesisBlockHeader := genesisBlockHeader } := by
            simp only [memoryPaidByGas, Cₘ, GasConstants.Gmemory, Cₘ.QuadraticCeofficient]
            have h0 : (default : State).machineState.activeWords.toNat = 0 := by rfl
            rw [h0]
            simpa only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.zero_div]
              using g.val.isLt
          have hout := X_success_output_size_le_maxReturnDataSizeByGas hpaid₀ hx
          simp [hx] at h
          rcases h with ⟨_, houtEq⟩
          subst out
          exact hout
      | revert g' xiOut =>
          simp [hx] at h

lemma Xi_success_output_size_lt_uint256
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {res : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate}
    {out : ByteArray}
    (h : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.success res out)) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (Xi_success_output_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

lemma Xi_revert_output_size_le_maxReturnDataSizeByGas
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {g' : UInt256} {out : ByteArray}
    (h : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' out)) :
    out.size ≤ maxReturnDataSizeByGas := by
  unfold Ξ at h
  simp [bind, Except.bind] at h
  cases hx : X (g.toNat + 1) (D_J I.code 0)
      { (default : State) with
        accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
        createdAccounts := createdAccounts, machineState.gasAvailable := .ofUInt256 g,
        blocks := blocks, genesisBlockHeader := genesisBlockHeader } with
  | error e => simp [hx] at h
  | ok xres =>
      cases xres with
      | success state' xiOut =>
          simp [hx] at h
      | revert gₓ xiOut =>
          have hpaid₀ :
              memoryPaidByGas
                { (default : State) with
                  accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
                  createdAccounts := createdAccounts, machineState.gasAvailable := .ofUInt256 g,
                  blocks := blocks, genesisBlockHeader := genesisBlockHeader } := by
            simp only [memoryPaidByGas, Cₘ, GasConstants.Gmemory, Cₘ.QuadraticCeofficient]
            have h0 : (default : State).machineState.activeWords.toNat = 0 := by rfl
            rw [h0]
            simpa only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.zero_div]
              using g.val.isLt
          have hout := X_revert_output_size_le_maxReturnDataSizeByGas hpaid₀ hx
          simp [hx] at h
          rcases h with ⟨_, houtEq⟩
          subst out
          exact hout

lemma Xi_revert_output_size_lt_uint256
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {g' : UInt256} {out : ByteArray}
    (h : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' out)) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (Xi_revert_output_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

lemma Xi_tuple_match_output_size_le_maxReturnDataSizeByGas
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (match Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
      | .error _ => (createdAccounts, ∅, (⟨0⟩ : UInt256), A, ByteArray.empty)
      | .ok (.revert g' out) => (createdAccounts, ∅, g', A, out)
      | .ok (.success (createdAccounts', σ', g', A') out) =>
          (createdAccounts', σ', g', A', out)).2.2.2.2.size ≤ maxReturnDataSizeByGas := by
  cases hxi : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
  | error err =>
      simp [maxReturnDataSizeByGas]
  | ok xres =>
      cases xres with
      | revert g' out =>
          exact Xi_revert_output_size_le_maxReturnDataSizeByGas hxi
      | success res out =>
          rcases res with ⟨createdAccounts', σ', g', A'⟩
          exact Xi_success_output_size_le_maxReturnDataSizeByGas hxi

lemma Xi_tuple_match_output_size_lt_uint256
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (match Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
      | .error _ => (createdAccounts, ∅, (⟨0⟩ : UInt256), A, ByteArray.empty)
      | .ok (.revert g' out) => (createdAccounts, ∅, g', A, out)
      | .ok (.success (createdAccounts', σ', g', A') out) =>
          (createdAccounts', σ', g', A', out)).2.2.2.2.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (Xi_tuple_match_output_size_le_maxReturnDataSizeByGas
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    maxReturnDataSizeByGas_lt_uint256

lemma Lambda_Xi_tuple_match_output_size_le_maxReturnDataSizeByGas
    (a : AccountAddress) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σStar σ₀ : AccountMap) (g : UInt256) (AStar : Substate) (I : ExecutionEnv) :
    (match Ξ createdAccounts genesisBlockHeader blocks σStar σ₀ g AStar I with
      | .error _ => (a, createdAccounts, σ, (⟨0⟩ : UInt256), AStar, false, ByteArray.empty)
      | .ok (.revert g' out) => (a, createdAccounts, σ, g', AStar, false, out)
      | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
          let c := GasConstants.Gcodedeposit * returnedData.size
          let F : Bool := Id.run do
            let F₀ : Bool :=
              match σ.find? a with
              | .some ac => ac.code ≠ ByteArray.empty ∨ ac.nonce ≠ (⟨0⟩ : UInt256)
              | .none => false
            let F₂ : Bool := gStarStar.toNat < c
            let MAX_CODE_SIZE := 24576
            let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
            let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
            pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)
          let σ' : AccountMap :=
            if F then σ else
              let newAccount' := σStarStar.findD a default
              σStarStar.insert a {newAccount' with code := returnedData}
          let g' := if F then 0 else gStarStar.toNat - c
          let A' := if F then AStar else AStarStar
          let z := not F
          (a, createdAccounts', σ', .ofNat g', A', z, ByteArray.empty)).2.2.2.2.2.2.size ≤
      maxReturnDataSizeByGas := by
  cases hxi : Ξ createdAccounts genesisBlockHeader blocks σStar σ₀ g AStar I with
  | error err =>
      simp [maxReturnDataSizeByGas]
  | ok xres =>
      cases xres with
      | revert g' out =>
          exact Xi_revert_output_size_le_maxReturnDataSizeByGas hxi
      | success res returnedData =>
          rcases res with ⟨createdAccounts', σStarStar, gStarStar, AStarStar⟩
          simp [maxReturnDataSizeByGas]

lemma Lambda_Xi_tuple_match_output_size_lt_uint256
    (a : AccountAddress) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σStar σ₀ : AccountMap) (g : UInt256) (AStar : Substate) (I : ExecutionEnv) :
    (match Ξ createdAccounts genesisBlockHeader blocks σStar σ₀ g AStar I with
      | .error _ => (a, createdAccounts, σ, (⟨0⟩ : UInt256), AStar, false, ByteArray.empty)
      | .ok (.revert g' out) => (a, createdAccounts, σ, g', AStar, false, out)
      | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
          let c := GasConstants.Gcodedeposit * returnedData.size
          let F : Bool := Id.run do
            let F₀ : Bool :=
              match σ.find? a with
              | .some ac => ac.code ≠ ByteArray.empty ∨ ac.nonce ≠ (⟨0⟩ : UInt256)
              | .none => false
            let F₂ : Bool := gStarStar.toNat < c
            let MAX_CODE_SIZE := 24576
            let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
            let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
            pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)
          let σ' : AccountMap :=
            if F then σ else
              let newAccount' := σStarStar.findD a default
              σStarStar.insert a {newAccount' with code := returnedData}
          let g' := if F then 0 else gStarStar.toNat - c
          let A' := if F then AStar else AStarStar
          let z := not F
          (a, createdAccounts', σ', .ofNat g', A', z, ByteArray.empty)).2.2.2.2.2.2.size <
      UInt256.size := by
  have hle := Lambda_Xi_tuple_match_output_size_le_maxReturnDataSizeByGas
    a createdAccounts genesisBlockHeader blocks σ σStar σ₀ g AStar I
  exact Nat.lt_of_le_of_lt hle maxReturnDataSizeByGas_lt_uint256

lemma lambda_projection_output_size_le_maxReturnDataSizeByGas
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress)
    (g p v : UInt256) (i : ByteArray) (e : Fin 1025) (ζ : Option ByteArray)
    (H : BlockHeader) (w : Bool) :
    (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
      s o g p v i e ζ H w).2.2.2.2.2.2.size ≤ maxReturnDataSizeByGas := by
  let n : UInt256 := (σ.find? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩
  let lₐ := Lambda.L_A s n ζ i
  let a : AccountAddress := (ffi.KEC lₐ).extract 12 32 |> fromByteArrayBigEndian |> Fin.ofNat _
  let AStar := A.addAccessedAccount a
  let existentAccount := σ.findD a default
  let collision : ByteArray × Batteries.RBSet AccountAddress compare :=
    if existentAccount.nonce ≠ ⟨0⟩ || existentAccount.code.size ≠ 0 ||
        existentAccount.storage != default then
      (⟨#[0xfe]⟩, createdAccounts)
    else
      (i, createdAccounts.insert a)
  let initCode := collision.1
  let createdAccountsStar := collision.2
  let newAccount : Account :=
    { existentAccount with
      nonce := existentAccount.nonce + ⟨1⟩
      balance := v + existentAccount.balance }
  let σStar :=
    match σ.find? s with
    | none => σ
    | some ac => σ.insert s {ac with balance := ac.balance - v} |>.insert a newAccount
  let exEnv : ExecutionEnv :=
    { codeOwner := a, sender := o, source := s, weiValue := v, calldata := default,
      code := initCode, gasPrice := p.toNat, header := H, depth := e, perm := w,
      blobVersionedHashes := blobVersionedHashes }
  unfold Lambda
  simp only
  exact (by
    simpa only [n, lₐ, a, AStar, existentAccount, collision, initCode, createdAccountsStar,
      newAccount, σStar, exEnv] using
      (Lambda_Xi_tuple_match_output_size_le_maxReturnDataSizeByGas a createdAccountsStar genesisBlockHeader blocks
        σ σStar σ₀ g AStar exEnv))

lemma lambda_projection_output_size_lt_uint256
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress)
    (g p v : UInt256) (i : ByteArray) (e : Fin 1025) (ζ : Option ByteArray)
    (H : BlockHeader) (w : Bool) :
    (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
      s o g p v i e ζ H w).2.2.2.2.2.2.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (lambda_projection_output_size_le_maxReturnDataSizeByGas blobVersionedHashes
      createdAccounts genesisBlockHeader blocks σ σ₀ A s o g p v i e ζ H w)
    maxReturnDataSizeByGas_lt_uint256

lemma lambda_output_size_eq_zero_of_success
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o : AccountAddress}
    {g p v : UInt256} {i : ByteArray} {e : Fin 1025} {ζ : Option ByteArray}
    {H : BlockHeader} {w : Bool}
    {a : AccountAddress} {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {out : ByteArray}
    (h : Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w = (a, createdAccounts', σ', g', A', true, out)) :
    out.size = 0 := by
  unfold Lambda at h
  simp only at h
  split at h
  · simp at h
  · simp at h
  · simp at h
    rcases h with ⟨_, _, _, _, _, _hz, hout⟩
    cases hout
    rfl

lemma lambda_output_size_le_zero_of_success
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o : AccountAddress}
    {g p v : UInt256} {i : ByteArray} {e : Fin 1025} {ζ : Option ByteArray}
    {H : BlockHeader} {w : Bool}
    {a : AccountAddress} {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {out : ByteArray}
    (h : Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w = (a, createdAccounts', σ', g', A', true, out)) :
    out.size ≤ 0 := by
  exact Nat.le_of_eq (lambda_output_size_eq_zero_of_success h)

lemma lambda_projection_output_size_eq_zero_of_success
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress)
    (g p v : UInt256) (i : ByteArray) (e : Fin 1025) (ζ : Option ByteArray)
    (H : BlockHeader) (w : Bool)
    (hz :
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w).2.2.2.2.2.1 = true) :
    (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
      s o g p v i e ζ H w).2.2.2.2.2.2.size = 0 := by
  exact lambda_output_size_eq_zero_of_success
    (a :=
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w).1)
    (createdAccounts' :=
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w).2.1)
    (σ' :=
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w).2.2.1)
    (g' :=
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w).2.2.2.1)
    (A' :=
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w).2.2.2.2.1)
    (out :=
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w).2.2.2.2.2.2)
    (by
      rw [← hz])

lemma lambda_output_size_le_maxReturnDataSizeByGas
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o : AccountAddress}
    {g p v : UInt256} {i : ByteArray} {e : Fin 1025} {ζ : Option ByteArray}
    {H : BlockHeader} {w : Bool}
    {a : AccountAddress} {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (h : Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w = (a, createdAccounts', σ', g', A', z, out)) :
    out.size ≤ maxReturnDataSizeByGas := by
  by_cases hz : z = true
  · subst z
    exact Nat.le_trans (lambda_output_size_le_zero_of_success h) (Nat.zero_le _)
  have hout : out =
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w).2.2.2.2.2.2 := by
    have hp := congrArg (fun x => x.2.2.2.2.2.2) h
    simpa using hp.symm
  rw [hout]
  exact lambda_projection_output_size_le_maxReturnDataSizeByGas blobVersionedHashes createdAccounts
    genesisBlockHeader blocks σ σ₀ A s o g p v i e ζ H w

lemma lambda_output_size_lt_uint256
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o : AccountAddress}
    {g p v : UInt256} {i : ByteArray} {e : Fin 1025} {ζ : Option ByteArray}
    {H : BlockHeader} {w : Bool}
    {a : AccountAddress} {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (h : Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w = (a, createdAccounts', σ', g', A', z, out)) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (lambda_output_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

lemma theta_code_projection_output_size_le_maxReturnDataSizeByGas
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (code d : ByteArray) (g p v v' : UInt256) (e : Fin 1025)
    (H : BlockHeader) (w : Bool) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (ToExecute.Code code) g p v v' d e H w).2.2.2.2.2.size ≤
      maxReturnDataSizeByGas := by
  let σ'₁ :=
    match σ.find? r with
      | none =>
        if v != UInt256.ofNat 0 then
          σ.insert r { (default : Account) with balance := v}
        else
          σ
      | some acc =>
        σ.insert r { acc with balance := acc.balance + v}
  let σ₁ :=
    match σ'₁.find? s with
      | none => σ'₁
      | some acc =>
        σ'₁.insert s { acc with balance := acc.balance - v}
  let I : ExecutionEnv :=
    { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
      source := s, weiValue := v', depth := e, perm := w, code := code,
      header := H, blobVersionedHashes := blobVersionedHashes }
  unfold Θ
  simp only
  exact (by
    simpa only [σ'₁, σ₁, I] using
      (Xi_tuple_match_output_size_le_maxReturnDataSizeByGas createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I))

lemma theta_code_projection_output_size_lt_uint256
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (code d : ByteArray) (g p v v' : UInt256) (e : Fin 1025)
    (H : BlockHeader) (w : Bool) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (ToExecute.Code code) g p v v' d e H w).2.2.2.2.2.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (theta_code_projection_output_size_le_maxReturnDataSizeByGas
      blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
      code d g p v v' e H w)
    maxReturnDataSizeByGas_lt_uint256

lemma theta_code_output_size_le_maxReturnDataSizeByGas
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {code d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (h : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (ToExecute.Code code) g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out)) :
    out.size ≤ maxReturnDataSizeByGas := by
  have hout : out =
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (ToExecute.Code code) g p v v' d e H w).2.2.2.2.2 := by
    have hp := congrArg (fun x => x.2.2.2.2.2) h
    simpa using hp.symm
  rw [hout]
  exact theta_code_projection_output_size_le_maxReturnDataSizeByGas
    blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
    code d g p v v' e H w

lemma theta_code_output_size_lt_uint256
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {code d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (h : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (ToExecute.Code code) g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out)) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (theta_code_output_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

lemma theta_toExecute_nonprecompile_output_size_le_maxReturnDataSizeByGas
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (hnot : r ∉ π)
    (h : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (toExecute σ r) g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out)) :
    out.size ≤ maxReturnDataSizeByGas := by
  unfold toExecute at h
  simp [hnot] at h
  cases hfind : σ.find? r with
  | none =>
      simp [hfind] at h
      exact theta_code_output_size_le_maxReturnDataSizeByGas h
  | some acc =>
      simp [hfind] at h
      exact theta_code_output_size_le_maxReturnDataSizeByGas h

lemma theta_toExecute_nonprecompile_output_size_lt_uint256
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (hnot : r ∉ π)
    (h : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (toExecute σ r) g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out)) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (theta_toExecute_nonprecompile_output_size_le_maxReturnDataSizeByGas hnot h)
    maxReturnDataSizeByGas_lt_uint256

/--
Return-data bounds for precompiles.

The `Θ` precompile branch is proved below by case-splitting over the concrete dispatcher.  The
only remaining assumptions in this file are at true external boundaries:

* `ffi.sha256` and `ffi.BLAKE2Compress` are Lean `opaque` externs implemented in `Ethereum/FFI`.
* `blobRIP160`, `blobBN_ADD`, `blobBN_MUL`, `blobSNARKV`, and `blobPointEval` run Python
  processes through `totallySafePerformIO`.

All Lean-visible wrapper logic is proved locally.  In particular, `EXPMOD` is proved from its
Lean implementation and the Python-backed wrappers are reduced through `ByteArray.ofBlob_ok_size`
to assumptions about the external hex blob chunk count.
-/
lemma expModAux_lt {m : Nat} (hm : 0 < m) :
    ∀ n a c, expModAux m a c n < m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a c
      cases n with
      | zero =>
          simp [expModAux]
          exact Nat.mod_lt a hm
      | succ k =>
          unfold expModAux
          split
          · apply ih (k.succ / 2)
            exact Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)
          · apply ih (k.succ / 2)
            exact Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)

lemma expMod_lt {m : Nat} (hm : 0 < m) (b : UInt256) (n : Nat) :
    expMod m b n < m := by
  unfold expMod
  exact expModAux_lt hm n 1 b.toNat

private def expmodVariableCost (data : ByteArray) : Nat :=
  let base_length := nat_of_slice data 0 32
  let exp_length := nat_of_slice data 32 32
  let modulus_length := nat_of_slice data 64 32
  let exp := fun () => nat_of_slice data (96 + base_length) exp_length
  let multiplication_complexity := fun x y : Nat => ((max x y + 7) / 8) ^ 2
  let adjusted_exp_length :=
    if exp_length ≤ 32 ∧ exp () = 0 then
      0
    else if exp_length ≤ 32 then
      Nat.log 2 (exp ())
    else
      let length_part := 8 * (exp_length - 32)
      let bits_part :=
        let exp_head := nat_of_slice data (96 + base_length) 32
        if 32 < exp_length ∧ exp_head ≠ 0 then
          Nat.log 2 exp_head
        else
          0
      length_part + bits_part
  let iterations := max adjusted_exp_length 1
  multiplication_complexity base_length modulus_length * iterations / 3

private def expmodGasCost (data : ByteArray) : Nat :=
  max 200 (expmodVariableCost data)

lemma BE_expMod_size_le_modulus_length
    (data : ByteArray) (base_length exp_length modulus_length : Nat)
    (hmod :
      0 < nat_of_slice data (96 + base_length + exp_length) modulus_length) :
    (BE (expMod (nat_of_slice data (96 + base_length + exp_length) modulus_length)
      (.ofNat (nat_of_slice data 96 base_length))
      (nat_of_slice data (96 + base_length) exp_length))).size ≤ modulus_length := by
  have hmodlt := nat_of_slice_lt data (96 + base_length + exp_length) modulus_length
  exact BE_le (Nat.lt_trans
    (expMod_lt hmod (.ofNat (nat_of_slice data 96 base_length))
      (nat_of_slice data (96 + base_length) exp_length))
    hmodlt)

private lemma EXPMOD_modulus_length_le_maxReturnDataSizeByGas_of_cost_lt
    (base_length modulus_length iterations : Nat)
    (hiterations : 1 ≤ iterations)
    (hcost :
      ((max base_length modulus_length + 7) / 8) ^ 2 * iterations / 3 <
        UInt256.size) :
    modulus_length ≤ maxReturnDataSizeByGas := by
  by_contra hle
  have hm : maxReturnDataSizeByGas + 1 ≤ modulus_length := Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)
  let k := (maxReturnDataSizeByGas + 8) / 8
  have hkbound : UInt256.size ≤ k ^ 2 / 3 := by
    decide
  have hkarg : maxReturnDataSizeByGas + 8 ≤ max base_length modulus_length + 7 := by
    have hmodle : modulus_length ≤ max base_length modulus_length := le_max_right _ _
    omega
  have hk :
      k ≤ (max base_length modulus_length + 7) / 8 := by
    exact Nat.div_le_div_right hkarg
  have hksq :
      k ^ 2 ≤ ((max base_length modulus_length + 7) / 8) ^ 2 := by
    exact Nat.pow_le_pow_left hk 2
  have hiter :
      ((max base_length modulus_length + 7) / 8) ^ 2 ≤
        ((max base_length modulus_length + 7) / 8) ^ 2 * iterations := by
    exact Nat.le_mul_of_pos_right _ (Nat.succ_le_iff.mp hiterations)
  have hdiv :
      k ^ 2 / 3 ≤
        ((max base_length modulus_length + 7) / 8) ^ 2 * iterations / 3 := by
    exact Nat.div_le_div_right (Nat.le_trans hksq hiter)
  omega

private lemma EXPMOD_modulus_length_le_maxReturnDataSizeByGas_of_gas
    (data : ByteArray) (g : UInt256)
    (hgas : ¬ (g.toNat < 200 ∨ g.toNat < expmodVariableCost data)) :
    nat_of_slice data 64 32 ≤ maxReturnDataSizeByGas := by
  let base_length := nat_of_slice data 0 32
  let exp_length := nat_of_slice data 32 32
  let modulus_length := nat_of_slice data 64 32
  let exp := fun () => nat_of_slice data (96 + base_length) exp_length
  let multiplication_complexity := fun x y : Nat => ((max x y + 7) / 8) ^ 2
  let adjusted_exp_length :=
    if exp_length ≤ 32 && exp () == 0 then
      0
    else if exp_length ≤ 32 then
      Nat.log 2 (exp ())
    else
      let length_part := 8 * (exp_length - 32)
      let bits_part :=
        let exp_head := nat_of_slice data (96 + base_length) 32
        if 32 < exp_length ∧ exp_head != 0 then
          Nat.log 2 exp_head
        else
          0
      length_part + bits_part
  let iterations := max adjusted_exp_length 1
  let cost := multiplication_complexity base_length modulus_length * iterations / 3
  have hcost_le_g :
      cost ≤ g.toNat := by
    apply Nat.le_of_not_gt
    intro hcost
    apply hgas
    right
    simpa [base_length, exp_length, modulus_length, exp, multiplication_complexity,
      adjusted_exp_length, iterations, cost, expmodVariableCost] using hcost
  have hcost_lt : cost < UInt256.size :=
    Nat.lt_of_le_of_lt hcost_le_g g.val.isLt
  have hiterations : 1 ≤ iterations := by
    exact le_max_right adjusted_exp_length 1
  exact EXPMOD_modulus_length_le_maxReturnDataSizeByGas_of_cost_lt
    base_length modulus_length iterations hiterations hcost_lt

lemma precompile_EXPMOD_output_size_le_modulus_length
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_EXPMOD σ g A I).2.2.2.size ≤ nat_of_slice I.calldata 64 32 := by
  by_cases hgas : g.toNat < 200 ∨ g.toNat < expmodVariableCost I.calldata
  ·
    have hgasImpl := hgas
    simp only [expmodVariableCost] at hgasImpl
    simp [Ξ_EXPMOD, hgasImpl]
  ·
    have hgasImpl := hgas
    simp only [expmodVariableCost] at hgasImpl
    let data := I.calldata
    let base_length := nat_of_slice data 0 32
    let exp_length := nat_of_slice data 32 32
    let modulus_length := nat_of_slice data 64 32
    let modulus := nat_of_slice data (96 + base_length + exp_length) modulus_length
    by_cases hzero : modulus_length == 0 || modulus == 0
    · simp [Ξ_EXPMOD, hgasImpl, data, base_length, exp_length,
        modulus_length, modulus, hzero,
        ByteArray_zeroes_size]
    ·
      have hmod_ne : modulus ≠ 0 := by
        intro hz
        apply hzero
        simp [hz]
      have hmod_pos : 0 < modulus := Nat.pos_of_ne_zero hmod_ne
      have hbase_size :
          (BE (expMod modulus (.ofNat (nat_of_slice data 96 base_length))
            (nat_of_slice data (96 + base_length) exp_length))).size ≤ modulus_length := by
        simpa [data, base_length, exp_length, modulus_length, modulus] using
          BE_expMod_size_le_modulus_length data base_length exp_length modulus_length hmod_pos
      by_cases hpad :
          modulus_length ≥
            (BE (expMod modulus (.ofNat (nat_of_slice data 96 base_length))
              (nat_of_slice data (96 + base_length) exp_length))).size
      · simp [Ξ_EXPMOD, hgasImpl, data, base_length, exp_length,
          modulus_length, modulus, hzero, hpad]
        rw [ByteArray_zeroes_size]
        have hzero_size :
            ((OfNat.ofNat modulus_length : USize) -
              (OfNat.ofNat
                (BE (expMod modulus (.ofNat (nat_of_slice data 96 base_length))
                  (nat_of_slice data (96 + base_length) exp_length))).size : USize)).toNat ≤
              modulus_length -
                (BE (expMod modulus (.ofNat (nat_of_slice data 96 base_length))
                  (nat_of_slice data (96 + base_length) exp_length))).size :=
          USize.toNat_ofBitVec_sub_ofNat_le hbase_size
        have hzero_size' :
            ((OfNat.ofNat (nat_of_slice I.calldata 64 32) : USize) -
              (OfNat.ofNat
                (BE (expMod
                  (nat_of_slice I.calldata
                    (96 + nat_of_slice I.calldata 0 32 + nat_of_slice I.calldata 32 32)
                    (nat_of_slice I.calldata 64 32))
                  (.ofNat (nat_of_slice I.calldata 96 (nat_of_slice I.calldata 0 32)))
                  (nat_of_slice I.calldata (96 + nat_of_slice I.calldata 0 32)
                    (nat_of_slice I.calldata 32 32)))).size : USize)).toNat ≤
              nat_of_slice I.calldata 64 32 -
                (BE (expMod
                  (nat_of_slice I.calldata
                    (96 + nat_of_slice I.calldata 0 32 + nat_of_slice I.calldata 32 32)
                    (nat_of_slice I.calldata 64 32))
                  (.ofNat (nat_of_slice I.calldata 96 (nat_of_slice I.calldata 0 32)))
                  (nat_of_slice I.calldata (96 + nat_of_slice I.calldata 0 32)
                    (nat_of_slice I.calldata 32 32)))).size := by
          simpa [data, base_length, exp_length, modulus_length, modulus] using hzero_size
        have hbase_size' :
            (BE (expMod
              (nat_of_slice I.calldata
                (96 + nat_of_slice I.calldata 0 32 + nat_of_slice I.calldata 32 32)
                (nat_of_slice I.calldata 64 32))
              (.ofNat (nat_of_slice I.calldata 96 (nat_of_slice I.calldata 0 32)))
              (nat_of_slice I.calldata (96 + nat_of_slice I.calldata 0 32)
                (nat_of_slice I.calldata 32 32)))).size ≤
              nat_of_slice I.calldata 64 32 := by
          simpa [data, base_length, exp_length, modulus_length, modulus] using hbase_size
        omega
      · rw [Ξ_EXPMOD]
        rw [if_neg (by
          intro hg
          apply hgas
          simpa [expmodVariableCost] using hg)]
        simp only [data, base_length, exp_length, modulus_length, modulus, hzero, hpad]
        simpa [data, base_length, exp_length, modulus_length, modulus] using hbase_size

private def thetaValueTransferAccountMap
    (σ : AccountMap) (s r : AccountAddress) (v : UInt256) : AccountMap :=
  let σ'₁ :=
    match σ.find? r with
    | none =>
        if v != UInt256.ofNat 0 then
          σ.insert r { (default : Account) with balance := v}
        else
          σ
    | some acc =>
        σ.insert r { acc with balance := acc.balance + v}
  match σ'₁.find? s with
  | none => σ'₁
  | some acc =>
      σ'₁.insert s { acc with balance := acc.balance - v}

private def precompileDispatchResult
    (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
  match pc with
  | 1 => (∅, Ξ_ECREC σ g A I)
  | 2 => (∅, Ξ_SHA256 σ g A I)
  | 3 => (∅, Ξ_RIP160 σ g A I)
  | 4 => (∅, Ξ_ID σ g A I)
  | 5 => (∅, Ξ_EXPMOD σ g A I)
  | 6 => (∅, Ξ_BN_ADD σ g A I)
  | 7 => (∅, Ξ_BN_MUL σ g A I)
  | 8 => (∅, Ξ_SNARKV σ g A I)
  | 9 => (∅, Ξ_BLAKE2_F σ g A I)
  | 10 => (∅, Ξ_PointEval σ g A I)
  | _ => default

lemma precompile_ECREC_output_size_le_maxReturnDataSizeByGas_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_ECREC σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size := by
  have h12 : (OfNat.ofNat 12 : USize).toNat = 12 := by
    apply USize.toNat_ofNat_of_le_of_lt (n := 12) (i := 12)
    · rcases System.Platform.numBits_eq with h | h <;> rw [USize.size, h] <;> norm_num
    · rfl
  unfold Ξ_ECREC
  by_cases hgas : g.toNat < 3000
  · simp [hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [hgas]
    left
    split
    · simp [maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    · split
      · simp [ByteArray.size_append, ByteArray_zeroes_size, ByteArray.size_extract,
          maxReturnDataSizeByGas, maxReturnDataWordsByGas]
        omega
      · simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

private lemma List.mapM_loop_ok_length {α β : Type} (f : α → Except String β) :
    ∀ (xs : List α) (acc ys : List β),
      List.mapM.loop f xs acc = .ok ys → ys.length = acc.length + xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro acc ys h
      simp [List.mapM.loop] at h
      cases h
      simp
  | cons x xs ih =>
      intro acc ys h
      simp [List.mapM.loop, bind, Except.bind] at h
      cases hx : f x with
      | error e => simp [hx] at h
      | ok y =>
          simp [hx] at h
          have hlen := ih (y :: acc) ys h
          simp at hlen ⊢
          omega

private lemma List.mapM_ok_length {α β : Type} (f : α → Except String β)
    {xs : List α} {ys : List β} :
    xs.mapM f = .ok ys → ys.length = xs.length := by
  intro h
  have hlen := List.mapM_loop_ok_length f xs [] ys h
  simpa using hlen

lemma ByteArray.ofBlob_ok_size {blob : Blob} {s : ByteArray}
    (h : ByteArray.ofBlob blob = .ok s) :
    s.size = (blob.toList.toChunks 2).length := by
  unfold ByteArray.ofBlob at h
  simp [bind, Except.bind, pure, Except.pure] at h
  cases hmap : (blob.toList.toChunks 2).mapM ofHex? with
  | error e => simp [hmap] at h
  | ok chunks =>
      simp [hmap] at h
      cases h
      have hlen := List.mapM_ok_length (f := ofHex?) hmap
      simp [ByteArray.size]
      exact hlen

axiom ffi_sha256_output_size (d : ByteArray) (len : USize) :
    (ffi.sha256 d len).size = 32

lemma precompile_SHA256_output_size_le_maxReturnDataSizeByGas_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_SHA256 σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size := by
  unfold Ξ_SHA256 ffi.SHA256
  simp [pure, Except.pure]
  split
  · simp [maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [ffi_sha256_output_size, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

axiom blobRIP160_output_chunks (d : ByteArray) :
    ((blobRIP160 (toHex d)).toList.toChunks 2).length = 20

lemma RIP160_ok_output_size {d s : ByteArray} :
    RIP160 d = .ok s → s.size = 20 := by
  intro h
  unfold RIP160 at h
  rw [ByteArray.ofBlob_ok_size h]
  exact blobRIP160_output_chunks d

lemma precompile_RIP160_output_size_le_maxReturnDataSizeByGas_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_RIP160 σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size := by
  by_cases hgas : g.toNat < 600 + 120 * ((I.calldata.size + 31) / 32)
  · simp [Ξ_RIP160, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_RIP160, hgas]
    cases hres : RIP160 I.calldata with
    | ok s =>
        have hs := RIP160_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

lemma precompile_ID_output_size_le_maxReturnDataSizeByGas_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_ID σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size := by
  by_cases hgas : g.toNat <
      (let l := I.calldata.size
       let ceil := (l + 31) / 32
       15 + 3 * ceil)
  · simp [Ξ_ID, hgas, maxReturnDataSizeByGas]
  · exact Nat.le_trans (by simp [Ξ_ID, hgas]) (le_max_right _ _)

lemma precompile_EXPMOD_output_size_le_maxReturnDataSizeByGas_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_EXPMOD σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size := by
  by_cases hgas : g.toNat < 200 ∨ g.toNat < expmodVariableCost I.calldata
  ·
    have hgasImpl := hgas
    simp only [expmodVariableCost] at hgasImpl
    simp [Ξ_EXPMOD, hgasImpl, maxReturnDataSizeByGas]
  ·
    have hmod :
        nat_of_slice I.calldata 64 32 ≤ maxReturnDataSizeByGas :=
      EXPMOD_modulus_length_le_maxReturnDataSizeByGas_of_gas I.calldata g hgas
    have hout :
        (Ξ_EXPMOD σ g A I).2.2.2.size ≤ nat_of_slice I.calldata 64 32 :=
      precompile_EXPMOD_output_size_le_modulus_length
    exact Nat.le_trans hout (Nat.le_trans hmod (le_max_left _ _))

axiom blobBN_ADD_output_chunks {x₀ y₀ x₁ y₁ : ByteArray}
    (h : blobBN_ADD (toHex x₀) (toHex y₀) (toHex x₁) (toHex y₁) ≠ "error") :
    ((blobBN_ADD (toHex x₀) (toHex y₀) (toHex x₁) (toHex y₁)).toList.toChunks 2).length = 64

lemma BN_ADD_ok_output_size {x₀ y₀ x₁ y₁ s : ByteArray} :
    BN_ADD x₀ y₀ x₁ y₁ = .ok s → s.size = 64 := by
  intro h
  unfold BN_ADD at h
  split at h
  · simp at h
  · rename_i hblob
    rw [ByteArray.ofBlob_ok_size h]
    exact blobBN_ADD_output_chunks hblob

lemma precompile_BN_ADD_output_size_le_maxReturnDataSizeByGas_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_BN_ADD σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size := by
  by_cases hgas : g.toNat < 150
  · simp [Ξ_BN_ADD, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_BN_ADD, hgas]
    cases hres : BN_ADD (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) (I.calldata.readBytes 96 32) with
    | ok s =>
        have hs := BN_ADD_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

axiom blobBN_MUL_output_chunks {x₀ y₀ n : ByteArray}
    (h : blobBN_MUL (toHex x₀) (toHex y₀) (toHex n) ≠ "error") :
    ((blobBN_MUL (toHex x₀) (toHex y₀) (toHex n)).toList.toChunks 2).length = 64

lemma BN_MUL_ok_output_size {x₀ y₀ n s : ByteArray} :
    BN_MUL x₀ y₀ n = .ok s → s.size = 64 := by
  intro h
  unfold BN_MUL at h
  split at h
  · simp at h
  · rename_i hblob
    rw [ByteArray.ofBlob_ok_size h]
    exact blobBN_MUL_output_chunks hblob

lemma precompile_BN_MUL_output_size_le_maxReturnDataSizeByGas_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_BN_MUL σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size := by
  by_cases hgas : g.toNat < 6000
  · simp [Ξ_BN_MUL, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_BN_MUL, hgas]
    cases hres : BN_MUL (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) with
    | ok s =>
        have hs := BN_MUL_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

axiom blobSNARKV_output_chunks {d : ByteArray}
    (h : blobSNARKV (toHex d) ≠ "error") :
    ((blobSNARKV (toHex d)).toList.toChunks 2).length = 32

lemma SNARKV_ok_output_size {d s : ByteArray} :
    SNARKV d = .ok s → s.size = 32 := by
  intro h
  unfold SNARKV at h
  split at h
  · simp at h
  · rename_i hblob
    rw [ByteArray.ofBlob_ok_size h]
    exact blobSNARKV_output_chunks hblob

lemma precompile_SNARKV_output_size_le_maxReturnDataSizeByGas_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_SNARKV σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size := by
  by_cases hgas : g.toNat < 34000 * (I.calldata.size / 192) + 45000
  · simp [Ξ_SNARKV, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_SNARKV, hgas]
    cases hres : SNARKV I.calldata with
    | ok s =>
        have hs := SNARKV_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

axiom ffi_BLAKE2Compress_output_size (d : ByteArray) :
    (ffi.BLAKE2Compress d).size = 64

lemma ffi_BLAKE2_ok_output_size {d s : ByteArray} :
    ffi.BLAKE2 d = .ok s → s.size = 64 := by
  intro h
  unfold ffi.BLAKE2 at h
  by_cases hsize : d.size != 213
  · simp [hsize, bind, Except.bind] at h
  · by_cases hflag : ¬d[212]! = 0 ∧ ¬d[212]! = 1
    · simp [hsize, hflag, pure, Except.pure, bind, Except.bind] at h
    · simp [hsize, hflag, pure, Except.pure, bind, Except.bind] at h
      cases h
      exact ffi_BLAKE2Compress_output_size d

lemma precompile_BLAKE2_F_output_size_le_maxReturnDataSizeByGas_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_BLAKE2_F σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size := by
  by_cases hgas : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)
  · simp [Ξ_BLAKE2_F, hgas, dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_BLAKE2_F, hgas]
    cases hres : ffi.BLAKE2 I.calldata with
    | ok s =>
        have hs := ffi_BLAKE2_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

axiom blobPointEval_output_chunks {d : ByteArray}
    (h : blobPointEval (toHex d) ≠ "error") :
    ((blobPointEval (toHex d)).toList.toChunks 2).length = 64

lemma PointEval_ok_output_size {d s : ByteArray} :
    PointEval d = .ok s → s.size = 64 := by
  intro h
  unfold PointEval at h
  split at h
  · simp at h
  · rename_i hblob
    rw [ByteArray.ofBlob_ok_size h]
    exact blobPointEval_output_chunks hblob

lemma precompile_PointEval_output_size_le_maxReturnDataSizeByGas_or_calldata
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} :
    (Ξ_PointEval σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size := by
  by_cases hgas : g.toNat < 50000
  · simp [Ξ_PointEval, hgas, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
  · simp [Ξ_PointEval, hgas]
    cases hres : PointEval I.calldata with
    | ok s =>
        have hs := PointEval_ok_output_size hres
        simp [hs, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
    | error e =>
        simp [dbgTrace, maxReturnDataSizeByGas, maxReturnDataWordsByGas]

lemma precompile_dispatch_output_size_le_maxReturnDataSizeByGas_or_calldata
    (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (precompileDispatchResult pc σ g A I).2.2.2.2.size ≤
      max maxReturnDataSizeByGas I.calldata.size := by
  by_cases h1 : pc = 1
  · subst pc
    change (Ξ_ECREC σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size
    exact precompile_ECREC_output_size_le_maxReturnDataSizeByGas_or_calldata
  · by_cases h2 : pc = 2
    · subst pc
      change (Ξ_SHA256 σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size
      exact precompile_SHA256_output_size_le_maxReturnDataSizeByGas_or_calldata
    · by_cases h3 : pc = 3
      · subst pc
        change (Ξ_RIP160 σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size
        exact precompile_RIP160_output_size_le_maxReturnDataSizeByGas_or_calldata
      · by_cases h4 : pc = 4
        · subst pc
          change (Ξ_ID σ g A I).2.2.2.size ≤ max maxReturnDataSizeByGas I.calldata.size
          exact precompile_ID_output_size_le_maxReturnDataSizeByGas_or_calldata
        · by_cases h5 : pc = 5
          · subst pc
            change (Ξ_EXPMOD σ g A I).2.2.2.size ≤
              max maxReturnDataSizeByGas I.calldata.size
            exact precompile_EXPMOD_output_size_le_maxReturnDataSizeByGas_or_calldata
          · by_cases h6 : pc = 6
            · subst pc
              change (Ξ_BN_ADD σ g A I).2.2.2.size ≤
                max maxReturnDataSizeByGas I.calldata.size
              exact precompile_BN_ADD_output_size_le_maxReturnDataSizeByGas_or_calldata
            · by_cases h7 : pc = 7
              · subst pc
                change (Ξ_BN_MUL σ g A I).2.2.2.size ≤
                  max maxReturnDataSizeByGas I.calldata.size
                exact precompile_BN_MUL_output_size_le_maxReturnDataSizeByGas_or_calldata
              · by_cases h8 : pc = 8
                · subst pc
                  change (Ξ_SNARKV σ g A I).2.2.2.size ≤
                    max maxReturnDataSizeByGas I.calldata.size
                  exact precompile_SNARKV_output_size_le_maxReturnDataSizeByGas_or_calldata
                · by_cases h9 : pc = 9
                  · subst pc
                    change (Ξ_BLAKE2_F σ g A I).2.2.2.size ≤
                      max maxReturnDataSizeByGas I.calldata.size
                    exact precompile_BLAKE2_F_output_size_le_maxReturnDataSizeByGas_or_calldata
                  · by_cases h10 : pc = 10
                    · subst pc
                      change (Ξ_PointEval σ g A I).2.2.2.size ≤
                        max maxReturnDataSizeByGas I.calldata.size
                      exact precompile_PointEval_output_size_le_maxReturnDataSizeByGas_or_calldata
                    · rw [precompileDispatchResult.eq_def]
                      repeat' split <;> (try contradiction)
                      · change (default : ByteArray).size ≤
                          max maxReturnDataSizeByGas I.calldata.size
                        simp [default, Inhabited.default, maxReturnDataSizeByGas]

private lemma theta_precompiled_output_eq
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r pc : AccountAddress)
    (d : ByteArray) (g p v v' : UInt256) (e : Fin 1025)
    (H : BlockHeader) (w : Bool) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w).2.2.2.2.2 =
      (let σ₁ := thetaValueTransferAccountMap σ s r v
       let I : ExecutionEnv :=
        { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
          code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
          blobVersionedHashes := blobVersionedHashes }
       let result := precompileDispatchResult pc σ₁ g A I
       result.2.2.2.2) := by
  unfold Θ thetaValueTransferAccountMap
  simp
  rfl

lemma theta_precompiled_output_size_le_maxReturnDataSizeByGas_or_calldata
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r pc : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray} :
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (ToExecute.Precompiled pc) g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out) →
    out.size ≤ max maxReturnDataSizeByGas d.size := by
  intro h
  have hout := congrArg
    (fun x : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 ×
        Substate × Bool × ByteArray => x.2.2.2.2.2) h
  change ((fun x : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 ×
      Substate × Bool × ByteArray => x.2.2.2.2.2)
        (createdAccounts', σ', g', A', z, out)).size ≤
    max maxReturnDataSizeByGas d.size
  rw [← congrArg ByteArray.size hout]
  change (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
      (ToExecute.Precompiled pc) g p v v' d e H w).2.2.2.2.2.size ≤
    max maxReturnDataSizeByGas d.size
  rw [theta_precompiled_output_eq blobVersionedHashes createdAccounts genesisBlockHeader
    blocks σ σ₀ A s o r pc d g p v v' e H w]
  let I : ExecutionEnv :=
    { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
      code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
      blobVersionedHashes := blobVersionedHashes }
  have hdispatch := precompile_dispatch_output_size_le_maxReturnDataSizeByGas_or_calldata pc
    (thetaValueTransferAccountMap σ s r v) g A I
  simpa [I] using hdispatch

lemma theta_precompiled_output_size_le_maxReturnDataSizeByGas
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r pc : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray} :
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (ToExecute.Precompiled pc) g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out) →
    d.size ≤ maxReturnDataSizeByGas →
    out.size ≤ maxReturnDataSizeByGas := by
  intro h hd
  exact Nat.le_trans
    (theta_precompiled_output_size_le_maxReturnDataSizeByGas_or_calldata h)
    (max_le le_rfl hd)

lemma theta_precompiled_output_size_lt_uint256
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r pc : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray} :
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (ToExecute.Precompiled pc) g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out) →
    d.size < UInt256.size →
    out.size < UInt256.size := by
  intro h hd
  exact Nat.lt_of_le_of_lt
    (theta_precompiled_output_size_le_maxReturnDataSizeByGas_or_calldata h)
    (max_lt maxReturnDataSizeByGas_lt_uint256 hd)

lemma theta_output_size_le_maxReturnDataSizeByGas_or_calldata
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {c : ToExecute} {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (h : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out)) :
    out.size ≤ max maxReturnDataSizeByGas d.size := by
  cases c with
  | Code code =>
      exact Nat.le_trans
        (theta_code_output_size_le_maxReturnDataSizeByGas h)
        (le_max_left _ _)
  | Precompiled pc =>
      exact theta_precompiled_output_size_le_maxReturnDataSizeByGas_or_calldata h

lemma theta_output_size_le_maxReturnDataSizeByGas
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {c : ToExecute} {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (h : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out))
    (hd : d.size ≤ maxReturnDataSizeByGas) :
    out.size ≤ maxReturnDataSizeByGas := by
  cases c with
  | Code code =>
      exact theta_code_output_size_le_maxReturnDataSizeByGas h
  | Precompiled pc =>
      exact theta_precompiled_output_size_le_maxReturnDataSizeByGas h hd

lemma theta_output_size_lt_uint256
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {c : ToExecute} {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (h : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out))
    (hd : d.size < UInt256.size) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (theta_output_size_le_maxReturnDataSizeByGas_or_calldata h)
    (max_lt maxReturnDataSizeByGas_lt_uint256 hd)

lemma theta_toExecute_output_size_le_maxReturnDataSizeByGas
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (h : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (toExecute σ r) g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out))
    (hd : d.size ≤ maxReturnDataSizeByGas) :
    out.size ≤ maxReturnDataSizeByGas := by
  exact theta_output_size_le_maxReturnDataSizeByGas h hd

lemma theta_toExecute_output_size_lt_uint256
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {d : ByteArray} {g p v v' : UInt256} {e : Fin 1025}
    {H : BlockHeader} {w : Bool}
    {createdAccounts' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (h : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (toExecute σ r) g p v v' d e H w =
        (createdAccounts', σ', g', A', z, out))
    (hd : d.size < UInt256.size) :
    out.size < UInt256.size := by
  exact theta_output_size_lt_uint256 h hd

lemma theta_projection_output_size_le_maxReturnDataSizeByGas
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (c : ToExecute) (d : ByteArray) (g p v v' : UInt256) (e : Fin 1025)
    (H : BlockHeader) (w : Bool)
    (hd : d.size ≤ maxReturnDataSizeByGas) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.2.2.2.2.size ≤ maxReturnDataSizeByGas := by
  exact theta_output_size_le_maxReturnDataSizeByGas
    (createdAccounts' :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).1)
    (σ' :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.1)
    (g' :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.2.1)
    (A' :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.2.2.1)
    (z :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.2.2.2.1)
    (out :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.2.2.2.2)
    rfl hd

lemma theta_projection_output_size_lt_uint256
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (c : ToExecute) (d : ByteArray) (g p v v' : UInt256) (e : Fin 1025)
    (H : BlockHeader) (w : Bool)
    (hd : d.size < UInt256.size) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.2.2.2.2.size < UInt256.size := by
  exact theta_output_size_lt_uint256
    (createdAccounts' :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).1)
    (σ' :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.1)
    (g' :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.2.1)
    (A' :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.2.2.1)
    (z :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.2.2.2.1)
    (out :=
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        c g p v v' d e H w).2.2.2.2.2)
    rfl hd

lemma theta_toExecute_projection_output_size_le_maxReturnDataSizeByGas
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (d : ByteArray) (g p v v' : UInt256) (e : Fin 1025)
    (H : BlockHeader) (w : Bool)
    (hd : d.size ≤ maxReturnDataSizeByGas) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (toExecute σ r) g p v v' d e H w).2.2.2.2.2.size ≤
      maxReturnDataSizeByGas := by
  exact theta_projection_output_size_le_maxReturnDataSizeByGas blobVersionedHashes createdAccounts
    genesisBlockHeader blocks σ σ₀ A s o r (toExecute σ r) d g p v v' e H w hd

lemma theta_toExecute_projection_output_size_lt_uint256
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (d : ByteArray) (g p v v' : UInt256) (e : Fin 1025)
    (H : BlockHeader) (w : Bool)
    (hd : d.size < UInt256.size) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (toExecute σ r) g p v v' d e H w).2.2.2.2.2.size < UInt256.size := by
  exact theta_projection_output_size_lt_uint256 blobVersionedHashes createdAccounts
    genesisBlockHeader blocks σ σ₀ A s o r (toExecute σ r) d g p v v' e H w hd

set_option linter.unusedSimpArgs false in
lemma call_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {evmState state' : State} {x : UInt256}
    (hin :
      (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
      inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  unfold call at h
  simp [Id.run, bind, Except.bind, pure, Except.pure,
    Ethereum.State.addAccessedAccount, Ethereum.State.replaceStackAndIncrPC,
    Ethereum.State.incrPC] at h
  repeat split at h
  all_goals
    try contradiction
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp
    try
      simpa using
        (theta_projection_output_size_le_maxReturnDataSizeByGas
          blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
          evmState.blocks evmState.accountMap evmState.σ₀
          (evmState.substate.addAccessedAccount (AccountAddress.ofUInt256 t))
          (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
          (AccountAddress.ofUInt256 recipient)
          (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
          (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (.ofNat
            (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas
              evmState.accountMap evmState.machineState evmState.substate))
          (.ofNat evmState.executionEnv.gasPrice) value value'
          (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission
          hin)

set_option linter.unusedSimpArgs false in
lemma call_returnData_size_lt_uint256 {gasCost : Nat} {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {evmState state' : State} {x : UInt256}
    (hin :
      (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
      inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (call_returnData_size_le_maxReturnDataSizeByGas hin h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma step_call_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (hin : ∀ {stack : Stack UInt256}
      {gas target value inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop7 =
        some (stack, gas, target, value, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : step gasCost (Operation.CALL, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i liftPop popped hLift callResult vCall hCall
  rcases vCall with ⟨_, _⟩
  have hpop := option_liftM_eq_some hLift
  have hin' :
      (({ state with
        machineState.execLength := state.machineState.execLength + 1 }).machineState.memory.readWithPadding
          popped.2.2.2.2.1.toNat popped.2.2.2.2.2.1.toNat).size ≤
        maxReturnDataSizeByGas := by
    simpa using hin hpop
  have hout := call_returnData_size_le_maxReturnDataSizeByGas hin' hCall
  rw [← h]
  simpa using hout

set_option linter.unusedSimpArgs false in
lemma step_call_returnData_size_lt_uint256 {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (hin : ∀ {stack : Stack UInt256}
      {gas target value inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop7 =
        some (stack, gas, target, value, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : step gasCost (Operation.CALL, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_call_returnData_size_le_maxReturnDataSizeByGas hin h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma step_callcode_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (hin : ∀ {stack : Stack UInt256}
      {gas target value inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop7 =
        some (stack, gas, target, value, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : step gasCost (Operation.CALLCODE, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i liftPop popped hLift callResult vCall hCall
  rcases vCall with ⟨_, _⟩
  have hpop := option_liftM_eq_some hLift
  have hin' :
      (({ state with
        machineState.execLength := state.machineState.execLength + 1 }).machineState.memory.readWithPadding
          popped.2.2.2.2.1.toNat popped.2.2.2.2.2.1.toNat).size ≤
        maxReturnDataSizeByGas := by
    simpa using hin hpop
  have hout := call_returnData_size_le_maxReturnDataSizeByGas hin' hCall
  rw [← h]
  simpa using hout

set_option linter.unusedSimpArgs false in
lemma step_callcode_returnData_size_lt_uint256 {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (hin : ∀ {stack : Stack UInt256}
      {gas target value inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop7 =
        some (stack, gas, target, value, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : step gasCost (Operation.CALLCODE, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_callcode_returnData_size_le_maxReturnDataSizeByGas hin h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma step_delegatecall_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (hin : ∀ {stack : Stack UInt256}
      {gas target inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop6 =
        some (stack, gas, target, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : step gasCost (Operation.DELEGATECALL, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i liftPop popped hLift callResult vCall hCall
  rcases vCall with ⟨_, _⟩
  have hpop := option_liftM_eq_some hLift
  have hin' :
      (({ state with
        machineState.execLength := state.machineState.execLength + 1 }).machineState.memory.readWithPadding
          popped.2.2.2.1.toNat popped.2.2.2.2.1.toNat).size ≤
        maxReturnDataSizeByGas := by
    simpa using hin hpop
  have hout := call_returnData_size_le_maxReturnDataSizeByGas hin' hCall
  rw [← h]
  simpa using hout

set_option linter.unusedSimpArgs false in
lemma step_delegatecall_returnData_size_lt_uint256 {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (hin : ∀ {stack : Stack UInt256}
      {gas target inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop6 =
        some (stack, gas, target, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : step gasCost (Operation.DELEGATECALL, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_delegatecall_returnData_size_le_maxReturnDataSizeByGas hin h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma step_staticcall_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (hin : ∀ {stack : Stack UInt256}
      {gas target inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop6 =
        some (stack, gas, target, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : step gasCost (Operation.STATICCALL, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i liftPop popped hLift callResult vCall hCall
  rcases vCall with ⟨_, _⟩
  have hpop := option_liftM_eq_some hLift
  have hin' :
      (({ state with
        machineState.execLength := state.machineState.execLength + 1 }).machineState.memory.readWithPadding
          popped.2.2.2.1.toNat popped.2.2.2.2.1.toNat).size ≤
        maxReturnDataSizeByGas := by
    simpa using hin hpop
  have hout := call_returnData_size_le_maxReturnDataSizeByGas hin' hCall
  rw [← h]
  simpa using hout

set_option linter.unusedSimpArgs false in
lemma step_staticcall_returnData_size_lt_uint256 {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (hin : ∀ {stack : Stack UInt256}
      {gas target inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop6 =
        some (stack, gas, target, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : step gasCost (Operation.STATICCALL, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_staticcall_returnData_size_le_maxReturnDataSizeByGas hin h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma step_create_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.CREATE, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    rw [← h]
    simp
    try
      simpa using
        (lambda_projection_output_size_le_maxReturnDataSizeByGas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

set_option linter.unusedSimpArgs false in
lemma step_create_returnData_size_lt_uint256 {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.CREATE, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_create_returnData_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma step_create2_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.CREATE2, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    rw [← h]
    simp
    try
      simpa using
        (lambda_projection_output_size_le_maxReturnDataSizeByGas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

set_option linter.unusedSimpArgs false in
lemma step_create2_returnData_size_lt_uint256 {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.CREATE2, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_create2_returnData_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

lemma step_recursive_returnData_size_le_maxReturnDataSizeByGas {gasCost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)} {state state' : State}
    (hop : op ∈
      ([Operation.CALL, Operation.CALLCODE, Operation.DELEGATECALL, Operation.STATICCALL,
        Operation.CREATE, Operation.CREATE2] : List Operation))
    (hin7 : ∀ {stack : Stack UInt256}
      {gas target value inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop7 =
        some (stack, gas, target, value, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (hin6 : ∀ {stack : Stack UInt256}
      {gas target inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop6 =
        some (stack, gas, target, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : step gasCost (op, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  simp at hop
  rcases hop with hcall | hcallcode | hdelegatecall | hstaticcall | hcreate | hcreate2
  · subst op
    exact step_call_returnData_size_le_maxReturnDataSizeByGas hin7 h
  · subst op
    exact step_callcode_returnData_size_le_maxReturnDataSizeByGas hin7 h
  · subst op
    exact step_delegatecall_returnData_size_le_maxReturnDataSizeByGas hin6 h
  · subst op
    exact step_staticcall_returnData_size_le_maxReturnDataSizeByGas hin6 h
  · subst op
    exact step_create_returnData_size_le_maxReturnDataSizeByGas h
  · subst op
    exact step_create2_returnData_size_le_maxReturnDataSizeByGas h

lemma step_recursive_returnData_size_lt_uint256 {gasCost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)} {state state' : State}
    (hop : op ∈
      ([Operation.CALL, Operation.CALLCODE, Operation.DELEGATECALL, Operation.STATICCALL,
        Operation.CREATE, Operation.CREATE2] : List Operation))
    (hin7 : ∀ {stack : Stack UInt256}
      {gas target value inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop7 =
        some (stack, gas, target, value, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (hin6 : ∀ {stack : Stack UInt256}
      {gas target inOffset inSize outOffset outSize : UInt256},
      state.machineState.stack.pop6 =
        some (stack, gas, target, inOffset, inSize, outOffset, outSize) →
      (state.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
        maxReturnDataSizeByGas)
    (h : step gasCost (op, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_recursive_returnData_size_le_maxReturnDataSizeByGas hop hin7 hin6 h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma Xstep_recursive_returnData_size_le_maxReturnDataSizeByGas {validJumps : Array UInt256}
    {state state' : State} {ret : Option (HaltCause × ByteArray)}
    (hpaid : memoryPaidByGas state)
    (hop :
      ((decode state.executionEnv.code state.machineState.pc).getD
        (Operation.STOP, (none : Option (UInt256 × Nat)))).1 ∈
      ([Operation.CALL, Operation.CALLCODE, Operation.DELEGATECALL, Operation.STATICCALL,
        Operation.CREATE, Operation.CREATE2] : List Operation))
    (h : Xstep validJumps state = .ok (state', ret)) :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  unfold Xstep at h
  generalize hdecode :
      (decode state.executionEnv.code state.machineState.pc).getD
        (Operation.STOP, (none : Option (UInt256 × Nat))) = instr at h hop
  rcases instr with ⟨op, arg⟩
  simp at hop
  rcases hop with hcall | hcallcode | hdelegatecall | hstaticcall | hcreate | hcreate2
  · subst op
    simp [bind, Except.bind, hdecode] at h
    split at h
    · contradiction
    · rename_i stateZ cost hZ
      split at h
      · contradiction
      · rename_i stepped hstep
        let stepState : State := { stateZ with executionEnv.depth := state.executionEnv.depth }
        have hsame := Z_stack_active_eq (by simpa using hZ)
        have hin7 : ∀ {stack : Stack UInt256}
            {gas target value inOffset inSize outOffset outSize : UInt256},
            stepState.machineState.stack.pop7 =
              some (stack, gas, target, value, inOffset, inSize, outOffset, outSize) →
            (stepState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
              maxReturnDataSizeByGas := by
          intro stack gas target value inOffset inSize outOffset outSize hpop
          have hpop0 :
              state.machineState.stack.pop7 =
                some (stack, gas, target, value, inOffset, inSize, outOffset, outSize) := by
            simpa [stepState, hsame.1] using hpop
          have hin0 :=
            call_input_size_le_maxReturnDataSizeByGas_of_Z
              (validJumps := validJumps) (op := Operation.CALL)
              (Or.inl rfl) hpaid hpop0 (by simpa using hZ)
          simpa [stepState, hsame.2.2] using hin0
        have hout :=
          step_call_returnData_size_le_maxReturnDataSizeByGas
            (state := stepState) hin7 (by simpa [stepState] using hstep)
        injection h with hp
        cases hp
        simpa [stepState] using hout
  · subst op
    simp [bind, Except.bind, hdecode] at h
    split at h
    · contradiction
    · rename_i stateZ cost hZ
      split at h
      · contradiction
      · rename_i stepped hstep
        let stepState : State := { stateZ with executionEnv.depth := state.executionEnv.depth }
        have hsame := Z_stack_active_eq (by simpa using hZ)
        have hin7 : ∀ {stack : Stack UInt256}
            {gas target value inOffset inSize outOffset outSize : UInt256},
            stepState.machineState.stack.pop7 =
              some (stack, gas, target, value, inOffset, inSize, outOffset, outSize) →
            (stepState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
              maxReturnDataSizeByGas := by
          intro stack gas target value inOffset inSize outOffset outSize hpop
          have hpop0 :
              state.machineState.stack.pop7 =
                some (stack, gas, target, value, inOffset, inSize, outOffset, outSize) := by
            simpa [stepState, hsame.1] using hpop
          have hin0 :=
            call_input_size_le_maxReturnDataSizeByGas_of_Z
              (validJumps := validJumps) (op := Operation.CALLCODE)
              (Or.inr rfl) hpaid hpop0 (by simpa using hZ)
          simpa [stepState, hsame.2.2] using hin0
        have hout :=
          step_callcode_returnData_size_le_maxReturnDataSizeByGas
            (state := stepState) hin7 (by simpa [stepState] using hstep)
        injection h with hp
        cases hp
        simpa [stepState] using hout
  · subst op
    simp [bind, Except.bind, hdecode] at h
    split at h
    · contradiction
    · rename_i stateZ cost hZ
      split at h
      · contradiction
      · rename_i stepped hstep
        let stepState : State := { stateZ with executionEnv.depth := state.executionEnv.depth }
        have hsame := Z_stack_active_eq (by simpa using hZ)
        have hin6 : ∀ {stack : Stack UInt256}
            {gas target inOffset inSize outOffset outSize : UInt256},
            stepState.machineState.stack.pop6 =
              some (stack, gas, target, inOffset, inSize, outOffset, outSize) →
            (stepState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
              maxReturnDataSizeByGas := by
          intro stack gas target inOffset inSize outOffset outSize hpop
          have hpop0 :
              state.machineState.stack.pop6 =
                some (stack, gas, target, inOffset, inSize, outOffset, outSize) := by
            simpa [stepState, hsame.1] using hpop
          have hin0 :=
            delegate_input_size_le_maxReturnDataSizeByGas_of_Z
              (validJumps := validJumps) (op := Operation.DELEGATECALL)
              (Or.inl rfl) hpaid hpop0 (by simpa using hZ)
          simpa [stepState, hsame.2.2] using hin0
        have hout :=
          step_delegatecall_returnData_size_le_maxReturnDataSizeByGas
            (state := stepState) hin6 (by simpa [stepState] using hstep)
        injection h with hp
        cases hp
        simpa [stepState] using hout
  · subst op
    simp [bind, Except.bind, hdecode] at h
    split at h
    · contradiction
    · rename_i stateZ cost hZ
      split at h
      · contradiction
      · rename_i stepped hstep
        let stepState : State := { stateZ with executionEnv.depth := state.executionEnv.depth }
        have hsame := Z_stack_active_eq (by simpa using hZ)
        have hin6 : ∀ {stack : Stack UInt256}
            {gas target inOffset inSize outOffset outSize : UInt256},
            stepState.machineState.stack.pop6 =
              some (stack, gas, target, inOffset, inSize, outOffset, outSize) →
            (stepState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat).size ≤
              maxReturnDataSizeByGas := by
          intro stack gas target inOffset inSize outOffset outSize hpop
          have hpop0 :
              state.machineState.stack.pop6 =
                some (stack, gas, target, inOffset, inSize, outOffset, outSize) := by
            simpa [stepState, hsame.1] using hpop
          have hin0 :=
            delegate_input_size_le_maxReturnDataSizeByGas_of_Z
              (validJumps := validJumps) (op := Operation.STATICCALL)
              (Or.inr rfl) hpaid hpop0 (by simpa using hZ)
          simpa [stepState, hsame.2.2] using hin0
        have hout :=
          step_staticcall_returnData_size_le_maxReturnDataSizeByGas
            (state := stepState) hin6 (by simpa [stepState] using hstep)
        injection h with hp
        cases hp
        simpa [stepState] using hout
  · subst op
    simp [bind, Except.bind, hdecode] at h
    split at h
    · contradiction
    · rename_i stateZ cost hZ
      split at h
      · contradiction
      · rename_i stepped hstep
        have hout := step_create_returnData_size_le_maxReturnDataSizeByGas hstep
        injection h with hp
        cases hp
        simpa using hout
  · subst op
    simp [bind, Except.bind, hdecode] at h
    split at h
    · contradiction
    · rename_i stateZ cost hZ
      split at h
      · contradiction
      · rename_i stepped hstep
        have hout := step_create2_returnData_size_le_maxReturnDataSizeByGas hstep
        injection h with hp
        cases hp
        simpa using hout

set_option linter.unusedSimpArgs false in
lemma Xstep_recursive_returnData_size_lt_uint256 {validJumps : Array UInt256}
    {state state' : State} {ret : Option (HaltCause × ByteArray)}
    (hpaid : memoryPaidByGas state)
    (hop :
      ((decode state.executionEnv.code state.machineState.pc).getD
        (Operation.STOP, (none : Option (UInt256 × Nat)))).1 ∈
      ([Operation.CALL, Operation.CALLCODE, Operation.DELEGATECALL, Operation.STATICCALL,
        Operation.CREATE, Operation.CREATE2] : List Operation))
    (h : Xstep validJumps state = .ok (state', ret)) :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (Xstep_recursive_returnData_size_le_maxReturnDataSizeByGas hpaid hop h)
    maxReturnDataSizeByGas_lt_uint256

end EVM

end Ethereum
