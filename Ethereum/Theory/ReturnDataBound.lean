import Ethereum.Semantics

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
  native_decide

lemma maxReturnDataSizeByGas_lt_uint256 :
    maxReturnDataSizeByGas < UInt256.size := by
  norm_num [maxReturnDataSizeByGas, maxReturnDataWordsByGas, UInt256.size]

lemma pow_two_64_le_maxReturnDataSizeByGas :
    2 ^ 64 ≤ maxReturnDataSizeByGas := by
  norm_num [maxReturnDataSizeByGas, maxReturnDataWordsByGas]

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
  split
  · change (default : ByteArray).size ≤ len
    simp [default, Inhabited.default]
  · rw [ByteArray.size_append, ByteArray_zeroes_size]
    have hread := ByteArray.readWithoutPadding_size_le b addr len
    have hzero :
        (USize.ofBitVec
          ((len : BitVec System.Platform.numBits) -
            ((b.readWithoutPadding addr len).size :
              BitVec System.Platform.numBits))).toNat ≤
          len - (b.readWithoutPadding addr len).size :=
      USize.toNat_ofBitVec_sub_ofNat_le hread
    omega

lemma ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas
    (b : ByteArray) (addr len : Nat) :
    (b.readWithPadding addr len).size ≤ maxReturnDataSizeByGas := by
  by_cases hlen : len ≥ 2 ^ 64
  · have hlen' : 2 ^ 64 ≤ len := by simpa using hlen
    norm_num at hlen'
    simp [ByteArray.readWithPadding, hlen', default, Inhabited.default]
  ·
    have hsize := ByteArray.readWithPadding_size_le b addr len
    have h64 : len ≤ 2 ^ 64 := by omega
    exact Nat.le_trans hsize (Nat.le_trans h64 pow_two_64_le_maxReturnDataSizeByGas)

lemma ByteArray.readWithPadding_size_lt_uint256 (b : ByteArray) (addr len : Nat) :
    (b.readWithPadding addr len).size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas b addr len)
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
    (machine : MachineState) (offset len : UInt256) :
    (machine.evmReturn offset len).H_return.size ≤ maxReturnDataSizeByGas := by
  simp [MachineState.evmReturn,
    ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas]

lemma MachineState.evmRevert_H_return_size_le_maxReturnDataSizeByGas
    (machine : MachineState) (offset len : UInt256) :
    (machine.evmRevert offset len).H_return.size ≤ maxReturnDataSizeByGas := by
  simp [MachineState.evmRevert, MachineState.evmReturn,
    ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas]

lemma step_return_H_return_size_le_maxReturnDataSizeByGas {cost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
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
        offset len

lemma step_revert_H_return_size_le_maxReturnDataSizeByGas {cost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
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
        offset len

lemma MachineState.evmReturn_H_return_size_lt_uint256
    (machine : MachineState) (offset len : UInt256) :
    (machine.evmReturn offset len).H_return.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (MachineState.evmReturn_H_return_size_le_maxReturnDataSizeByGas machine offset len)
    maxReturnDataSizeByGas_lt_uint256

lemma MachineState.evmRevert_H_return_size_lt_uint256
    (machine : MachineState) (offset len : UInt256) :
    (machine.evmRevert offset len).H_return.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (MachineState.evmRevert_H_return_size_le_maxReturnDataSizeByGas machine offset len)
    maxReturnDataSizeByGas_lt_uint256

lemma step_return_H_return_size_lt_uint256 {cost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step cost (.RETURN, arg) state = .ok state') :
    state'.machineState.H_return.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_return_H_return_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

lemma step_revert_H_return_size_lt_uint256 {cost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step cost (.REVERT, arg) state = .ok state') :
    state'.machineState.H_return.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_revert_H_return_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

lemma Xstep_halt_output_size_le_maxReturnDataSizeByGas
    {validJumps : Array UInt256} {state state' : State}
    {cause : HaltCause} {out : ByteArray}
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
        (decode state.executionEnv.code state.machineState.pc).getD (.STOP, none) = instr at hstep h
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
            exact step_return_H_return_size_le_maxReturnDataSizeByGas hstep
          · rcases h with ⟨_, _, hout⟩
            subst out
            exact step_revert_H_return_size_le_maxReturnDataSizeByGas hstep
          · rcases h with ⟨_, _, hout⟩
            subst out
            simp [maxReturnDataSizeByGas]

lemma Xstep_halt_output_size_lt_uint256 {validJumps : Array UInt256} {state state' : State}
    {cause : HaltCause} {out : ByteArray}
    (h : Xstep validJumps state = .ok (state', some (cause, out))) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (Xstep_halt_output_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

lemma X_success_output_size_le_maxReturnDataSizeByGas
    {fuel : Nat} {validJumps : Array UInt256}
    {state state' : State} {out : ByteArray}
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
              exact ih h
          | some halted =>
              rcases halted with ⟨cause, haltOut⟩
              cases cause <;> simp at h
              rcases h with ⟨_, hout⟩
              subst out
              exact Xstep_halt_output_size_le_maxReturnDataSizeByGas hstep

lemma X_success_output_size_lt_uint256 {fuel : Nat} {validJumps : Array UInt256}
    {state state' : State} {out : ByteArray}
    (h : X fuel validJumps state = .ok (.success state' out)) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (X_success_output_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

lemma X_revert_output_size_le_maxReturnDataSizeByGas
    {fuel : Nat} {validJumps : Array UInt256}
    {state : State} {g : UInt256} {out : ByteArray}
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
              exact ih h
          | some halted =>
              rcases halted with ⟨cause, haltOut⟩
              cases cause <;> simp at h
              rcases h with ⟨_, hout⟩
              subst out
              exact Xstep_halt_output_size_le_maxReturnDataSizeByGas hstep

lemma X_revert_output_size_lt_uint256 {fuel : Nat} {validJumps : Array UInt256}
    {state : State} {g : UInt256} {out : ByteArray}
    (h : X fuel validJumps state = .ok (.revert g out)) :
    out.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (X_revert_output_size_le_maxReturnDataSizeByGas h)
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
          have hout := X_success_output_size_le_maxReturnDataSizeByGas hx
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
          have hout := X_revert_output_size_le_maxReturnDataSizeByGas hx
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
    native_decide
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
      exact USize.toNat_ofNat_le _
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
          h12, maxReturnDataSizeByGas, maxReturnDataWordsByGas]
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
          (ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas _ _ _))

set_option linter.unusedSimpArgs false in
lemma call_returnData_size_lt_uint256 {gasCost : Nat} {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {evmState state' : State} {x : UInt256}
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
      inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (call_returnData_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma step_call_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.CALL, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ _ _ _ vCall hCall
  rcases vCall with ⟨_, _⟩
  have hout := call_returnData_size_le_maxReturnDataSizeByGas hCall
  rw [← h]
  simpa using hout

set_option linter.unusedSimpArgs false in
lemma step_call_returnData_size_lt_uint256 {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.CALL, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_call_returnData_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma step_callcode_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.CALLCODE, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ _ _ _ vCall hCall
  rcases vCall with ⟨_, _⟩
  have hout := call_returnData_size_le_maxReturnDataSizeByGas hCall
  rw [← h]
  simpa using hout

set_option linter.unusedSimpArgs false in
lemma step_callcode_returnData_size_lt_uint256 {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.CALLCODE, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_callcode_returnData_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma step_delegatecall_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.DELEGATECALL, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ _ _ _ vCall hCall
  rcases vCall with ⟨_, _⟩
  have hout := call_returnData_size_le_maxReturnDataSizeByGas hCall
  rw [← h]
  simpa using hout

set_option linter.unusedSimpArgs false in
lemma step_delegatecall_returnData_size_lt_uint256 {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.DELEGATECALL, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_delegatecall_returnData_size_le_maxReturnDataSizeByGas h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma step_staticcall_returnData_size_le_maxReturnDataSizeByGas
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.STATICCALL, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ _ _ _ vCall hCall
  rcases vCall with ⟨_, _⟩
  have hout := call_returnData_size_le_maxReturnDataSizeByGas hCall
  rw [← h]
  simpa using hout

set_option linter.unusedSimpArgs false in
lemma step_staticcall_returnData_size_lt_uint256 {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (Operation.STATICCALL, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_staticcall_returnData_size_le_maxReturnDataSizeByGas h)
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
    (h : step gasCost (op, arg) state = .ok state') :
    state'.machineState.returnData.size ≤ maxReturnDataSizeByGas := by
  simp at hop
  rcases hop with hcall | hcallcode | hdelegatecall | hstaticcall | hcreate | hcreate2
  · subst op
    exact step_call_returnData_size_le_maxReturnDataSizeByGas h
  · subst op
    exact step_callcode_returnData_size_le_maxReturnDataSizeByGas h
  · subst op
    exact step_delegatecall_returnData_size_le_maxReturnDataSizeByGas h
  · subst op
    exact step_staticcall_returnData_size_le_maxReturnDataSizeByGas h
  · subst op
    exact step_create_returnData_size_le_maxReturnDataSizeByGas h
  · subst op
    exact step_create2_returnData_size_le_maxReturnDataSizeByGas h

lemma step_recursive_returnData_size_lt_uint256 {gasCost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)} {state state' : State}
    (hop : op ∈
      ([Operation.CALL, Operation.CALLCODE, Operation.DELEGATECALL, Operation.STATICCALL,
        Operation.CREATE, Operation.CREATE2] : List Operation))
    (h : step gasCost (op, arg) state = .ok state') :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (step_recursive_returnData_size_le_maxReturnDataSizeByGas hop h)
    maxReturnDataSizeByGas_lt_uint256

set_option linter.unusedSimpArgs false in
lemma Xstep_recursive_returnData_size_le_maxReturnDataSizeByGas {validJumps : Array UInt256}
    {state state' : State} {ret : Option (HaltCause × ByteArray)}
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
  all_goals
    subst op
    simp [bind, Except.bind, hdecode] at h
    split at h
    · contradiction
    · rename_i cost hZ
      split at h
      · contradiction
      · rename_i stepped hstep
        have hout :=
          step_recursive_returnData_size_le_maxReturnDataSizeByGas
            (by simp)
            hstep
        injection h with hp
        cases hp
        simpa using hout

set_option linter.unusedSimpArgs false in
lemma Xstep_recursive_returnData_size_lt_uint256 {validJumps : Array UInt256}
    {state state' : State} {ret : Option (HaltCause × ByteArray)}
    (hop :
      ((decode state.executionEnv.code state.machineState.pc).getD
        (Operation.STOP, (none : Option (UInt256 × Nat)))).1 ∈
      ([Operation.CALL, Operation.CALLCODE, Operation.DELEGATECALL, Operation.STATICCALL,
        Operation.CREATE, Operation.CREATE2] : List Operation))
    (h : Xstep validJumps state = .ok (state', ret)) :
    state'.machineState.returnData.size < UInt256.size := by
  exact Nat.lt_of_le_of_lt
    (Xstep_recursive_returnData_size_le_maxReturnDataSizeByGas hop h)
    maxReturnDataSizeByGas_lt_uint256

end EVM

end Ethereum
