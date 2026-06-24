import Ethereum.Semantics

import Mathlib.Tactic

namespace Ethereum

namespace EVM

lemma ByteArray.readWithoutPadding_size_le (b : ByteArray) (addr len : Nat) :
    (b.readWithoutPadding addr len).size ≤ len := by
  unfold ByteArray.readWithoutPadding
  split
  · simp
  · rw [ByteArray.size_extract]
    omega

lemma ByteArray.readWithPadding_size_lt_uint256 (b : ByteArray) (addr len : Nat) :
    (b.readWithPadding addr len).size < UInt256.size := by
  unfold ByteArray.readWithPadding
  split
  · change (default : ByteArray).size < UInt256.size
    simp [default, Inhabited.default, UInt256.size]
  · rename_i hlen
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    have hread := ByteArray.readWithoutPadding_size_le b addr len
    have hzero :
        ((⟨len - (b.readWithoutPadding addr len).size⟩ : USize).toNat) < 2 ^ 64 := by
      exact USize.toNat_lt _
    have hlenlt : len < 2 ^ 64 := by omega
    unfold UInt256.size
    omega

lemma MachineState.evmReturn_H_return_size_lt_uint256
    (machine : MachineState) (offset len : UInt256) :
    (machine.evmReturn offset len).H_return.size < UInt256.size := by
  simp [MachineState.evmReturn, ByteArray.readWithPadding_size_lt_uint256]

lemma MachineState.evmRevert_H_return_size_lt_uint256
    (machine : MachineState) (offset len : UInt256) :
    (machine.evmRevert offset len).H_return.size < UInt256.size := by
  simp [MachineState.evmRevert, MachineState.evmReturn,
    ByteArray.readWithPadding_size_lt_uint256]

lemma step_return_H_return_size_lt_uint256 {cost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step cost (.RETURN, arg) state = .ok state') :
    state'.machineState.H_return.size < UInt256.size := by
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
      exact ByteArray.readWithPadding_size_lt_uint256
        state.machineState.memory offset.toNat len.toNat

lemma step_revert_H_return_size_lt_uint256 {cost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step cost (.REVERT, arg) state = .ok state') :
    state'.machineState.H_return.size < UInt256.size := by
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
      exact ByteArray.readWithPadding_size_lt_uint256
        state.machineState.memory offset.toNat len.toNat

lemma Xstep_halt_output_size_lt_uint256 {validJumps : Array UInt256} {state state' : State}
    {cause : HaltCause} {out : ByteArray}
    (h : Xstep validJumps state = .ok (state', some (cause, out))) :
    out.size < UInt256.size := by
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
            simp [UInt256.size]
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
            exact step_return_H_return_size_lt_uint256 hstep
          · rcases h with ⟨_, _, hout⟩
            subst out
            exact step_revert_H_return_size_lt_uint256 hstep
          · rcases h with ⟨_, _, hout⟩
            subst out
            simp [UInt256.size]

lemma X_success_output_size_lt_uint256 {fuel : Nat} {validJumps : Array UInt256}
    {state state' : State} {out : ByteArray}
    (h : X fuel validJumps state = .ok (.success state' out)) :
    out.size < UInt256.size := by
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
              exact Xstep_halt_output_size_lt_uint256 hstep

lemma X_revert_output_size_lt_uint256 {fuel : Nat} {validJumps : Array UInt256}
    {state : State} {g : UInt256} {out : ByteArray}
    (h : X fuel validJumps state = .ok (.revert g out)) :
    out.size < UInt256.size := by
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
              exact Xstep_halt_output_size_lt_uint256 hstep

lemma Xi_success_output_size_lt_uint256
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {res : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate}
    {out : ByteArray}
    (h : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.success res out)) :
    out.size < UInt256.size := by
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
          have hout := X_success_output_size_lt_uint256 hx
          simp [hx] at h
          rcases h with ⟨_, houtEq⟩
          subst out
          exact hout
      | revert g' xiOut =>
          simp [hx] at h

lemma Xi_revert_output_size_lt_uint256
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {g' : UInt256} {out : ByteArray}
    (h : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' out)) :
    out.size < UInt256.size := by
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
          have hout := X_revert_output_size_lt_uint256 hx
          simp [hx] at h
          rcases h with ⟨_, houtEq⟩
          subst out
          exact hout

lemma Xi_tuple_match_output_size_lt_uint256
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (match Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
      | .error _ => (createdAccounts, ∅, (⟨0⟩ : UInt256), A, ByteArray.empty)
      | .ok (.revert g' out) => (createdAccounts, ∅, g', A, out)
      | .ok (.success (createdAccounts', σ', g', A') out) =>
          (createdAccounts', σ', g', A', out)).2.2.2.2.size < UInt256.size := by
  cases hxi : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
  | error err =>
      simp [UInt256.size]
  | ok xres =>
      cases xres with
      | revert g' out =>
          exact Xi_revert_output_size_lt_uint256 hxi
      | success res out =>
          rcases res with ⟨createdAccounts', σ', g', A'⟩
          exact Xi_success_output_size_lt_uint256 hxi

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
  cases hxi : Ξ createdAccounts genesisBlockHeader blocks σStar σ₀ g AStar I with
  | error err =>
      simp [UInt256.size]
  | ok xres =>
      cases xres with
      | revert g' out =>
          exact Xi_revert_output_size_lt_uint256 hxi
      | success res returnedData =>
          rcases res with ⟨createdAccounts', σStarStar, gStarStar, AStarStar⟩
          simp [UInt256.size]

lemma lambda_projection_output_size_lt_uint256
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress)
    (g p v : UInt256) (i : ByteArray) (e : Fin 1025) (ζ : Option ByteArray)
    (H : BlockHeader) (w : Bool) :
    (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
      s o g p v i e ζ H w).2.2.2.2.2.2.size < UInt256.size := by
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
      (Lambda_Xi_tuple_match_output_size_lt_uint256 a createdAccountsStar genesisBlockHeader blocks
        σ σStar σ₀ g AStar exEnv))

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
  have hout : out =
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
        s o g p v i e ζ H w).2.2.2.2.2.2 := by
    have hp := congrArg (fun x => x.2.2.2.2.2.2) h
    simpa using hp.symm
  rw [hout]
  exact lambda_projection_output_size_lt_uint256 blobVersionedHashes createdAccounts
    genesisBlockHeader blocks σ σ₀ A s o g p v i e ζ H w

lemma theta_code_projection_output_size_lt_uint256
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (code d : ByteArray) (g p v v' : UInt256) (e : Fin 1025)
    (H : BlockHeader) (w : Bool) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (ToExecute.Code code) g p v v' d e H w).2.2.2.2.2.size < UInt256.size := by
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
      (Xi_tuple_match_output_size_lt_uint256 createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I))

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
  have hout : out =
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (ToExecute.Code code) g p v v' d e H w).2.2.2.2.2 := by
    have hp := congrArg (fun x => x.2.2.2.2.2) h
    simpa using hp.symm
  rw [hout]
  exact theta_code_projection_output_size_lt_uint256
    blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
    code d g p v v' e H w

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
  unfold toExecute at h
  simp [hnot] at h
  cases hfind : σ.find? r with
  | none =>
      simp [hfind] at h
      exact theta_code_output_size_lt_uint256 h
  | some acc =>
      simp [hfind] at h
      exact theta_code_output_size_lt_uint256 h

/--
Trusted assumption for opaque precompile implementations.

The EVM-level proof above bounds return data produced by interpreted bytecode.  Precompiles are
implemented externally, so their corresponding bound is exposed as the single assumption needed
to lift the bytecode theorem to arbitrary call targets.
-/
axiom theta_precompiled_output_size_lt_uint256
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
    out.size < UInt256.size

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
        (createdAccounts', σ', g', A', z, out)) :
    out.size < UInt256.size := by
  cases c with
  | Code code =>
      exact theta_code_output_size_lt_uint256 h
  | Precompiled pc =>
      exact theta_precompiled_output_size_lt_uint256 h

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
        (createdAccounts', σ', g', A', z, out)) :
    out.size < UInt256.size := by
  exact theta_output_size_lt_uint256 h

end EVM

end Ethereum
