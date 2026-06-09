import Ethereum.Semantics
import Ethereum.UInt256
import Ethereum.Data.Stack

namespace Ethereum

namespace EVM

set_option linter.unusedSimpArgs false

/-
 -  Helper lemmas
 -/

local instance : MonadLift Option (Except EVM.ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

lemma UInt256_lt_to_Nat : ∀ (a b : UInt256), a < b → a.toNat < b.toNat := by
  intros a b hlt; exact hlt

lemma UInt256_subzero : ∀ (a : UInt256), a - { val := 0 } = a := by
  intros a
  simp [Sub.sub, HSub.hSub, Sub.sub, UInt256.sub]
  simp [Fin.sub]
  have ha : a.1 % UInt256.size = a.1 := by
    apply Nat.mod_eq_of_lt; simp
  cases a with
  | mk a' => cases a' with
    | mk n hn =>
      simp [*] at ha
      simp; assumption

lemma  Sat256_natsub_zero : ∀ (a : Sat256), a.natSub 0 = a :=
  by intros a; simp [Sat256.natSub, Id.run]

lemma UInt256_subzero' : ∀ (a : UInt256), a - UInt256.ofNat 0 = a :=
  by intros a; simp [UInt256.ofNat, Id.run]; apply UInt256_subzero a

lemma UInt256_ofNat_0 : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by
  simp [UInt256.ofNat, Id.run]

lemma UInt256_ofNat_1 : UInt256.ofNat 1 = (⟨1⟩ : UInt256) := by
  rfl

lemma extCodeHash_executionEnv_eq (s : State) (env : ExecutionEnv) (v : UInt256) :
    Ethereum.State.extCodeHash {s with executionEnv := env} v =
      let result := Ethereum.State.extCodeHash s v
      ({result.1 with executionEnv := env}, result.2) := by
  simp [Ethereum.State.extCodeHash, Ethereum.State.addAccessedAccount]
  split <;> rfl

@[simp] lemma C'_jump (s : State) : C' s .JUMP = GasConstants.Gmid := by
  simp [C', InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero, InstructionGasGroups.Wbase,
    InstructionGasGroups.Wverylow, InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
    InstructionGasGroups.Wverylow.dupInstrs, InstructionGasGroups.Wverylow.swapInstrs,
    InstructionGasGroups.Wlow, InstructionGasGroups.Wmid]

@[simp] lemma C'_jumpi (s : State) : C' s .JUMPI = GasConstants.Ghigh := by
  simp [C', InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero, InstructionGasGroups.Wbase,
    InstructionGasGroups.Wverylow, InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
    InstructionGasGroups.Wverylow.dupInstrs, InstructionGasGroups.Wverylow.swapInstrs,
    InstructionGasGroups.Wlow, InstructionGasGroups.Wmid, InstructionGasGroups.Whigh]

@[simp] lemma monadLift_option_some {α : Type} (a : α) :
    (monadLift (some a) : Except EVM.ExecutionException α) = .ok a := by
  rfl

@[simp] lemma monadLift_option_none {α : Type} :
    (monadLift (none : Option α) : Except EVM.ExecutionException α) = .error .StackUnderflow := by
  rfl

@[simp] lemma Account_toPersistentAccountState_storage (acc : Account) :
    acc.toPersistentAccountState.storage = acc.storage := by
  rfl

@[simp] lemma Account_fst_storage (acc : Account) :
    acc.1.storage = acc.storage := by
  rfl

lemma UInt256_bne_zero_eq_false_eq (b : UInt256)
    (h : (b != (⟨0⟩ : UInt256)) = false) : b = (⟨0⟩ : UInt256) := by
  cases b with
  | mk bv =>
    cases bv with
    | mk n hn =>
      change (! (⟨n, hn⟩ == (0 : Fin UInt256.size))) = false at h
      have hbeq : (⟨n, hn⟩ == (0 : Fin UInt256.size)) = true := by
        cases hb : (⟨n, hn⟩ == (0 : Fin UInt256.size)) <;> simp [hb] at h ⊢
      have hfin : ⟨n, hn⟩ = (0 : Fin UInt256.size) := LawfulBEq.eq_of_beq hbeq
      cases hfin
      rfl

lemma UInt256_bne_zero_eq_true_ne (b : UInt256)
    (h : (b != (⟨0⟩ : UInt256)) = true) : b ≠ (⟨0⟩ : UInt256) := by
  cases b with
  | mk bv =>
    cases bv with
    | mk n hn =>
      intro hz
      cases hz
      have hfalse : (({ val := ⟨0, hn⟩ } : UInt256) != (⟨0⟩ : UInt256)) = false := by
        simpa using (show ((⟨0⟩ : UInt256) != (⟨0⟩ : UInt256)) = false by decide)
      rw [hfalse] at h
      contradiction


/-
 -         Opcode Step Results
 -/


/-
 -   Stop and Arithmetic Operations
 -/

theorem step_invalid : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.INVALID, .none)
  → Xstep (D_J I_b ⟨0⟩) s = .error .InvalidInstruction
:= by
    intros s I_b hinvalid
    simp [Xstep, Z, δ, I_b, hinvalid]

theorem step_stop : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.STOP, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.stack.length - 0 + 0 > 1024 then .error .StackOverflow
      else
      .ok ({s with
              machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gzero
              machineState.execLength := s.machineState.execLength + 1
              machineState.returnData := .empty
            }, .some (true, .empty))
:= by
    intros s I_b hstop
    simp [Xstep, Z, δ, I_b, hstop]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    have hgas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gzero := by
      simp [GasConstants.Gzero]
    have hgas' :
        ¬ (s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gzero := by
      simpa [UInt256_subzero'] using hgas
    rw [if_neg hgas']
    simp [α, Operation.isCreate]
    by_cases hoverflow : 1024 < s.machineState.stack.length
    · simp [hoverflow]
    ·
      simp [hoverflow]
      simp [bind, Except.bind]
      unfold step
      simp [MachineState.setReturnData, GasConstants.Gzero]
      rw [Sat256_natsub_zero]

theorem step_add : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.ADD, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024
        then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := (a + b) :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hadd
    simp [Xstep, Z, δ, I_b, hadd]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy
        , InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero
        , InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
            simpa [UInt256_subzero'] using hgas
          simp [bind, Except.bind]

          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]; constructor
            · simp [UInt256.add]; rfl
            · rw [Sat256_natsub_zero]

theorem step_mul : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.MUL, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Glow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.mul a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub $ GasConstants.Glow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hmul
    simp [Xstep, Z, δ, I_b, hmul]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy
        , InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero
        , InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs
        , InstructionGasGroups.Wlow ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Glow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]

          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push, flip]
            rw [Sat256_natsub_zero]

theorem step_exp : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.EXP, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        let gasCost :=
          if b == ⟨0⟩ then GasConstants.Gexp
          else GasConstants.Gexp + GasConstants.Gexpbyte * (1 + Nat.log 256 b.toNat)
        if s.machineState.gasAvailable.toNat < gasCost then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.exp a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub gasCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hexp
    simp [Xstep, Z, δ, I_b, hexp]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C']
      by_cases hgas:
          ((s.machineState.gasAvailable.natSub 0).toNat <
            if b == ⟨0⟩ then GasConstants.Gexp
            else GasConstants.Gexp + GasConstants.Gexpbyte * (1 + Nat.log 256 b.toNat))
      · simp [hgas]
        have hgas0 :
            s.machineState.gasAvailable.toNat <
              (if b == ⟨0⟩ then GasConstants.Gexp
              else GasConstants.Gexp + GasConstants.Gexpbyte * (1 + Nat.log 256 b.toNat)) := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 :
            ¬ s.machineState.gasAvailable.toNat <
              (if b == ⟨0⟩ then GasConstants.Gexp
              else GasConstants.Gexp + GasConstants.Gexpbyte * (1 + Nat.log 256 b.toNat)) := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push, flip]
            rw [Sat256_natsub_zero]

theorem step_addmod : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.ADDMOD, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gmid then .error .OutOfGass
        else
        if s.machineState.stack.length - 3 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.addMod a b c :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gmid
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b haddmod
    simp [Xstep, Z, δ, I_b, haddmod]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | a :: b :: c :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 < 3 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs
        , InstructionGasGroups.Wlow, InstructionGasGroups.Wmid ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gmid)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gmid := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gmid := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execTriOp, Stack.pop3, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push, Ethereum.State.calldataload]
            rw [Sat256_natsub_zero]

theorem step_mulmod : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.MULMOD, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gmid then .error .OutOfGass
        else
        if s.machineState.stack.length - 3 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.mulMod a b c :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gmid
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hmulmod
    simp [Xstep, Z, δ, I_b, hmulmod]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | a :: b :: c :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 < 3 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs
        , InstructionGasGroups.Wlow, InstructionGasGroups.Wmid ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gmid)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gmid := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gmid := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execTriOp, Stack.pop3, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push, Ethereum.State.blockHash]
            rw [Sat256_natsub_zero]

theorem step_sdiv : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SDIV, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Glow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.sdiv a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Glow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hsdiv
    simp [Xstep, Z, δ, I_b, hsdiv]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs
        , InstructionGasGroups.Wlow ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Glow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push, blobhash]
            rw [UInt256_subzero']

theorem step_mod : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.MOD, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Glow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.mod a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Glow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hmod
    simp [Xstep, Z, δ, I_b, hmod]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs
        , InstructionGasGroups.Wlow ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Glow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_smod : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SMOD, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Glow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.smod a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Glow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hsmod
    simp [Xstep, Z, δ, I_b, hsmod]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs
        , InstructionGasGroups.Wlow ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Glow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_signextend : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SIGNEXTEND, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Glow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.signextend a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Glow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hsignextend
    simp [Xstep, Z, δ, I_b, hsignextend]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs
        , InstructionGasGroups.Wlow ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Glow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_sub : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SUB, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.sub a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hsub
    simp [Xstep, Z, δ, I_b, hsub]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy
        , InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero
        , InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs
        , InstructionGasGroups.Wlow ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]

          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_div : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DIV, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Glow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.div a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Glow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdiv
    simp [Xstep, Z, δ, I_b, hdiv]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy
        , InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero
        , InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs
        , InstructionGasGroups.Wlow ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Glow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Glow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]

          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

/-
 -   Comparison and Bitwise Logic Operations
 -/

theorem step_lt : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.LT, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.lt a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hlt
    simp [Xstep, Z, δ, I_b, hlt]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_gt : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.GT, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.gt a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hgt
    simp [Xstep, Z, δ, I_b, hgt]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_slt : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SLT, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.slt a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hslt
    simp [Xstep, Z, δ, I_b, hslt]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_sgt : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SGT, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.sgt a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hsgt
    simp [Xstep, Z, δ, I_b, hsgt]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_eq : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.EQ, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.eq a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b heq
    simp [Xstep, Z, δ, I_b, heq]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_and : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.AND, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.land a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hand
    simp [Xstep, Z, δ, I_b, hand]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_or : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.OR, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.lor a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hor
    simp [Xstep, Z, δ, I_b, hor]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_xor : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.XOR, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.xor a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hxor
    simp [Xstep, Z, δ, I_b, hxor]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_byte : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.BYTE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.byteAt a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hbyte
    simp [Xstep, Z, δ, I_b, hbyte]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_shl : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SHL, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.shiftLeft b a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hshl
    simp [Xstep, Z, δ, I_b, hshl]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push, flip]
            rw [UInt256_subzero']

theorem step_shr : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SHR, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.shiftRight b a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hshr
    simp [Xstep, Z, δ, I_b, hshr]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push, flip]
            rw [UInt256_subzero']

theorem step_sar : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SAR, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.sar a b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hsar
    simp [Xstep, Z, δ, I_b, hsar]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execBinOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_iszero : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.ISZERO, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.isZero a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hiszero
    simp [Xstep, Z, δ, I_b, hiszero]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execUnOp, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_not : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.NOT, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := UInt256.lnot a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hnot
    simp [Xstep, Z, δ, I_b, hnot]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.execUnOp, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

/-
 -   Keccak Operation
 -/

theorem step_keccak : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.KECCAK256, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        let memoryCost := memoryExpansionCost s .KECCAK256
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let hashCost := GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32)
        if gasAvailable'.toNat < hashCost then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 1 > 1024 then .error .StackOverflow
        else
        let bytes := s.machineState.memory.readWithPadding a.toNat b.toNat
        let kec := ffi.KEC bytes
        .ok ({s with
                  machineState.stack := UInt256.ofNat (fromByteArrayBigEndian kec) :: t,
                  machineState.gasAvailable := gasAvailable'.natSub hashCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hkeccak
    simp [Xstep, Z, δ, I_b, hkeccak]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .KECCAK256
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .KECCAK256)
        by_cases hgas :
            gasAvailable'.toNat <
              GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32)
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32) := by
            simpa [gasAvailable', memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32) := by
            simpa [gasAvailable', memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length + 1
          · simp [hoverflow]
          ·
            simp [hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Id.run, EVM.binaryMachineStateOp', Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            simp
            apply And.intro
            · simp [UInt256.ofNat, Id.run]; rfl
            · apply And.intro
              · simp [Stack.push, MachineState.keccak256]
              · simp [MachineState.keccak256]

/-
 -   Environment Information Operations
 -/

theorem step_address : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.ADDRESS, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.codeOwner.val :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b haddress
    simp [Xstep, Z, δ, I_b, haddress]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.executionEnvOp, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push, Ethereum.State.selfbalance]
          rw [UInt256_subzero']

theorem step_origin : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.ORIGIN, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.sender.val :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b horigin
    simp [Xstep, Z, δ, I_b, horigin]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.executionEnvOp, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_caller : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CALLER, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.source.val :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hcaller
    simp [Xstep, Z, δ, I_b, hcaller]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.executionEnvOp, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_callvalue : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CALLVALUE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := s.executionEnv.weiValue :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hcallvalue
    simp [Xstep, Z, δ, I_b, hcallvalue]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.executionEnvOp, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_calldatasize : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CALLDATASIZE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.calldata.size :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hcalldatasize
    simp [Xstep, Z, δ, I_b, hcalldatasize]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.executionEnvOp, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_codesize : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CODESIZE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.code.size :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hcodesize
    simp [Xstep, Z, δ, I_b, hcodesize]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.executionEnvOp, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_gasprice : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.GASPRICE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.gasPrice :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hgasprice
    simp [Xstep, Z, δ, I_b, hgasprice]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.executionEnvOp, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_returndatasize : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.RETURNDATASIZE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.machineState.returnData.size :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hreturndatasize
    simp [Xstep, Z, δ, I_b, hreturndatasize]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.machineStateOp, Ethereum.State.replaceStackAndIncrPC, MachineState.returndatasize]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_coinbase : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.COINBASE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.header.beneficiary.val :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hcoinbase
    simp [Xstep, Z, δ, I_b, hcoinbase]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.stateOp, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.coinBase]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_timestamp : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.TIMESTAMP, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.header.timestamp :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b htimestamp
    simp [Xstep, Z, δ, I_b, htimestamp]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.stateOp, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.timeStamp]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_number : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.NUMBER, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.header.number :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hnumber
    simp [Xstep, Z, δ, I_b, hnumber]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.stateOp, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.number]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_prevrandao : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PREVRANDAO, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := s.executionEnv.header.prevRandao :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hprevrandao
    simp [Xstep, Z, δ, I_b, hprevrandao]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.executionEnvOp, Ethereum.prevRandao, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_gaslimit : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.GASLIMIT, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.header.gasLimit :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hgaslimit
    simp [Xstep, Z, δ, I_b, hgaslimit]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.stateOp, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.gasLimit]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_chainid : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CHAINID, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat Ethereum.chainId :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hchainid
    simp [Xstep, Z, δ, I_b, hchainid]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.stateOp, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.chainId]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_basefee : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.BASEFEE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.header.baseFeePerGas :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hbasefee
    simp [Xstep, Z, δ, I_b, hbasefee]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.executionEnvOp, Ethereum.basefee, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_blobbasefee : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.BLOBBASEFEE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := UInt256.ofNat s.executionEnv.header.getBlobGasprice :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hblobbasefee
    simp [Xstep, Z, δ, I_b, hblobbasefee]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.executionEnvOp, Ethereum.ExecutionEnv.getBlobGasprice, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_calldataload : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CALLDATALOAD, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack :=
                    (uInt256OfByteArray <| s.executionEnv.calldata.readBytes a.toNat 32) :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hcalldataload
    simp [Xstep, Z, δ, I_b, hcalldataload]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs ]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.unaryStateOp, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            apply And.intro
            · simp [Ethereum.State.calldataload]
            · rw [UInt256_subzero']

theorem step_blockhash : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.BLOCKHASH, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gblockhash then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack :=
                    (if s.executionEnv.header.number ≤ a.toNat || a.toNat + 256 < s.executionEnv.header.number then
                      ⟨0⟩
                    else
                      s.blocks.map ProcessedBlock.hash |>.getD a.toNat ⟨0⟩) :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gblockhash
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hblockhash
    simp [Xstep, Z, δ, I_b, hblockhash]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C']
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gblockhash)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gblockhash := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gblockhash := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.unaryStateOp, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            apply And.intro
            · simp [Ethereum.State.blockHash, Ethereum.State.blockHashes]
            · rw [UInt256_subzero']

theorem step_blobhash : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.BLOBHASH, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.HASH_OPCODE_GAS then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack :=
                    (s.executionEnv.blobVersionedHashes[a.toNat]?.option ⟨0⟩
                      (.ofNat ∘ fromByteArrayBigEndian)) :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.HASH_OPCODE_GAS
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hblobhash
    simp [Xstep, Z, δ, I_b, hblobhash]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C']
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.HASH_OPCODE_GAS)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.HASH_OPCODE_GAS := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.HASH_OPCODE_GAS := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.unaryExecutionEnvOp, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          unfold blobhash
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push]
            rw [UInt256_subzero']

theorem step_selfbalance : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SELFBALANCE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Glow then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack :=
                  (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ::
                    s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Glow
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hselfbalance
    simp [Xstep, Z, δ, I_b, hselfbalance]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
      , InstructionGasGroups.Wverylow
      , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
      , InstructionGasGroups.Wverylow.dupInstrs
      , InstructionGasGroups.Wverylow.swapInstrs
      , InstructionGasGroups.Wlow]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Glow)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Glow := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Glow := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.stateOp, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          apply And.intro
          · simp [Ethereum.State.selfbalance]
          · rw [UInt256_subzero']
theorem step_balance : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.BALANCE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        let addr := AccountAddress.ofUInt256 a
        let gasCost := Caccess addr s.substate
        if s.machineState.gasAvailable.toNat < gasCost then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  substate :=
                    {s.substate with
                      accessedAccounts := s.substate.accessedAccounts.insert addr}
                  machineState.stack := (s.accountMap.find? addr |>.elim ⟨0⟩ (·.balance)) :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub gasCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hbalance
    simp [Xstep, Z, δ, I_b, hbalance]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount]
      by_cases hgas:
          ((s.machineState.gasAvailable.natSub 0).toNat <
            Caccess (AccountAddress.ofUInt256 a) s.substate)
      · simp [hgas]
        have hgas0 :
            s.machineState.gasAvailable.toNat <
              Caccess (AccountAddress.ofUInt256 a) s.substate := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 :
            ¬ s.machineState.gasAvailable.toNat <
              Caccess (AccountAddress.ofUInt256 a) s.substate := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.unaryStateOp, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push, Ethereum.State.balance, Ethereum.State.addAccessedAccount,
              Ethereum.Substate.addAccessedAccount]
            apply And.intro
            · rw [UInt256_ofNat_1]
            · rw [UInt256_subzero']

theorem step_extcodesize : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.EXTCODESIZE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        let addr := AccountAddress.ofUInt256 a
        let gasCost := Caccess addr s.substate
        if s.machineState.gasAvailable.toNat < gasCost then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  substate :=
                    {s.substate with
                      accessedAccounts := s.substate.accessedAccounts.insert addr}
                  machineState.stack :=
                    (s.accountMap.find? addr |>.option ⟨0⟩ (.ofNat ∘ ByteArray.size ∘ (·.code))) :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub gasCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hextcodesize
    simp [Xstep, Z, δ, I_b, hextcodesize]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount]
      by_cases hgas:
          ((s.machineState.gasAvailable.natSub 0).toNat <
            Caccess (AccountAddress.ofUInt256 a) s.substate)
      · simp [hgas]
        have hgas0 :
            s.machineState.gasAvailable.toNat <
              Caccess (AccountAddress.ofUInt256 a) s.substate := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 :
            ¬ s.machineState.gasAvailable.toNat <
              Caccess (AccountAddress.ofUInt256 a) s.substate := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.unaryStateOp, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · simp [Stack.push, Ethereum.State.extCodeSize, Ethereum.State.lookupAccount,
              Ethereum.State.addAccessedAccount, Ethereum.Substate.addAccessedAccount]
            apply And.intro
            · rw [UInt256_ofNat_1]
            · rw [UInt256_subzero']

theorem step_extcodehash : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.EXTCODEHASH, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        let addr := AccountAddress.ofUInt256 a
        let gasCost := Caccess addr s.substate
        if s.machineState.gasAvailable.toNat < gasCost then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        let hash :=
          if s.accountMap.find? addr |>.option true Account.emptyAccount then
            ⟨0⟩
          else
            s.accountMap.find? addr |>.option ⟨0⟩ Account.codeHash
        .ok ({s with
                  substate :=
                    {s.substate with
                      accessedAccounts := s.substate.accessedAccounts.insert addr}
                  machineState.stack := hash :: t
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub gasCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hextcodehash
    simp [Xstep, Z, δ, I_b, hextcodehash]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount]
      by_cases hgas:
          ((s.machineState.gasAvailable.natSub 0).toNat <
            Caccess (AccountAddress.ofUInt256 a) s.substate)
      · simp [hgas]
        have hgas0 :
            s.machineState.gasAvailable.toNat <
              Caccess (AccountAddress.ofUInt256 a) s.substate := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 :
            ¬ s.machineState.gasAvailable.toNat <
              Caccess (AccountAddress.ofUInt256 a) s.substate := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.unaryStateOp, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp [Stack.push, Ethereum.State.extCodeHash, Ethereum.State.dead,
            Ethereum.State.lookupAccount, Ethereum.State.addAccessedAccount,
            Ethereum.Substate.addAccessedAccount, UInt256_ofNat_1, UInt256_subzero']
          by_cases hdead :
              Option.option true Account.emptyAccount
                (Batteries.RBMap.find? s.accountMap (AccountAddress.ofUInt256 a)) = true
          · simp [hdead, UInt256_ofNat_1, UInt256_subzero']
          · simp [hdead, UInt256_ofNat_1, UInt256_subzero']

/-
 -   Machine and Stack Operations
 -/

theorem step_pop : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.POP, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | _ :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 0 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hpop
    simp [Xstep, Z, δ, I_b, hpop]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']
theorem step_mload : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.MLOAD, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        let memoryCost := memoryExpansionCost s .MLOAD
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        if gasAvailable'.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack :=
                    (if a.toNat ≥ s.machineState.memory.size ∨
                        a ≥ s.machineState.activeWords * ⟨32⟩ then
                      ⟨0⟩
                    else
                      UInt256.ofNat
                        (fromByteArrayBigEndian
                          (s.machineState.memory.readWithPadding a.toNat 32))) :: t
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat 32)
                  machineState.gasAvailable := gasAvailable'.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hmload
    simp [Xstep, Z, δ, I_b, hmload]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .MLOAD
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .MLOAD)
        by_cases hgas : gasAvailable'.toNat < GasConstants.Gverylow
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat 32)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow := by
            simpa [gasAvailable', memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
            InstructionGasGroups.Wzero, InstructionGasGroups.Wbase,
            InstructionGasGroups.Wverylow]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat 32)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow := by
            simpa [gasAvailable', memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
            InstructionGasGroups.Wzero, InstructionGasGroups.Wbase,
            InstructionGasGroups.Wverylow]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length + 1
          · simp [hoverflow]
          ·
            simp [hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Id.run, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            simp [MachineState.mload, MachineState.lookupMemory]
            apply And.intro
            · rw [UInt256_ofNat_1]
            · simp [Stack.push]

theorem step_mstore : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.MSTORE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        let memoryCost := memoryExpansionCost s .MSTORE
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        if gasAvailable'.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 0 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := t
                  machineState.memory := b.toByteArray.write 0 s.machineState.memory a.toNat 32
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat 32)
                  machineState.gasAvailable := gasAvailable'.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hmstore
    simp [Xstep, Z, δ, I_b, hmstore]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .MSTORE
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .MSTORE)
        by_cases hgas : gasAvailable'.toNat < GasConstants.Gverylow
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat 32)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow := by
            simpa [gasAvailable', memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
            InstructionGasGroups.Wzero, InstructionGasGroups.Wbase,
            InstructionGasGroups.Wverylow]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat 32)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow := by
            simpa [gasAvailable', memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
            InstructionGasGroups.Wzero, InstructionGasGroups.Wbase,
            InstructionGasGroups.Wverylow]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Id.run, EVM.binaryMachineStateOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            simp [MachineState.mstore, MachineState.writeWord, writeBytes]
            rw [UInt256_ofNat_1]

theorem step_mstore8 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.MSTORE8, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        let memoryCost := memoryExpansionCost s .MSTORE8
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        if gasAvailable'.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 0 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := t
                  machineState.memory :=
                    (⟨#[UInt8.ofNat b.toNat]⟩ : ByteArray).write 0 s.machineState.memory a.toNat 1
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat 1)
                  machineState.gasAvailable := gasAvailable'.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hmstore8
    simp [Xstep, Z, δ, I_b, hmstore8]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .MSTORE8
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .MSTORE8)
        by_cases hgas : gasAvailable'.toNat < GasConstants.Gverylow
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat 1)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow := by
            simpa [gasAvailable', memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
            InstructionGasGroups.Wzero, InstructionGasGroups.Wbase,
            InstructionGasGroups.Wverylow]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat 1)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow := by
            simpa [gasAvailable', memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
            InstructionGasGroups.Wzero, InstructionGasGroups.Wbase,
            InstructionGasGroups.Wverylow]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Id.run, EVM.binaryMachineStateOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            simp [MachineState.mstore8, writeBytes]
            rw [UInt256_ofNat_1]

theorem step_sload : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SLOAD, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        let gasCost := Csload (a :: t) s.substate s.executionEnv
        if s.machineState.gasAvailable.toNat < gasCost then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        let value :=
          s.accountMap.find? s.executionEnv.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD a ⟨0⟩)
        .ok ({s with
                  substate :=
                    {s.substate with
                      accessedStorageKeys :=
                        s.substate.accessedStorageKeys.insert (s.executionEnv.codeOwner, a)}
                  machineState.stack := value :: t
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub gasCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hsload
    simp [Xstep, Z, δ, I_b, hsload]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
      by_cases hgas :
          ((s.machineState.gasAvailable.natSub 0).toNat <
            Csload (a :: t) s.substate s.executionEnv)
      · simp [hgas, C', hstack]
        have hgas0 :
            s.machineState.gasAvailable.toNat <
              Csload (a :: t) s.substate s.executionEnv := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 :
            ¬ s.machineState.gasAvailable.toNat <
              Csload (a :: t) s.substate s.executionEnv := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, C', hstack]
        simp [α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.unaryStateOp, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp [Ethereum.State.sload, Ethereum.State.lookupAccount, Ethereum.State.addAccessedStorageKey,
          Ethereum.Substate.addAccessedStorageKey, Account.lookupStorage, Stack.push, UInt256_ofNat_1]
          rw [UInt256_subzero']

theorem step_tload : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.TLOAD, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        if s.machineState.gasAvailable.toNat < Ctload then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 1 > 1024 then .error .StackOverflow
        else
        let value :=
          s.accountMap.find? s.executionEnv.codeOwner |>.option ⟨0⟩
            (fun acc => acc.tstorage.findD a ⟨0⟩)
        .ok ({s with
                  machineState.stack := value :: t
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub Ctload
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b htload
    simp [Xstep, Z, δ, I_b, htload]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
      by_cases hgas :
          ((s.machineState.gasAvailable.natSub 0).toNat < Ctload)
      · simp [hgas, C', hstack]
        have hgas0 : s.machineState.gasAvailable.toNat < Ctload := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < Ctload := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, C', hstack]
        simp [α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 1
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [Id.run, EVM.unaryStateOp, Stack.pop, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp [Ethereum.State.tload, Ethereum.State.lookupAccount, Account.lookupTransientStorage,
          Stack.push, UInt256_ofNat_1]
          rw [UInt256_subzero']

theorem step_tstore : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.TSTORE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < Ctstore then .error .OutOfGass
        else if s.machineState.stack.length - 2 + 0 > 1024 then .error .StackOverflow
        else if ¬ s.executionEnv.perm then .error .StaticModeViolation
        else
        let accountMap :=
          s.accountMap.find? s.executionEnv.codeOwner |>.option s.accountMap
            (fun acc =>
              s.accountMap.insert s.executionEnv.codeOwner
                (if b == default then
                  {acc with tstorage := acc.tstorage.erase a}
                else
                  {acc with tstorage := acc.tstorage.insert a b}))
        .ok ({s with
                  accountMap := accountMap
                  machineState.stack := t
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub Ctstore
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b htstore
    simp [Xstep, Z, δ, I_b, htstore]
    match hstack : s.machineState.stack with
    | [] => simp
    | [_] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
      by_cases hgas :
          ((s.machineState.gasAvailable.natSub 0).toNat < Ctstore)
      · simp [hgas, C', hstack]
        have hgas0 : s.machineState.gasAvailable.toNat < Ctstore := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < Ctstore := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, C', hstack]
        simp [α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length
        · simp [hoverflow]
        ·
          simp [hoverflow]
          by_cases hstatic : s.executionEnv.perm = false
          · simp [hstatic]
          ·
            have hperm : s.executionEnv.perm = true := by
              cases hp : s.executionEnv.perm
              · exact False.elim (hstatic hp)
              · rfl
            simp [hstatic, hperm, bind, Except.bind]
            unfold step
            simp [Id.run, binaryStateOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            cases hacc :
                Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner with
            | none =>
              simp [Ethereum.State.tstore, Ethereum.State.lookupAccount,
                Ethereum.State.updateAccount, Account.updateTransientStorage,
                Stack.push, UInt256_ofNat_1, UInt256_subzero', hacc, hperm,
                Option.option]
            | some acc =>
              simp [Ethereum.State.tstore, Ethereum.State.lookupAccount,
                Ethereum.State.updateAccount, Account.updateTransientStorage,
                Stack.push, UInt256_ofNat_1, UInt256_subzero', hacc, hperm,
                Option.option]

theorem step_calldatacopy : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CALLDATACOPY, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: t =>
        let memoryCost := memoryExpansionCost s .CALLDATACOPY
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let copyCost := GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
        if gasAvailable'.toNat < copyCost then .error .OutOfGass
        else
        if s.machineState.stack.length - 3 + 0 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := t
                  machineState.memory :=
                    s.executionEnv.calldata.write b.toNat s.machineState.memory a.toNat c.toNat
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub copyCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hcalldatacopy
    simp [Xstep, Z, δ, I_b, hcalldatacopy]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | a :: b :: c :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 < 3 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .CALLDATACOPY
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .CALLDATACOPY)
        let copyCost := GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
        by_cases hgas : gasAvailable'.toNat < copyCost
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) := by
            simpa [gasAvailable', copyCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', copyCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) := by
            simpa [gasAvailable', copyCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', copyCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Id.run, EVM.ternaryCopyOp, Stack.pop3, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            simp [calldatacopy, UInt256_ofNat_1]

theorem step_codecopy : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CODECOPY, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: t =>
        let memoryCost := memoryExpansionCost s .CODECOPY
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let copyCost := GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
        if gasAvailable'.toNat < copyCost then .error .OutOfGass
        else
        if s.machineState.stack.length - 3 + 0 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := t
                  machineState.memory :=
                    s.executionEnv.code.write b.toNat s.machineState.memory a.toNat c.toNat
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub copyCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hcodecopy
    simp [Xstep, Z, δ, I_b, hcodecopy]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | a :: b :: c :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 < 3 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .CODECOPY
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .CODECOPY)
        let copyCost := GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
        by_cases hgas : gasAvailable'.toNat < copyCost
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) := by
            simpa [gasAvailable', copyCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', copyCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) := by
            simpa [gasAvailable', copyCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', copyCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Id.run, EVM.ternaryCopyOp, Stack.pop3, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            simp [codeCopy, UInt256_ofNat_1]

theorem step_returndatacopy : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.RETURNDATACOPY, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: t =>
        let memoryCost := memoryExpansionCost s .RETURNDATACOPY
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let copyCost := GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
        if gasAvailable'.toNat < copyCost then .error .OutOfGass
        else if b.toNat + c.toNat > s.machineState.returnData.size then .error .InvalidMemoryAccess
        else
        if s.machineState.stack.length - 3 + 0 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := t
                  machineState.memory :=
                    s.machineState.returnData.write b.toNat s.machineState.memory a.toNat c.toNat
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub copyCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hreturndatacopy
    simp [Xstep, Z, δ, I_b, hreturndatacopy]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | a :: b :: c :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 < 3 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .RETURNDATACOPY
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .RETURNDATACOPY)
        let copyCost := GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
        by_cases hgas : gasAvailable'.toNat < copyCost
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) := by
            simpa [gasAvailable', copyCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', copyCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) := by
            simpa [gasAvailable', copyCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', copyCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy]
          by_cases hreturn : b.toNat + c.toNat > s.machineState.returnData.size
          · simp [hreturn]
          ·
            simp [hreturn]
            simp [α, Operation.isCreate]
            by_cases hoverflow : 1024 < t.length
            · simp [hoverflow]
            ·
              simp [hoverflow]
              simp [bind, Except.bind]
              unfold step
              simp [Id.run, Stack.pop3, Ethereum.State.replaceStackAndIncrPC,
                MachineState.returndatacopy, writeBytes]
              unfold Ethereum.State.incrPC
              simp [UInt256_ofNat_1]

theorem step_extcodecopy : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.EXTCODECOPY, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: t =>
        let memoryCost := memoryExpansionCost s .EXTCODECOPY
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let addr := AccountAddress.ofUInt256 a
        let copyCost := Caccess addr s.substate + GasConstants.Gcopy * ((d.toNat + 31) / 32)
        if gasAvailable'.toNat < copyCost then .error .OutOfGass
        else
        if s.machineState.stack.length - 4 + 0 > 1024 then .error .StackOverflow
        else
        let code := s.accountMap.find? addr |>.option .empty (·.code)
        .ok ({s with
                  substate.accessedAccounts := s.substate.accessedAccounts.insert addr
                  machineState.stack := t
                  machineState.memory := code.write c.toNat s.machineState.memory b.toNat d.toNat
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat b.toNat d.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub copyCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hextcodecopy
    simp [Xstep, Z, δ, I_b, hextcodecopy]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 < 4 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .EXTCODECOPY
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .EXTCODECOPY)
        let addr := AccountAddress.ofUInt256 a
        let copyCost := Caccess addr s.substate + GasConstants.Gcopy * ((d.toNat + 31) / 32)
        by_cases hgas : gasAvailable'.toNat < copyCost
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat b.toNat d.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                Caccess (AccountAddress.ofUInt256 a) s.substate +
                  GasConstants.Gcopy * ((d.toNat + 31) / 32) := by
            simpa [gasAvailable', addr, copyCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', addr, copyCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat b.toNat d.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                Caccess (AccountAddress.ofUInt256 a) s.substate +
                  GasConstants.Gcopy * ((d.toNat + 31) / 32) := by
            simpa [gasAvailable', addr, copyCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', addr, copyCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Id.run, EVM.quaternaryCopyOp, Stack.pop4, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            simp [Ethereum.extCodeCopy', Ethereum.State.lookupAccount,
              Ethereum.Substate.addAccessedAccount, UInt256_ofNat_1]

theorem step_mcopy : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.MCOPY, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: t =>
        let memoryCost := memoryExpansionCost s .MCOPY
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let copyCost := GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
        if gasAvailable'.toNat < copyCost then .error .OutOfGass
        else
        if s.machineState.stack.length - 3 + 0 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := t
                  machineState.memory := s.machineState.memory.write b.toNat s.machineState.memory a.toNat c.toNat
                  machineState.activeWords :=
                    UInt256.ofNat
                      (MachineState.M s.machineState.activeWords.toNat (max a.toNat b.toNat) c.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub copyCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hmcopy
    simp [Xstep, Z, δ, I_b, hmcopy]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | a :: b :: c :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 < 3 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .MCOPY
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .MCOPY)
        let copyCost := GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
        by_cases hgas : gasAvailable'.toNat < copyCost
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat (max a.toNat b.toNat) c.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) := by
            simpa [gasAvailable', copyCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', copyCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat (max a.toNat b.toNat) c.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) := by
            simpa [gasAvailable', copyCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', copyCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Id.run, EVM.ternaryMachineStateOp, Stack.pop3, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            simp [MachineState.mcopy, writeBytes, UInt256_ofNat_1]

theorem step_return : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.RETURN, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        let memoryCost := memoryExpansionCost s .RETURN
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        if s.machineState.stack.length - 2 + 0 > 1024 then .error .StackOverflow
        else
        let output := s.machineState.memory.readWithPadding a.toNat b.toNat
        .ok ({s with
                  machineState.stack := t
                  machineState.H_return := output
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub GasConstants.Gzero
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.some (true, output))
      | _ => .error .StackUnderflow
:= by
    intros s I_b hreturn
    simp [Xstep, Z, δ, I_b, hreturn]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .RETURN
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .RETURN)
        by_cases hgas : gasAvailable'.toNat < GasConstants.Gzero
        · simp [GasConstants.Gzero] at hgas
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gzero := by
            simpa [gasAvailable', memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
            InstructionGasGroups.Wzero]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Id.run, EVM.binaryMachineStateOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            simp [MachineState.evmReturn, UInt256_ofNat_1, UInt256_subzero']

theorem step_revert : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.REVERT, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        let memoryCost := memoryExpansionCost s .REVERT
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        if s.machineState.stack.length - 2 + 0 > 1024 then .error .StackOverflow
        else
        let output := s.machineState.memory.readWithPadding a.toNat b.toNat
        .ok ({s with
                  machineState.stack := t
                  machineState.H_return := output
                  machineState.activeWords :=
                    let m := MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat
                    UInt256.ofNat (MachineState.M (UInt256.ofNat m).toNat a.toNat b.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub GasConstants.Gzero
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.some (false, output))
      | _ => .error .StackUnderflow
:= by
    intros s I_b hrevert
    simp [Xstep, Z, δ, I_b, hrevert]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .REVERT
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .REVERT)
        by_cases hgas : gasAvailable'.toNat < GasConstants.Gzero
        · simp [GasConstants.Gzero] at hgas
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gzero := by
            simpa [gasAvailable', memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack,
            InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
            InstructionGasGroups.Wzero]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Id.run, EVM.binaryMachineStateOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
            unfold Ethereum.State.incrPC
            simp [MachineState.evmRevert, MachineState.evmReturn, UInt256_ofNat_1, UInt256_subzero']

theorem step_log0 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.LOG0, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        let memoryCost := memoryExpansionCost s .LOG0
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let logCost := GasConstants.Glog + GasConstants.Glogdata * b.toNat
        if gasAvailable'.toNat < logCost then .error .OutOfGass
        else if s.machineState.stack.length - 2 + 0 > 1024 then .error .StackOverflow
        else if ¬ s.executionEnv.perm then .error .StaticModeViolation
        else
        let mem := s.machineState.memory.readWithPadding a.toNat b.toNat
        .ok ({s with
                  substate.logSeries := s.substate.logSeries.push ⟨s.executionEnv.codeOwner, #[], mem⟩
                  machineState.stack := t
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub logCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hlog0
    simp [Xstep, Z, δ, I_b, hlog0]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG0
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .LOG0)
        let logCost := GasConstants.Glog + GasConstants.Glogdata * b.toNat
        by_cases hgas : gasAvailable'.toNat < logCost
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Glog + GasConstants.Glogdata * b.toNat := by
            simpa [gasAvailable', logCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', logCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Glog + GasConstants.Glogdata * b.toNat := by
            simpa [gasAvailable', logCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', logCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            by_cases hstatic : s.executionEnv.perm = false
            · simp [hstatic]
            ·
              have hperm : s.executionEnv.perm = true := by
                cases hp : s.executionEnv.perm
                · exact False.elim (hstatic hp)
                · rfl
              simp [hstatic, hperm, bind, Except.bind]
              unfold step
              simp [Id.run, EVM.log0Op, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
              unfold Ethereum.State.incrPC
              simp [EVM.evmLogOp, logOp, UInt256_ofNat_1]

theorem step_log1 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.LOG1, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: t =>
        let memoryCost := memoryExpansionCost s .LOG1
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let logCost := GasConstants.Glog + GasConstants.Glogdata * b.toNat + GasConstants.Glogtopic
        if gasAvailable'.toNat < logCost then .error .OutOfGass
        else if s.machineState.stack.length - 3 + 0 > 1024 then .error .StackOverflow
        else if ¬ s.executionEnv.perm then .error .StaticModeViolation
        else
        let mem := s.machineState.memory.readWithPadding a.toNat b.toNat
        .ok ({s with
                  substate.logSeries := s.substate.logSeries.push ⟨s.executionEnv.codeOwner, #[c], mem⟩
                  machineState.stack := t
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub logCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hlog1
    simp [Xstep, Z, δ, I_b, hlog1]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | a :: b :: c :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 < 3 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG1
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .LOG1)
        let logCost := GasConstants.Glog + GasConstants.Glogdata * b.toNat + GasConstants.Glogtopic
        by_cases hgas : gasAvailable'.toNat < logCost
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Glog + GasConstants.Glogdata * b.toNat + GasConstants.Glogtopic := by
            simpa [gasAvailable', logCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', logCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Glog + GasConstants.Glogdata * b.toNat + GasConstants.Glogtopic := by
            simpa [gasAvailable', logCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', logCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            by_cases hstatic : s.executionEnv.perm = false
            · simp [hstatic]
            ·
              have hperm : s.executionEnv.perm = true := by
                cases hp : s.executionEnv.perm
                · exact False.elim (hstatic hp)
                · rfl
              simp [hstatic, hperm, bind, Except.bind]
              unfold step
              simp [Id.run, EVM.log1Op, Stack.pop3, Ethereum.State.replaceStackAndIncrPC]
              unfold Ethereum.State.incrPC
              simp [EVM.evmLogOp, logOp, UInt256_ofNat_1]

theorem step_log2 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.LOG2, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: t =>
        let memoryCost := memoryExpansionCost s .LOG2
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let logCost := GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic
        if gasAvailable'.toNat < logCost then .error .OutOfGass
        else if s.machineState.stack.length - 4 + 0 > 1024 then .error .StackOverflow
        else if ¬ s.executionEnv.perm then .error .StaticModeViolation
        else
        let mem := s.machineState.memory.readWithPadding a.toNat b.toNat
        .ok ({s with
                  substate.logSeries := s.substate.logSeries.push ⟨s.executionEnv.codeOwner, #[c, d], mem⟩
                  machineState.stack := t
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub logCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hlog2
    simp [Xstep, Z, δ, I_b, hlog2]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 < 4 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG2
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .LOG2)
        let logCost := GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic
        by_cases hgas : gasAvailable'.toNat < logCost
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic := by
            simpa [gasAvailable', logCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', logCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic := by
            simpa [gasAvailable', logCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', logCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            by_cases hstatic : s.executionEnv.perm = false
            · simp [hstatic]
            ·
              have hperm : s.executionEnv.perm = true := by
                cases hp : s.executionEnv.perm
                · exact False.elim (hstatic hp)
                · rfl
              simp [hstatic, hperm, bind, Except.bind]
              unfold step
              simp [Id.run, EVM.log2Op, Stack.pop4, Ethereum.State.replaceStackAndIncrPC]
              unfold Ethereum.State.incrPC
              simp [EVM.evmLogOp, logOp, UInt256_ofNat_1]

theorem step_log3 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.LOG3, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: t =>
        let memoryCost := memoryExpansionCost s .LOG3
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let logCost := GasConstants.Glog + GasConstants.Glogdata * b.toNat + 3 * GasConstants.Glogtopic
        if gasAvailable'.toNat < logCost then .error .OutOfGass
        else if s.machineState.stack.length - 5 + 0 > 1024 then .error .StackOverflow
        else if ¬ s.executionEnv.perm then .error .StaticModeViolation
        else
        let mem := s.machineState.memory.readWithPadding a.toNat b.toNat
        .ok ({s with
                  substate.logSeries := s.substate.logSeries.push ⟨s.executionEnv.codeOwner, #[c, d, e], mem⟩
                  machineState.stack := t
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub logCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hlog3
    simp [Xstep, Z, δ, I_b, hlog3]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 < 5 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG3
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .LOG3)
        let logCost := GasConstants.Glog + GasConstants.Glogdata * b.toNat + 3 * GasConstants.Glogtopic
        by_cases hgas : gasAvailable'.toNat < logCost
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Glog + GasConstants.Glogdata * b.toNat + 3 * GasConstants.Glogtopic := by
            simpa [gasAvailable', logCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', logCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Glog + GasConstants.Glogdata * b.toNat + 3 * GasConstants.Glogtopic := by
            simpa [gasAvailable', logCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', logCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            by_cases hstatic : s.executionEnv.perm = false
            · simp [hstatic]
            ·
              have hperm : s.executionEnv.perm = true := by
                cases hp : s.executionEnv.perm
                · exact False.elim (hstatic hp)
                · rfl
              simp [hstatic, hperm, bind, Except.bind]
              unfold step
              simp [Id.run, EVM.log3Op, Stack.pop5, Ethereum.State.replaceStackAndIncrPC]
              unfold Ethereum.State.incrPC
              simp [EVM.evmLogOp, logOp, UInt256_ofNat_1]

theorem step_log4 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.LOG4, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: t =>
        let memoryCost := memoryExpansionCost s .LOG4
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let logCost := GasConstants.Glog + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic
        if gasAvailable'.toNat < logCost then .error .OutOfGass
        else if s.machineState.stack.length - 6 + 0 > 1024 then .error .StackOverflow
        else if ¬ s.executionEnv.perm then .error .StaticModeViolation
        else
        let mem := s.machineState.memory.readWithPadding a.toNat b.toNat
        .ok ({s with
                  substate.logSeries := s.substate.logSeries.push ⟨s.executionEnv.codeOwner, #[c, d, e, f], mem⟩
                  machineState.stack := t
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
                  machineState.gasAvailable := gasAvailable'.natSub logCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hlog4
    simp [Xstep, Z, δ, I_b, hlog4]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 < 6 := by simp
      simp [hstacksize']
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG4
      · simp [hmem]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .LOG4)
        let logCost := GasConstants.Glog + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic
        by_cases hgas : gasAvailable'.toNat < logCost
        · have hgas' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Glog + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic := by
            simpa [gasAvailable', logCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', logCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
        ·
          have hgas' :
              ¬ (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat
                        (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Glog + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic := by
            simpa [gasAvailable', logCost, memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas
          simp [gasAvailable', logCost, hgas', memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            by_cases hstatic : s.executionEnv.perm = false
            · simp [hstatic]
            ·
              have hperm : s.executionEnv.perm = true := by
                cases hp : s.executionEnv.perm
                · exact False.elim (hstatic hp)
                · rfl
              simp [hstatic, hperm, bind, Except.bind]
              unfold step
              simp [Id.run, EVM.log4Op, Stack.pop6, Ethereum.State.replaceStackAndIncrPC]
              unfold Ethereum.State.incrPC
              simp [EVM.evmLogOp, logOp, UInt256_ofNat_1]

theorem step_sstore : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SSTORE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        let gasCost := Csstore s
        if s.machineState.gasAvailable.toNat < gasCost then .error .OutOfGass
        else if s.machineState.stack.length - 2 + 0 > 1024 then .error .StackOverflow
        else if ¬ s.executionEnv.perm then .error .StaticModeViolation
        else if s.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then .error .OutOfGass
        else
        let Iₐ := s.executionEnv.codeOwner
        let v₀ :=
          match s.σ₀.find? Iₐ with
          | none => ⟨0⟩
          | some acc => acc.storage.findD a ⟨0⟩
        let v := (s.accountMap.find! Iₐ).storage.findD a ⟨0⟩
        let v' := b
        let r_dirtyclear : ℤ :=
          if v₀ ≠ UInt256.ofNat 0 && v = UInt256.ofNat 0 then - GasConstants.Rsclear else
          if v₀ ≠ UInt256.ofNat 0 && v' = UInt256.ofNat 0 then GasConstants.Rsclear else
          0
        let r_dirtyreset : ℤ :=
          if v₀ = v' && v₀ = UInt256.ofNat 0 then GasConstants.Gsset - GasConstants.Gwarmaccess else
          if v₀ = v' && v₀ ≠ UInt256.ofNat 0 then GasConstants.Gsreset - GasConstants.Gwarmaccess else
          0
        let ΔAᵣ : ℤ :=
          if v ≠ v' && v₀ = v && v' = UInt256.ofNat 0 then GasConstants.Rsclear else
          if v ≠ v' && v₀ ≠ v then r_dirtyclear + r_dirtyreset else
          0
        let newAᵣ : UInt256 :=
          match ΔAᵣ with
          | .ofNat n => s.substate.refundBalance + UInt256.ofNat n
          | .negSucc n => s.substate.refundBalance - UInt256.ofNat n - ⟨1⟩
        let accountMap :=
          s.accountMap.find? Iₐ |>.option s.accountMap
            (fun acc =>
              s.accountMap.insert Iₐ
                (if b == default then
                  {acc with storage := acc.storage.erase a}
                else
                  {acc with storage := acc.storage.insert a b}))
        let substate :=
          s.accountMap.find? Iₐ |>.option s.substate
            (fun _ =>
              {s.substate with
                accessedStorageKeys := s.substate.accessedStorageKeys.insert (Iₐ, a)
                refundBalance := newAᵣ})
        .ok ({s with
                  accountMap := accountMap
                  substate := substate
                  machineState.stack := t
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub gasCost
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hsstore
    simp [Xstep, Z, δ, I_b, hsstore]
    match hstack : s.machineState.stack with
    | [] => simp
    | [_] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
      let chargedState : State :=
        {s with
          machineState :=
            {s.machineState with
              stack := a :: b :: t
              gasAvailable := s.machineState.gasAvailable.natSub 0}}
      by_cases hgas :
          ((s.machineState.gasAvailable.natSub 0).toNat < Csstore chargedState)
      · simp [hgas, C', hstack, chargedState]
        have hgas0 : s.machineState.gasAvailable.toNat < Csstore s := by
          simpa [chargedState, Csstore, hstack, UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < Csstore s := by
          simpa [chargedState, Csstore, hstack, UInt256_subzero'] using hgas
        simp [hgas, hgas0, C', hstack, chargedState]
        simp [α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length
        · simp [hoverflow]
        ·
          simp [hoverflow]
          by_cases hstatic : s.executionEnv.perm = false
          · simp [hstatic]
          ·
            have hperm : s.executionEnv.perm = true := by
              cases hp : s.executionEnv.perm
              · exact False.elim (hstatic hp)
              · rfl
            simp [hstatic, hperm]
            by_cases hstipend :
                (s.machineState.gasAvailable.natSub 0).toNat ≤ GasConstants.Gcallstipend
            · have hstipend0 :
                  s.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend := by
                simpa [UInt256_subzero'] using hstipend
              simp [hstipend, hstipend0]
            ·
              have hstipend0 :
                  ¬ s.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend := by
                simpa [UInt256_subzero'] using hstipend
              simp [hstipend, hstipend0, bind, Except.bind]
              unfold step
              simp [Id.run, binaryStateOp, Stack.pop2, Ethereum.State.replaceStackAndIncrPC]
              unfold Ethereum.State.incrPC
              cases hacc :
                  Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner with
              | none =>
                simp [Ethereum.State.sstore, Ethereum.State.lookupAccount,
                  Ethereum.State.setAccount, Ethereum.State.addAccessedStorageKey,
                  Ethereum.Substate.addAccessedStorageKey,
                  Account.updateStorage, Stack.push, UInt256_ofNat_1, UInt256_subzero',
                  hacc, hperm, Option.option]
                simp [Csstore, hstack]
              | some acc =>
                cases acc with
                | mk ps ts =>
                  cases ps
                  simp [Ethereum.State.sstore, Ethereum.State.lookupAccount,
                    Ethereum.State.setAccount, Ethereum.State.addAccessedStorageKey,
                    Ethereum.Substate.addAccessedStorageKey,
                    Account.updateStorage, Stack.push, UInt256_ofNat_1, UInt256_subzero',
                    hacc, hperm, Option.option]
                  rw [Account_fst_storage
                    (Batteries.RBMap.find! s.accountMap s.executionEnv.codeOwner)]
                  rw [Account_fst_storage
                    (Batteries.RBMap.find! s.accountMap s.executionEnv.codeOwner)]
                  rw [Account_fst_storage
                    (Batteries.RBMap.find! s.accountMap s.executionEnv.codeOwner)]
                  rw [Account_fst_storage
                    (Batteries.RBMap.find! s.accountMap s.executionEnv.codeOwner)]
                  simp [Csstore, hstack]
                  rfl

theorem step_call : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CALL, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | gas :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t =>
        let memoryCost := memoryExpansionCost s .CALL
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
          let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
          let gasState := {s with machineState.gasAvailable := gasAvailable'}
          let gasCost :=
            Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value gas
              s.accountMap gasState.machineState s.substate
          if gasAvailable'.toNat < gasCost then .error .OutOfGass
          else if s.machineState.stack.length - 7 + 1 > 1024 then .error .StackOverflow
          else if ¬ s.executionEnv.perm ∧ value ≠ ⟨0⟩ then .error .StaticModeViolation
          else
            let tAddr := AccountAddress.ofUInt256 target
            let source := AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner)
            let recipient := tAddr
            let Iₐ := s.executionEnv.codeOwner
            let σ := s.accountMap
            let Iₑ := s.executionEnv.depth
            let callMachineState := {gasState.machineState with execLength := s.machineState.execLength + 1}
            let callgas := Ccallgas tAddr recipient value gas σ callMachineState s.substate
            let i := s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let Astar := s.addAccessedAccount tAddr |>.substate
            let (cA, σ', g', A', z, o) :=
              if value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 then
                Θ s.executionEnv.blobVersionedHashes
                  (createdAccounts := s.createdAccounts) (genesisBlockHeader := s.genesisBlockHeader)
                  (blocks := s.blocks) (σ := σ) (σ₀ := s.σ₀) (A := Astar)
                  (s := source) (o := s.executionEnv.sender) (r := recipient)
                  (c := toExecute σ tAddr) (g := .ofNat callgas) (p := .ofNat s.executionEnv.gasPrice)
                  (v := value) (v' := value) (d := i) (e := Iₑ + 1)
                  (H := s.executionEnv.header) (w := s.executionEnv.perm)
              else
                (s.createdAccounts, s.accountMap, .ofNat callgas, Astar, false, .empty)
            let n : UInt256 := min outSize (.ofNat o.size)
            let x : UInt256 :=
              if (!z) || value > (σ.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ||
                  s.executionEnv.depth == 1024 then ⟨0⟩ else ⟨1⟩
            .ok ({ s with
                accountMap := σ'
                substate := A'
                machineState :=
                { s.machineState with
                  stack := x :: t
                  pc := s.machineState.pc + ⟨1⟩
                  memory := o.write 0 s.machineState.memory outOffset.toNat n.toNat
                  returnData := o
                  gasAvailable := gasAvailable'.natSub $ gasCost + g'.toNat
                  execLength := s.machineState.execLength + 1
                  activeWords :=
                    let m := MachineState.M s.machineState.activeWords.toNat inOffset.toNat inSize.toNat
                    .ofNat <| MachineState.M m outOffset.toNat outSize.toNat }
                createdAccounts := cA
              }, .none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdecode
    cases hstk : s.machineState.stack with
    | nil =>
      simp [Xstep, Z, δ, I_b, hdecode, hstk]
    | cons gas xs1 =>
      cases xs1 with
      | nil =>
        simp [Xstep, Z, δ, I_b, hdecode, hstk]
      | cons target xs2 =>
        cases xs2 with
        | nil =>
          simp [Xstep, Z, δ, I_b, hdecode, hstk]
        | cons value xs3 =>
          cases xs3 with
          | nil =>
            simp [Xstep, Z, δ, I_b, hdecode, hstk]
          | cons inOffset xs4 =>
            cases xs4 with
            | nil =>
              simp [Xstep, Z, δ, I_b, hdecode, hstk]
            | cons inSize xs5 =>
              cases xs5 with
              | nil =>
                simp [Xstep, Z, δ, I_b, hdecode, hstk]
              | cons outOffset xs6 =>
                cases xs6 with
                | nil =>
                  simp [Xstep, Z, δ, I_b, hdecode, hstk]
                | cons outSize t =>
      simp [Xstep, Z, δ, I_b, hdecode]
      have hnot_underflow : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 7 := by
        omega
      simp [hstk]
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .CALL
      · simp [hmem, hnot_underflow]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .CALL)
        let gasState := {s with machineState.gasAvailable := gasAvailable'}
        let gasCost :=
          Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value gas
            s.accountMap gasState.machineState s.substate
        by_cases hgas : gasAvailable'.toNat < gasCost
        · have hgas_cond := hgas
          simp [gasAvailable', gasState, gasCost, hstk] at hgas_cond
          simp [gasAvailable', gasState, gasCost, hgas_cond, C', hstk, hnot_underflow]
        ·
          have hgas_cond := hgas
          simp [gasAvailable', gasState, gasCost, hstk] at hgas_cond
          have hgas_not :
              ¬ (s.machineState.gasAvailable.natSub (memoryExpansionCost s .CALL)).toNat <
                Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value gas
                  s.accountMap
                  { pc := s.machineState.pc,
                    stack := gas :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t,
                    execLength := s.machineState.execLength,
                    gasAvailable := s.machineState.gasAvailable.natSub (memoryExpansionCost s .CALL),
                    activeWords := s.machineState.activeWords, memory := s.machineState.memory,
                    returnData := s.machineState.returnData, H_return := s.machineState.H_return }
                  s.substate := by
            omega
          by_cases hoverflow : 1024 < t.length + 1
          · simp [gasAvailable', gasState, gasCost, hgas_not, C', hstk, α, hoverflow, hnot_underflow,
              Operation.isCreate]
          ·
            by_cases hstatic : ¬s.executionEnv.perm ∧ value ≠ ⟨0⟩
            · have hstatic_cond : s.executionEnv.perm = false ∧ ¬ value = ({ val := 0 } : UInt256) := by
                simpa using hstatic
              simp [gasAvailable', gasState, gasCost, hgas_not, hstatic_cond, C', hstk, α, hoverflow, hnot_underflow,
                Operation.isCreate]
            · have hstatic_not : ¬ (s.executionEnv.perm = false ∧ ¬ value = ({ val := 0 } : UInt256)) := by
                simpa using hstatic
              have hdepth_eq :
                  (s.executionEnv.depth.val = 1024) = (s.executionEnv.depth = (1024 : Fin 1025)) := by
                apply propext
                constructor
                · intro h
                  ext
                  simpa using h
                · intro h
                  rw [h]
                  rfl
              simp [gasAvailable', gasState, gasCost, hgas_not, hstatic_not, C', hstk, α, hoverflow, hnot_underflow,
                Operation.isCreate, bind, Except.bind]
              unfold step
              simp [Id.run, Stack.pop7, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                Ethereum.State.addAccessedAccount, writeBytes, call, liftM, bind, Bind.bind,
                Except.bind, Except.pure, Pure.pure, MonadLift.monadLift]
              simp [Stack.push, UInt256_ofNat_1, hdepth_eq]

theorem step_call' : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CALL, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | gas :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t =>
        let memoryCost := memoryExpansionCost s .CALL
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
          let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
          let gasState := {s with machineState.gasAvailable := gasAvailable'}
          let gasCost :=
            Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value gas
              s.accountMap gasState.machineState s.substate
          if gasAvailable'.toNat < gasCost then .error .OutOfGass
          else if s.machineState.stack.length - 7 + 1 > 1024 then .error .StackOverflow
          else if ¬ s.executionEnv.perm ∧ value ≠ ⟨0⟩ then .error .StaticModeViolation
          else
            let tAddr := AccountAddress.ofUInt256 target
            let source := AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner)
            let recipient := tAddr
            let Iₐ := s.executionEnv.codeOwner
            let σ := s.accountMap
            let Iₑ := s.executionEnv.depth
            let callMachineState := {gasState.machineState with execLength := s.machineState.execLength + 1}
            let callgas := Ccallgas tAddr recipient value gas σ callMachineState s.substate
            let i := s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let Astar := s.addAccessedAccount tAddr |>.substate
            let (cA, σ', g', A', z, o) :=
              if value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 then
                Θ s.executionEnv.blobVersionedHashes
                  (createdAccounts := s.createdAccounts) (genesisBlockHeader := s.genesisBlockHeader)
                  (blocks := s.blocks) (σ := σ) (σ₀ := s.σ₀) (A := Astar)
                  (s := source) (o := s.executionEnv.sender) (r := recipient)
                  (c := toExecute σ tAddr) (g := .ofNat callgas) (p := .ofNat s.executionEnv.gasPrice)
                  (v := value) (v' := value) (d := i) (e := Iₑ + 1)
                  (H := s.executionEnv.header) (w := s.executionEnv.perm)
              else
                (s.createdAccounts, s.accountMap, .ofNat callgas, Astar, false, .empty)
            let n : UInt256 := min outSize (.ofNat o.size)
            let x : UInt256 :=
              if (!z) || value > (σ.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ||
                  s.executionEnv.depth == 1024 then ⟨0⟩ else ⟨1⟩
            .ok ({ s with
                accountMap := σ'
                substate := A'
                machineState :=
                { s.machineState with
                  stack := x :: t
                  pc := s.machineState.pc + ⟨1⟩
                  memory := o.write 0 s.machineState.memory outOffset.toNat n.toNat
                  returnData := o
                  gasAvailable := gasAvailable'.natSub (gasCost - g'.toNat)
                  execLength := s.machineState.execLength + 1
                  activeWords :=
                    let m := MachineState.M s.machineState.activeWords.toNat inOffset.toNat inSize.toNat
                    .ofNat <| MachineState.M m outOffset.toNat outSize.toNat }
                createdAccounts := cA
              }, .none)
      | _ => .error .StackUnderflow
:= by
    exact step_call

theorem step_callcode : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CALLCODE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | gas :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t =>
        let memoryCost := memoryExpansionCost s .CALLCODE
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
          let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
          let gasState := {s with machineState.gasAvailable := gasAvailable'}
          let gasCost :=
            Ccall (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner value gas
              s.accountMap gasState.machineState s.substate
          if gasAvailable'.toNat < gasCost then .error .OutOfGass
          else if s.machineState.stack.length - 7 + 1 > 1024 then .error .StackOverflow
          else
            let tAddr := AccountAddress.ofUInt256 target
            let source := AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner)
            let recipient := AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner)
            let Iₐ := s.executionEnv.codeOwner
            let σ := s.accountMap
            let Iₑ := s.executionEnv.depth
            let callMachineState := {gasState.machineState with execLength := s.machineState.execLength + 1}
            let callgas := Ccallgas tAddr recipient value gas σ callMachineState s.substate
            let i := s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let Astar := s.addAccessedAccount tAddr |>.substate
            let (cA, σ', g', A', z, o) :=
              if value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 then
                Θ s.executionEnv.blobVersionedHashes
                  (createdAccounts := s.createdAccounts) (genesisBlockHeader := s.genesisBlockHeader)
                  (blocks := s.blocks) (σ := σ) (σ₀ := s.σ₀) (A := Astar)
                  (s := source) (o := s.executionEnv.sender) (r := recipient)
                  (c := toExecute σ tAddr) (g := .ofNat callgas) (p := .ofNat s.executionEnv.gasPrice)
                  (v := value) (v' := value) (d := i) (e := Iₑ + 1)
                  (H := s.executionEnv.header) (w := s.executionEnv.perm)
              else
                (s.createdAccounts, s.accountMap, .ofNat callgas, Astar, false, .empty)
            let n : UInt256 := min outSize (.ofNat o.size)
            let x : UInt256 :=
              if (!z) || value > (σ.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ||
                  s.executionEnv.depth == 1024 then ⟨0⟩ else ⟨1⟩
            .ok ({ s with
                accountMap := σ'
                substate := A'
                machineState :=
                { s.machineState with
                  stack := x :: t
                  pc := s.machineState.pc + ⟨1⟩
                  memory := o.write 0 s.machineState.memory outOffset.toNat n.toNat
                  returnData := o
                  gasAvailable := gasAvailable'.natSub (gasCost - g'.toNat)
                  execLength := s.machineState.execLength + 1
                  activeWords :=
                    let m := MachineState.M s.machineState.activeWords.toNat inOffset.toNat inSize.toNat
                    .ofNat <| MachineState.M m outOffset.toNat outSize.toNat }
                createdAccounts := cA
              }, .none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdecode
    cases hstk : s.machineState.stack with
    | nil =>
      simp [Xstep, Z, δ, I_b, hdecode, hstk]
    | cons gas xs1 =>
      cases xs1 with
      | nil =>
        simp [Xstep, Z, δ, I_b, hdecode, hstk]
      | cons target xs2 =>
        cases xs2 with
        | nil =>
          simp [Xstep, Z, δ, I_b, hdecode, hstk]
        | cons value xs3 =>
          cases xs3 with
          | nil =>
            simp [Xstep, Z, δ, I_b, hdecode, hstk]
          | cons inOffset xs4 =>
            cases xs4 with
            | nil =>
              simp [Xstep, Z, δ, I_b, hdecode, hstk]
            | cons inSize xs5 =>
              cases xs5 with
              | nil =>
                simp [Xstep, Z, δ, I_b, hdecode, hstk]
              | cons outOffset xs6 =>
                cases xs6 with
                | nil =>
                  simp [Xstep, Z, δ, I_b, hdecode, hstk]
                | cons outSize t =>
      simp [Xstep, Z, δ, I_b, hdecode]
      have hnot_underflow : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 7 := by
        omega
      simp [hstk]
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .CALLCODE
      · simp [hmem, hnot_underflow]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .CALLCODE)
        let gasState := {s with machineState.gasAvailable := gasAvailable'}
        let gasCost :=
          Ccall (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner value gas
            s.accountMap gasState.machineState s.substate
        by_cases hgas : gasAvailable'.toNat < gasCost
        · have hgas_cond := hgas
          simp [gasAvailable', gasState, gasCost, hstk] at hgas_cond
          simp [gasAvailable', gasState, gasCost, hgas_cond, C', hstk, hnot_underflow]
        ·
          have hgas_cond := hgas
          simp [gasAvailable', gasState, gasCost, hstk] at hgas_cond
          have hgas_not :
              ¬ (s.machineState.gasAvailable.natSub (memoryExpansionCost s .CALLCODE)).toNat <
                Ccall (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner value gas
                  s.accountMap
                  { pc := s.machineState.pc,
                    stack := gas :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t,
                    execLength := s.machineState.execLength,
                    gasAvailable := s.machineState.gasAvailable.natSub (memoryExpansionCost s .CALLCODE),
                    activeWords := s.machineState.activeWords, memory := s.machineState.memory,
                    returnData := s.machineState.returnData, H_return := s.machineState.H_return }
                  s.substate := by
            omega
          by_cases hoverflow : 1024 < t.length + 1
          · simp [gasAvailable', gasState, gasCost, hgas_not, C', hstk, α, hoverflow, hnot_underflow,
              Operation.isCreate]
          ·
            have hdepth_eq :
                (s.executionEnv.depth.val = 1024) = (s.executionEnv.depth = (1024 : Fin 1025)) := by
              apply propext
              constructor
              · intro h
                ext
                simpa using h
              · intro h
                rw [h]
                rfl
            simp [gasAvailable', gasState, gasCost, hgas_not, C', hstk, α, hoverflow, hnot_underflow,
              Operation.isCreate, bind, Except.bind]
            unfold step
            simp [Id.run, Stack.pop7, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              Ethereum.State.addAccessedAccount, writeBytes, call, liftM, bind, Bind.bind,
              Except.bind, Except.pure, Pure.pure, MonadLift.monadLift]
            simp [Stack.push, UInt256_ofNat_1, hdepth_eq]

theorem step_delegatecall : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DELEGATECALL, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | gas :: target :: inOffset :: inSize :: outOffset :: outSize :: t =>
        let memoryCost := memoryExpansionCost s .DELEGATECALL
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
          let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
          let gasState := {s with machineState.gasAvailable := gasAvailable'}
          let value := (⟨0⟩ : UInt256)
          let gasCost :=
            Ccall (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner value gas
              s.accountMap gasState.machineState s.substate
          if gasAvailable'.toNat < gasCost then .error .OutOfGass
          else if s.machineState.stack.length - 6 + 1 > 1024 then .error .StackOverflow
          else
            let tAddr := AccountAddress.ofUInt256 target
            let source := AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.source)
            let recipient := AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner)
            let value' := s.executionEnv.weiValue
            let Iₐ := s.executionEnv.codeOwner
            let σ := s.accountMap
            let Iₑ := s.executionEnv.depth
            let callMachineState := {gasState.machineState with execLength := s.machineState.execLength + 1}
            let callgas := Ccallgas tAddr recipient value gas σ callMachineState s.substate
            let i := s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let Astar := s.addAccessedAccount tAddr |>.substate
            let (cA, σ', g', A', z, o) :=
              if value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 then
                Θ s.executionEnv.blobVersionedHashes
                  (createdAccounts := s.createdAccounts) (genesisBlockHeader := s.genesisBlockHeader)
                  (blocks := s.blocks) (σ := σ) (σ₀ := s.σ₀) (A := Astar)
                  (s := source) (o := s.executionEnv.sender) (r := recipient)
                  (c := toExecute σ tAddr) (g := .ofNat callgas) (p := .ofNat s.executionEnv.gasPrice)
                  (v := value) (v' := value') (d := i) (e := Iₑ + 1)
                  (H := s.executionEnv.header) (w := s.executionEnv.perm)
              else
                (s.createdAccounts, s.accountMap, .ofNat callgas, Astar, false, .empty)
            let n : UInt256 := min outSize (.ofNat o.size)
            let x : UInt256 :=
              if (!z) || value > (σ.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ||
                  s.executionEnv.depth == 1024 then ⟨0⟩ else ⟨1⟩
            .ok ({ s with
                accountMap := σ'
                substate := A'
                machineState :=
                { s.machineState with
                  stack := x :: t
                  pc := s.machineState.pc + ⟨1⟩
                  memory := o.write 0 s.machineState.memory outOffset.toNat n.toNat
                  returnData := o
                  gasAvailable := gasAvailable'.natSub (gasCost - g'.toNat)
                  execLength := s.machineState.execLength + 1
                  activeWords :=
                    let m := MachineState.M s.machineState.activeWords.toNat inOffset.toNat inSize.toNat
                    .ofNat <| MachineState.M m outOffset.toNat outSize.toNat }
                createdAccounts := cA
              }, .none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdecode
    cases hstk : s.machineState.stack with
    | nil =>
      simp [Xstep, Z, δ, I_b, hdecode, hstk]
    | cons gas xs1 =>
      cases xs1 with
      | nil =>
        simp [Xstep, Z, δ, I_b, hdecode, hstk]
      | cons target xs2 =>
        cases xs2 with
        | nil =>
          simp [Xstep, Z, δ, I_b, hdecode, hstk]
        | cons inOffset xs3 =>
          cases xs3 with
          | nil =>
            simp [Xstep, Z, δ, I_b, hdecode, hstk]
          | cons inSize xs4 =>
            cases xs4 with
            | nil =>
              simp [Xstep, Z, δ, I_b, hdecode, hstk]
            | cons outOffset xs5 =>
              cases xs5 with
              | nil =>
                simp [Xstep, Z, δ, I_b, hdecode, hstk]
              | cons outSize t =>
      simp [Xstep, Z, δ, I_b, hdecode]
      have hnot_underflow : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 < 6 := by
        omega
      simp [hstk]
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .DELEGATECALL
      · simp [hmem, hnot_underflow]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .DELEGATECALL)
        let gasState := {s with machineState.gasAvailable := gasAvailable'}
        let value := (⟨0⟩ : UInt256)
        let gasCost :=
          Ccall (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner value gas
            s.accountMap gasState.machineState s.substate
        by_cases hgas : gasAvailable'.toNat < gasCost
        · have hgas_cond := hgas
          simp [gasAvailable', gasState, value, gasCost, hstk] at hgas_cond
          simp [gasAvailable', gasState, value, gasCost, hgas_cond, C', hstk, hnot_underflow]
        ·
          have hgas_cond := hgas
          simp [gasAvailable', gasState, value, gasCost, hstk] at hgas_cond
          have hgas_not :
              ¬ (s.machineState.gasAvailable.natSub (memoryExpansionCost s .DELEGATECALL)).toNat <
                Ccall (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner ({ val := 0 } : UInt256) gas
                  s.accountMap
                  { pc := s.machineState.pc,
                    stack := gas :: target :: inOffset :: inSize :: outOffset :: outSize :: t,
                    execLength := s.machineState.execLength,
                    gasAvailable := s.machineState.gasAvailable.natSub (memoryExpansionCost s .DELEGATECALL),
                    activeWords := s.machineState.activeWords, memory := s.machineState.memory,
                    returnData := s.machineState.returnData, H_return := s.machineState.H_return }
                  s.substate := by
            omega
          by_cases hoverflow : 1024 < t.length + 1
          · simp [gasAvailable', gasState, value, gasCost, hgas_not, C', hstk, α, hoverflow, hnot_underflow,
              Operation.isCreate]
          ·
            have hdepth_eq :
                (s.executionEnv.depth.val = 1024) = (s.executionEnv.depth = (1024 : Fin 1025)) := by
              apply propext
              constructor
              · intro h
                ext
                simpa using h
              · intro h
                rw [h]
                rfl
            simp [gasAvailable', gasState, value, gasCost, hgas_not, C', hstk, α, hoverflow, hnot_underflow,
              Operation.isCreate, bind, Except.bind]
            unfold step
            simp [Id.run, Stack.pop6, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              Ethereum.State.addAccessedAccount, writeBytes, call, liftM, bind, Bind.bind,
              Except.bind, Except.pure, Pure.pure, MonadLift.monadLift]
            simp [Stack.push, UInt256_ofNat_1, hdepth_eq]

theorem step_staticcall : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.STATICCALL, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | gas :: target :: inOffset :: inSize :: outOffset :: outSize :: t =>
        let memoryCost := memoryExpansionCost s .STATICCALL
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
          let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
          let gasState := {s with machineState.gasAvailable := gasAvailable'}
          let value := (⟨0⟩ : UInt256)
          let gasCost :=
            Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value gas
              s.accountMap gasState.machineState s.substate
          if gasAvailable'.toNat < gasCost then .error .OutOfGass
          else if s.machineState.stack.length - 6 + 1 > 1024 then .error .StackOverflow
          else
            let tAddr := AccountAddress.ofUInt256 target
            let source := AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner)
            let recipient := tAddr
            let Iₐ := s.executionEnv.codeOwner
            let σ := s.accountMap
            let Iₑ := s.executionEnv.depth
            let callMachineState := {gasState.machineState with execLength := s.machineState.execLength + 1}
            let callgas := Ccallgas tAddr recipient value gas σ callMachineState s.substate
            let i := s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let Astar := s.addAccessedAccount tAddr |>.substate
            let (cA, σ', g', A', z, o) :=
              if value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 then
                Θ s.executionEnv.blobVersionedHashes
                  (createdAccounts := s.createdAccounts) (genesisBlockHeader := s.genesisBlockHeader)
                  (blocks := s.blocks) (σ := σ) (σ₀ := s.σ₀) (A := Astar)
                  (s := source) (o := s.executionEnv.sender) (r := recipient)
                  (c := toExecute σ tAddr) (g := .ofNat callgas) (p := .ofNat s.executionEnv.gasPrice)
                  (v := value) (v' := value) (d := i) (e := Iₑ + 1)
                  (H := s.executionEnv.header) (w := false)
              else
                (s.createdAccounts, s.accountMap, .ofNat callgas, Astar, false, .empty)
            let n : UInt256 := min outSize (.ofNat o.size)
            let x : UInt256 :=
              if (!z) || value > (σ.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ||
                  s.executionEnv.depth == 1024 then ⟨0⟩ else ⟨1⟩
            .ok ({ s with
                accountMap := σ'
                substate := A'
                machineState :=
                { s.machineState with
                  stack := x :: t
                  pc := s.machineState.pc + ⟨1⟩
                  memory := o.write 0 s.machineState.memory outOffset.toNat n.toNat
                  returnData := o
                  gasAvailable := gasAvailable'.natSub (gasCost - g'.toNat)
                  execLength := s.machineState.execLength + 1
                  activeWords :=
                    let m := MachineState.M s.machineState.activeWords.toNat inOffset.toNat inSize.toNat
                    .ofNat <| MachineState.M m outOffset.toNat outSize.toNat }
                createdAccounts := cA
              }, .none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdecode
    cases hstk : s.machineState.stack with
    | nil =>
      simp [Xstep, Z, δ, I_b, hdecode, hstk]
    | cons gas xs1 =>
      cases xs1 with
      | nil =>
        simp [Xstep, Z, δ, I_b, hdecode, hstk]
      | cons target xs2 =>
        cases xs2 with
        | nil =>
          simp [Xstep, Z, δ, I_b, hdecode, hstk]
        | cons inOffset xs3 =>
          cases xs3 with
          | nil =>
            simp [Xstep, Z, δ, I_b, hdecode, hstk]
          | cons inSize xs4 =>
            cases xs4 with
            | nil =>
              simp [Xstep, Z, δ, I_b, hdecode, hstk]
            | cons outOffset xs5 =>
              cases xs5 with
              | nil =>
                simp [Xstep, Z, δ, I_b, hdecode, hstk]
              | cons outSize t =>
      simp [Xstep, Z, δ, I_b, hdecode]
      have hnot_underflow : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 < 6 := by
        omega
      simp [hstk]
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .STATICCALL
      · simp [hmem, hnot_underflow]
      · simp [hmem]
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .STATICCALL)
        let gasState := {s with machineState.gasAvailable := gasAvailable'}
        let value := (⟨0⟩ : UInt256)
        let gasCost :=
          Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value gas
            s.accountMap gasState.machineState s.substate
        by_cases hgas : gasAvailable'.toNat < gasCost
        · have hgas_cond := hgas
          simp [gasAvailable', gasState, value, gasCost, hstk] at hgas_cond
          simp [gasAvailable', gasState, value, gasCost, hgas_cond, C', hstk, hnot_underflow]
        ·
          have hgas_cond := hgas
          simp [gasAvailable', gasState, value, gasCost, hstk] at hgas_cond
          have hgas_not :
              ¬ (s.machineState.gasAvailable.natSub (memoryExpansionCost s .STATICCALL)).toNat <
                Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) ({ val := 0 } : UInt256) gas
                  s.accountMap
                  { pc := s.machineState.pc,
                    stack := gas :: target :: inOffset :: inSize :: outOffset :: outSize :: t,
                    execLength := s.machineState.execLength,
                    gasAvailable := s.machineState.gasAvailable.natSub (memoryExpansionCost s .STATICCALL),
                    activeWords := s.machineState.activeWords, memory := s.machineState.memory,
                    returnData := s.machineState.returnData, H_return := s.machineState.H_return }
                  s.substate := by
            omega
          by_cases hoverflow : 1024 < t.length + 1
          · simp [gasAvailable', gasState, value, gasCost, hgas_not, C', hstk, α, hoverflow, hnot_underflow,
              Operation.isCreate]
          ·
            have hdepth_eq :
                (s.executionEnv.depth.val = 1024) = (s.executionEnv.depth = (1024 : Fin 1025)) := by
              apply propext
              constructor
              · intro h
                ext
                simpa using h
              · intro h
                rw [h]
                rfl
            simp [gasAvailable', gasState, value, gasCost, hgas_not, C', hstk, α, hoverflow, hnot_underflow,
              Operation.isCreate, bind, Except.bind]
            unfold step
            simp [Id.run, Stack.pop6, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              Ethereum.State.addAccessedAccount, writeBytes, call, liftM, bind, Bind.bind,
              Except.bind, Except.pure, Pure.pure, MonadLift.monadLift]
            simp [Stack.push, UInt256_ofNat_1, hdepth_eq]

theorem step_create : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CREATE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | value :: offset :: size :: t =>
        let memoryCost := memoryExpansionCost s .CREATE
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let gasCost := GasConstants.Gcreate + R size.toNat
        if gasAvailable'.toNat < gasCost then .error .OutOfGass
        else if s.machineState.stack.length - 3 + 1 > 1024 then .error .StackOverflow
        else if ¬ s.executionEnv.perm then .error .StaticModeViolation
        else if size > ⟨49152⟩ then .error .OutOfGass
        else
        let createState :=
          {s with
            machineState.gasAvailable := gasAvailable'.natSub gasCost
            machineState.execLength := s.machineState.execLength + 1}
        let initCode := createState.machineState.memory.readWithPadding offset.toNat size.toNat
        let Iₐ := createState.executionEnv.codeOwner
        let Iₒ := createState.executionEnv.sender
        let Iₑ := createState.executionEnv.depth
        let σ := createState.accountMap
        let σ_Iₐ : Account := σ.find? Iₐ |>.getD default
        let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
        let createResult :=
          if σ_Iₐ.nonce.toNat ≥ 2^64 - 1 then
            (0, createState, UInt256.ofNat (L createState.machineState.gasAvailable.toNat), false, ByteArray.empty)
          else
            if hDepth : value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ initCode.size ≤ 49152 then
              let (a, cA, σ', g', A', z, o) :=
                Lambda createState.executionEnv.blobVersionedHashes createState.createdAccounts
                  createState.genesisBlockHeader createState.blocks σStar createState.σ₀ createState.substate
                  Iₐ Iₒ (UInt256.ofNat (L createState.machineState.gasAvailable.toNat))
                  (UInt256.ofNat createState.executionEnv.gasPrice) value initCode
                  ⟨createState.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩ none
                  createState.executionEnv.header createState.executionEnv.perm
              (a, {createState with accountMap := σ', substate := A', createdAccounts := cA}, g', z, o)
            else
              (0, createState, UInt256.ofNat (L createState.machineState.gasAvailable.toNat), false, ByteArray.empty)
        let (a, state', g', z, o) := createResult
        let balance := σ.find? Iₐ |>.option ⟨0⟩ (·.balance)
        let x : UInt256 := if z = false ∨ Iₑ = 1024 ∨ value > balance ∨ initCode.size > 49152 then ⟨0⟩ else UInt256.ofNat a
        let newReturnData : ByteArray := if z then .empty else o
        if createState.machineState.gasAvailable.toNat + g'.toNat < L createState.machineState.gasAvailable.toNat then .error .OutOfGass
        else
        .ok ({state' with
                  machineState.stack := x :: t
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M createState.machineState.activeWords.toNat offset.toNat size.toNat)
                  machineState.returnData := newReturnData
                  machineState.gasAvailable :=
                    (createState.machineState.gasAvailable.natSub 
                      (L createState.machineState.gasAvailable.toNat + g'.toNat))
                  machineState.pc := createState.machineState.pc + ⟨1⟩
                  executionEnv := s.executionEnv
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hcreate
    simp [Xstep, Z, δ, I_b, hcreate]
    match hstack : s.machineState.stack with
    | [] =>
      simp
    | value :: [] =>
      simp
    | value :: offset :: [] =>
      simp
    | value :: offset :: size :: t =>
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
      have hnot_underflow : ¬ t.length + 1 + 1 + 1 < 3 := by
        omega
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .CREATE
      ·
        have hmem' :
            s.machineState.gasAvailable.toNat <
              Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat)) -
                Cₘ s.machineState.activeWords := by
          simpa [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hmem
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack, hnot_underflow, hmem']
      ·
        have hmem' :
            ¬s.machineState.gasAvailable.toNat <
              Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat)) -
                Cₘ s.machineState.activeWords := by
          simpa [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hmem
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .CREATE)
        let gasCost := GasConstants.Gcreate + R size.toNat
        by_cases hgas : gasAvailable'.toNat < gasCost
        ·
          have hgas' : (s.machineState.gasAvailable.natSub (memoryExpansionCost s .CREATE)).toNat <
              GasConstants.Gcreate + R size.toNat := by
            simpa [gasAvailable', gasCost] using hgas
          have hgas'' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gcreate + R size.toNat := by
            simpa [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas'
          simp [gasAvailable', gasCost, memoryExpansionCost, memoryExpansionCost.μᵢ',
            hmem', hgas', hgas'', C', hstack, hnot_underflow]
        ·
          have hgas' : ¬ (s.machineState.gasAvailable.natSub (memoryExpansionCost s .CREATE)).toNat <
              GasConstants.Gcreate + R size.toNat := by
            simpa [gasAvailable', gasCost] using hgas
          have hgas'' :
              ¬(s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gcreate + R size.toNat := by
            simpa [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas'
          by_cases hoverflow : 1024 < t.length + 1
          ·
            have hoverflow' : s.machineState.stack.length - 3 + 1 > 1024 := by
              simpa [hstack] using hoverflow
            simp [gasAvailable', gasCost, memoryExpansionCost, memoryExpansionCost.μᵢ',
              hmem', hgas', hgas'', hoverflow, hoverflow', C', hstack, hnot_underflow, α]
          ·
            have hoverflow' : ¬s.machineState.stack.length - 3 + 1 > 1024 := by
              simpa [hstack] using hoverflow
            by_cases hperm : s.executionEnv.perm = false
            · simp [gasAvailable', gasCost, memoryExpansionCost, memoryExpansionCost.μᵢ',
                hmem', hgas', hgas'', hoverflow, hoverflow', hperm, C', hstack, hnot_underflow, α]
            ·
              have hperm_true : s.executionEnv.perm = true := by
                cases hp : s.executionEnv.perm with
                | false => exact False.elim (hperm hp)
                | true => rfl
              by_cases hsize : size > (⟨49152⟩ : UInt256)
              · simp [gasAvailable', gasCost, memoryExpansionCost, memoryExpansionCost.μᵢ',
                  hmem', hgas', hgas'', hoverflow, hoverflow', hperm, hperm_true, hsize, C', hstack, hnot_underflow,
                  Operation.isCreate, α]
              ·
                let createState : State :=
                  {s with
                    machineState.gasAvailable := gasAvailable'.natSub gasCost
                    machineState.execLength := s.machineState.execLength + 1}
                have hdepth_eq {hDepth : value ≤
                    (((createState.accountMap).find? createState.executionEnv.codeOwner).option ⟨0⟩ fun x => x.balance) ∧
                    createState.executionEnv.depth < 1024 ∧
                    (createState.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152} :
                    (⟨createState.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩ : Fin 1025) =
                      createState.executionEnv.depth + 1 := by
                  ext
                  simp [Fin.val_add, Fin.val_one]
                  omega
                simp [gasAvailable', gasCost, memoryExpansionCost, memoryExpansionCost.μᵢ',
                  hmem', hgas', hgas'', hoverflow, hoverflow', hperm, hperm_true, hsize, C', hstack,
                  hnot_underflow, Operation.isCreate, bind, Except.bind, α]
                unfold step
                let initCode := createState.machineState.memory.readWithPadding offset.toNat size.toNat
                let Iₐ := createState.executionEnv.codeOwner
                let Iₒ := createState.executionEnv.sender
                let σ := createState.accountMap
                let σ_Iₐ : Account := σ.find? Iₐ |>.getD default
                let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
                let createResult :=
                  if σ_Iₐ.nonce.toNat ≥ 2^64 - 1 then
                    (0, createState, UInt256.ofNat (L createState.machineState.gasAvailable.toNat), false, ByteArray.empty)
                  else
                    if hDepth : value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧
                        createState.executionEnv.depth < 1024 ∧ initCode.size ≤ 49152 then
                      let (a, cA, σ', g', A', z, o) :=
                        Lambda createState.executionEnv.blobVersionedHashes createState.createdAccounts
                          createState.genesisBlockHeader createState.blocks σStar createState.σ₀ createState.substate
                          Iₐ Iₒ (UInt256.ofNat (L createState.machineState.gasAvailable.toNat))
                          (UInt256.ofNat createState.executionEnv.gasPrice) value initCode
                          ⟨createState.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩ none
                          createState.executionEnv.header createState.executionEnv.perm
                      (a, {createState with accountMap := σ', substate := A', createdAccounts := cA}, g', z, o)
                    else
                      (0, createState, UInt256.ofNat (L createState.machineState.gasAvailable.toNat), false, ByteArray.empty)
                let g' := createResult.2.2.1
                by_cases hnonce : σ_Iₐ.nonce.toNat ≥ 2^64 - 1
                ·
                  have hnonce_expanded :
                      18446744073709551615 ≤
                        ((Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner).getD default).nonce.toNat := by
                    simpa [σ_Iₐ, σ, Iₐ, createState] using hnonce
                  by_cases hrefund :
                      (createState.machineState.gasAvailable + g').toNat <
                        L createState.machineState.gasAvailable.toNat
                  ·
                    have hrefund_expanded := hrefund
                    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                      createState, initCode, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                      hnonce, hnonce_expanded, hperm_true] at hrefund_expanded
                    simp [Id.run, Stack.pop3, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      Except.bind,
                      memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                      createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, Iₐ, Iₒ, σ, σ_Iₐ,
                      σStar, createResult, g', hnonce, hnonce_expanded, hrefund, hrefund_expanded]
                    rfl
                  ·
                    have hrefund_expanded := hrefund
                    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                      createState, initCode, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                      hnonce, hnonce_expanded, hperm_true] at hrefund_expanded
                    have hrefund_expanded_not := not_lt.mpr hrefund_expanded
                    simp [Id.run, Stack.pop3, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      Except.bind,
                      memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                      createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, Iₐ, Iₒ, σ, σ_Iₐ,
                      σStar, createResult, g', hnonce, hnonce_expanded, hrefund, hrefund_expanded,
                      hrefund_expanded_not]
                    rfl
                ·
                  have hnonce_expanded :
                      ¬ 18446744073709551615 ≤
                        ((Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner).getD default).nonce.toNat := by
                    simpa [σ_Iₐ, σ, Iₐ, createState] using hnonce
                  by_cases hDepth :
                      value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧
                        createState.executionEnv.depth < 1024 ∧ initCode.size ≤ 49152
                  ·
                    have hDepth_expanded :
                        value ≤
                            Option.option { val := 0 } (fun x => x.balance)
                              (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner) ∧
                          s.executionEnv.depth < 1024 ∧
                            (s.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152 := by
                      simpa [σ, Iₐ, initCode, createState] using hDepth
                    by_cases hrefund :
                        (createState.machineState.gasAvailable + g').toNat <
                          L createState.machineState.gasAvailable.toNat
                    ·
                      have hrefund_expanded := hrefund
                      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, initCode, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                        hnonce, hnonce_expanded, hDepth, hDepth_expanded, hdepth_eq, hperm_true] at hrefund_expanded
                      simp [Id.run, Stack.pop3, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                        Except.bind,
                        memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, Iₐ, Iₒ, σ, σ_Iₐ,
                        σStar, createResult, g', hnonce, hnonce_expanded, hDepth, hDepth_expanded, hrefund,
                        hrefund_expanded]
                      conv_lhs =>
                        simp [bind, Except.bind]
                      have hDepth_lt := hDepth_expanded.2.1
                      have hDepth_lt' : (↑s.executionEnv.depth : Nat) < 1024 := by
                        simpa using hDepth_lt
                      simp [hDepth_lt', hrefund_expanded]
                    ·
                      have hrefund_expanded := hrefund
                      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, initCode, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                        hnonce, hnonce_expanded, hDepth, hDepth_expanded, hdepth_eq, hperm_true] at hrefund_expanded
                      simp [Id.run, Stack.pop3, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                        Except.bind,
                        memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, Iₐ, Iₒ, σ, σ_Iₐ,
                        σStar, createResult, g', hnonce, hnonce_expanded, hDepth, hDepth_expanded, hrefund,
                        hrefund_expanded]
                      have hrefund_expanded_not := not_lt.mpr hrefund_expanded
                      have hDepth_lt := hDepth_expanded.2.1
                      have hDepth_lt' : (↑s.executionEnv.depth : Nat) < 1024 := by
                        simpa using hDepth_lt
                      have hDepth_ne : s.executionEnv.depth ≠ 1024 := by
                        omega
                      have hDepth_val_ne : (↑s.executionEnv.depth : Nat) ≠ 1024 := by
                        omega
                      simp [hDepth_expanded, hDepth_lt', hDepth_ne, hDepth_val_ne, hrefund_expanded_not, Stack.push]
                  ·
                    have hDepth_expanded :
                        ¬ (value ≤
                            Option.option { val := 0 } (fun x => x.balance)
                              (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner) ∧
                          s.executionEnv.depth < 1024 ∧
                            (s.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152) := by
                      simpa [σ, Iₐ, initCode, createState] using hDepth
                    have hDepth_expanded_nat :
                        ¬ (value ≤
                            Option.option { val := 0 } (fun x => x.balance)
                              (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner) ∧
                          (↑s.executionEnv.depth : Nat) < 1024 ∧
                            (s.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152) := by
                      intro h
                      exact hDepth_expanded ⟨h.1, by simpa using h.2.1, h.2.2⟩
                    by_cases hrefund :
                        (createState.machineState.gasAvailable + g').toNat <
                          L createState.machineState.gasAvailable.toNat
                    ·
                      have hrefund_expanded := hrefund
                      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, initCode, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                        hnonce, hnonce_expanded, hDepth, hDepth_expanded, hDepth_expanded_nat, hperm_true] at hrefund_expanded
                      simp [Id.run, Stack.pop3, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                        Except.bind,
                        memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, Iₐ, Iₒ, σ, σ_Iₐ,
                        σStar, createResult, g', hnonce, hnonce_expanded, hDepth, hDepth_expanded, hrefund,
                        hrefund_expanded]
                      conv_lhs =>
                        simp [bind, Except.bind]
                      simp [hDepth_expanded, hDepth_expanded_nat, hrefund_expanded]
                    ·
                      have hrefund_expanded := hrefund
                      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, initCode, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                        hnonce, hnonce_expanded, hDepth, hDepth_expanded, hDepth_expanded_nat, hperm_true] at hrefund_expanded
                      have hrefund_expanded_not := not_lt.mpr hrefund_expanded
                      simp [Id.run, Stack.pop3, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                        Except.bind,
                        memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, Iₐ, Iₒ, σ, σ_Iₐ,
                        σStar, createResult, g', hnonce, hnonce_expanded, hDepth, hDepth_expanded, hrefund,
                        hrefund_expanded, hrefund_expanded_not]
                      simp [hDepth_expanded, hDepth_expanded_nat, hrefund_expanded_not, Stack.push]

theorem step_create2 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.CREATE2, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | value :: offset :: size :: salt :: t =>
        let memoryCost := memoryExpansionCost s .CREATE2
        if s.machineState.gasAvailable.toNat < memoryCost then .error .OutOfGass
        else
        let gasAvailable' := s.machineState.gasAvailable.natSub memoryCost
        let gasCost := GasConstants.Gcreate + GasConstants.Gkeccak256word * ((size.toNat + 31) / 32) + R size.toNat
        if gasAvailable'.toNat < gasCost then .error .OutOfGass
        else if s.machineState.stack.length - 4 + 1 > 1024 then .error .StackOverflow
        else if ¬ s.executionEnv.perm then .error .StaticModeViolation
        else if size > ⟨49152⟩ then .error .OutOfGass
        else
        let createState :=
          {s with
            machineState.gasAvailable := gasAvailable'.natSub gasCost
            machineState.execLength := s.machineState.execLength + 1}
        let initCode := createState.machineState.memory.readWithPadding offset.toNat size.toNat
        let ζ := Ethereum.UInt256.toByteArray salt
        let Iₐ := createState.executionEnv.codeOwner
        let Iₒ := createState.executionEnv.sender
        let Iₑ := createState.executionEnv.depth
        let σ := createState.accountMap
        let σ_Iₐ : Account := σ.find? Iₐ |>.getD default
        let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
        let createResult :=
          if σ_Iₐ.nonce.toNat ≥ 2^64 - 1 then
            (0, createState, UInt256.ofNat (L createState.machineState.gasAvailable.toNat), false, ByteArray.empty)
          else
            if hDepth : value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ initCode.size ≤ 49152 then
              let (a, cA, σ', g', A', z, o) :=
                Lambda createState.executionEnv.blobVersionedHashes createState.createdAccounts
                  createState.genesisBlockHeader createState.blocks σStar createState.σ₀ createState.substate
                  Iₐ Iₒ (UInt256.ofNat (L createState.machineState.gasAvailable.toNat))
                  (UInt256.ofNat createState.executionEnv.gasPrice) value initCode
                  ⟨createState.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩ ζ
                  createState.executionEnv.header createState.executionEnv.perm
              (a, {createState with accountMap := σ', substate := A', createdAccounts := cA}, g', z, o)
            else
              (0, createState, UInt256.ofNat (L createState.machineState.gasAvailable.toNat), false, ByteArray.empty)
        let (a, state', g', z, o) := createResult
        let balance := σ.find? Iₐ |>.option ⟨0⟩ (·.balance)
        let x : UInt256 := if z = false ∨ Iₑ = 1024 ∨ value > balance ∨ initCode.size > 49152 then ⟨0⟩ else UInt256.ofNat a
        let newReturnData : ByteArray := if z then .empty else o
        if (createState.machineState.gasAvailable + g').toNat < L createState.machineState.gasAvailable.toNat then .error .OutOfGass
        else
        .ok ({state' with
                  machineState.stack := x :: t
                  machineState.activeWords :=
                    UInt256.ofNat (MachineState.M createState.machineState.activeWords.toNat offset.toNat size.toNat)
                  machineState.returnData := newReturnData
                  machineState.gasAvailable :=
                    UInt256.ofNat (createState.machineState.gasAvailable.toNat -
                      L createState.machineState.gasAvailable.toNat + g'.toNat)
                  machineState.pc := createState.machineState.pc + ⟨1⟩
                  executionEnv := s.executionEnv
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hcreate
    simp [Xstep, Z, δ, I_b, hcreate]
    match hstack : s.machineState.stack with
    | [] =>
      simp
    | value :: [] =>
      simp
    | value :: offset :: [] =>
      simp
    | value :: offset :: size :: [] =>
      simp
    | value :: offset :: size :: salt :: t =>
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack]
      have hnot_underflow : ¬ t.length + 1 + 1 + 1 + 1 < 4 := by
        omega
      by_cases hmem : s.machineState.gasAvailable.toNat < memoryExpansionCost s .CREATE2
      ·
        have hmem' :
            s.machineState.gasAvailable.toNat <
              Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat)) -
                Cₘ s.machineState.activeWords := by
          simpa [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hmem
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C', hstack, hnot_underflow, hmem']
      ·
        have hmem' :
            ¬s.machineState.gasAvailable.toNat <
              Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat)) -
                Cₘ s.machineState.activeWords := by
          simpa [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hmem
        let gasAvailable' := s.machineState.gasAvailable.natSub (memoryExpansionCost s .CREATE2)
        let gasCost := GasConstants.Gcreate + GasConstants.Gkeccak256word * ((size.toNat + 31) / 32) + R size.toNat
        by_cases hgas : gasAvailable'.toNat < gasCost
        ·
          have hgas' : (s.machineState.gasAvailable.natSub (memoryExpansionCost s .CREATE2)).toNat <
              GasConstants.Gcreate + GasConstants.Gkeccak256word * ((size.toNat + 31) / 32) + R size.toNat := by
            simpa [gasAvailable', gasCost] using hgas
          have hgas'' :
              (s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gcreate + GasConstants.Gkeccak256word * ((size.toNat + 31) / 32) + R size.toNat := by
            simpa [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas'
          simp [gasAvailable', gasCost, memoryExpansionCost, memoryExpansionCost.μᵢ',
            hmem', hgas', hgas'', C', hstack, hnot_underflow]
        ·
          have hgas' : ¬ (s.machineState.gasAvailable.natSub (memoryExpansionCost s .CREATE2)).toNat <
              GasConstants.Gcreate + GasConstants.Gkeccak256word * ((size.toNat + 31) / 32) + R size.toNat := by
            simpa [gasAvailable', gasCost] using hgas
          have hgas'' :
              ¬(s.machineState.gasAvailable -
                    UInt256.ofNat
                      (Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat offset.toNat size.toNat)) -
                        Cₘ s.machineState.activeWords)).toNat <
                GasConstants.Gcreate + GasConstants.Gkeccak256word * ((size.toNat + 31) / 32) + R size.toNat := by
            simpa [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack] using hgas'
          by_cases hoverflow : 1024 < t.length + 1
          ·
            have hoverflow' : s.machineState.stack.length - 4 + 1 > 1024 := by
              simpa [hstack] using hoverflow
            simp [gasAvailable', gasCost, memoryExpansionCost, memoryExpansionCost.μᵢ',
              hmem', hgas', hgas'', hoverflow, hoverflow', C', hstack, hnot_underflow, α]
          ·
            have hoverflow' : ¬s.machineState.stack.length - 4 + 1 > 1024 := by
              simpa [hstack] using hoverflow
            by_cases hperm : s.executionEnv.perm = false
            · simp [gasAvailable', gasCost, memoryExpansionCost, memoryExpansionCost.μᵢ',
                hmem', hgas', hgas'', hoverflow, hoverflow', hperm, C', hstack, hnot_underflow, α]
            ·
              have hperm_true : s.executionEnv.perm = true := by
                cases hp : s.executionEnv.perm with
                | false => exact False.elim (hperm hp)
                | true => rfl
              by_cases hsize : size > (⟨49152⟩ : UInt256)
              · simp [gasAvailable', gasCost, memoryExpansionCost, memoryExpansionCost.μᵢ',
                  hmem', hgas', hgas'', hoverflow, hoverflow', hperm, hperm_true, hsize, C', hstack, hnot_underflow,
                  Operation.isCreate, α]
              ·
                let createState : State :=
                  {s with
                    machineState.gasAvailable := gasAvailable'.natSub gasCost
                    machineState.execLength := s.machineState.execLength + 1}
                have hdepth_eq {hDepth : value ≤
                    (((createState.accountMap).find? createState.executionEnv.codeOwner).option ⟨0⟩ fun x => x.balance) ∧
                    createState.executionEnv.depth < 1024 ∧
                    (createState.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152} :
                    (⟨createState.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩ : Fin 1025) =
                      createState.executionEnv.depth + 1 := by
                  ext
                  simp [Fin.val_add, Fin.val_one]
                  omega
                simp [gasAvailable', gasCost, memoryExpansionCost, memoryExpansionCost.μᵢ',
                  hmem', hgas', hgas'', hoverflow, hoverflow', hperm, hperm_true, hsize, C', hstack,
                  hnot_underflow, Operation.isCreate, bind, Except.bind, α]
                unfold step
                let initCode := createState.machineState.memory.readWithPadding offset.toNat size.toNat
                let ζ := Ethereum.UInt256.toByteArray salt
                let Iₐ := createState.executionEnv.codeOwner
                let Iₒ := createState.executionEnv.sender
                let σ := createState.accountMap
                let σ_Iₐ : Account := σ.find? Iₐ |>.getD default
                let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
                let createResult :=
                  if σ_Iₐ.nonce.toNat ≥ 2^64 - 1 then
                    (0, createState, UInt256.ofNat (L createState.machineState.gasAvailable.toNat), false, ByteArray.empty)
                  else
                    if hDepth : value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧
                        createState.executionEnv.depth < 1024 ∧ initCode.size ≤ 49152 then
                      let (a, cA, σ', g', A', z, o) :=
                        Lambda createState.executionEnv.blobVersionedHashes createState.createdAccounts
                          createState.genesisBlockHeader createState.blocks σStar createState.σ₀ createState.substate
                          Iₐ Iₒ (UInt256.ofNat (L createState.machineState.gasAvailable.toNat))
                          (UInt256.ofNat createState.executionEnv.gasPrice) value initCode
                          ⟨createState.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩ ζ
                          createState.executionEnv.header createState.executionEnv.perm
                      (a, {createState with accountMap := σ', substate := A', createdAccounts := cA}, g', z, o)
                    else
                      (0, createState, UInt256.ofNat (L createState.machineState.gasAvailable.toNat), false, ByteArray.empty)
                let g' := createResult.2.2.1
                by_cases hnonce : σ_Iₐ.nonce.toNat ≥ 2^64 - 1
                ·
                  have hnonce_expanded :
                      18446744073709551615 ≤
                        ((Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner).getD default).nonce.toNat := by
                    simpa [σ_Iₐ, σ, Iₐ, createState] using hnonce
                  by_cases hrefund :
                      (createState.machineState.gasAvailable + g').toNat <
                        L createState.machineState.gasAvailable.toNat
                  ·
                    have hrefund_expanded := hrefund
                    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                      createState, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                      hnonce, hnonce_expanded, hperm_true] at hrefund_expanded
                    simp [Id.run, Stack.pop4, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      Except.bind,
                      memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                      createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ,
                      σStar, createResult, g', hnonce, hnonce_expanded, hrefund, hrefund_expanded]
                    rfl
                  ·
                    have hrefund_expanded := hrefund
                    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                      createState, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                      hnonce, hnonce_expanded, hperm_true] at hrefund_expanded
                    have hrefund_expanded_not := not_lt.mpr hrefund_expanded
                    simp [Id.run, Stack.pop4, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      Except.bind,
                      memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                      createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ,
                      σStar, createResult, g', hnonce, hnonce_expanded, hrefund, hrefund_expanded,
                      hrefund_expanded_not]
                    rfl
                ·
                  have hnonce_expanded :
                      ¬ 18446744073709551615 ≤
                        ((Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner).getD default).nonce.toNat := by
                    simpa [σ_Iₐ, σ, Iₐ, createState] using hnonce
                  by_cases hDepth :
                      value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧
                        createState.executionEnv.depth < 1024 ∧ initCode.size ≤ 49152
                  ·
                    have hDepth_expanded :
                        value ≤
                            Option.option { val := 0 } (fun x => x.balance)
                              (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner) ∧
                          s.executionEnv.depth < 1024 ∧
                            (s.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152 := by
                      simpa [σ, Iₐ, initCode, createState] using hDepth
                    by_cases hrefund :
                        (createState.machineState.gasAvailable + g').toNat <
                          L createState.machineState.gasAvailable.toNat
                    ·
                      have hrefund_expanded := hrefund
                      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                        hnonce, hnonce_expanded, hDepth, hDepth_expanded, hdepth_eq, hperm_true] at hrefund_expanded
                      simp [Id.run, Stack.pop4, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                        Except.bind,
                        memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ,
                        σStar, createResult, g', hnonce, hnonce_expanded, hDepth, hDepth_expanded, hrefund,
                        hrefund_expanded]
                      conv_lhs =>
                        simp [bind, Except.bind]
                      have hDepth_lt := hDepth_expanded.2.1
                      have hDepth_lt' : (↑s.executionEnv.depth : Nat) < 1024 := by
                        simpa using hDepth_lt
                      simp [hDepth_lt', hrefund_expanded]
                    ·
                      have hrefund_expanded := hrefund
                      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                        hnonce, hnonce_expanded, hDepth, hDepth_expanded, hdepth_eq, hperm_true] at hrefund_expanded
                      simp [Id.run, Stack.pop4, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                        Except.bind,
                        memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ,
                        σStar, createResult, g', hnonce, hnonce_expanded, hDepth, hDepth_expanded, hrefund,
                        hrefund_expanded]
                      have hrefund_expanded_not := not_lt.mpr hrefund_expanded
                      have hDepth_lt := hDepth_expanded.2.1
                      have hDepth_lt' : (↑s.executionEnv.depth : Nat) < 1024 := by
                        simpa using hDepth_lt
                      have hDepth_ne : s.executionEnv.depth ≠ 1024 := by
                        omega
                      have hDepth_val_ne : (↑s.executionEnv.depth : Nat) ≠ 1024 := by
                        omega
                      simp [hDepth_expanded, hDepth_lt', hDepth_ne, hDepth_val_ne, hrefund_expanded_not, Stack.push]
                  ·
                    have hDepth_expanded :
                        ¬ (value ≤
                            Option.option { val := 0 } (fun x => x.balance)
                              (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner) ∧
                          s.executionEnv.depth < 1024 ∧
                            (s.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152) := by
                      simpa [σ, Iₐ, initCode, createState] using hDepth
                    have hDepth_expanded_nat :
                        ¬ (value ≤
                            Option.option { val := 0 } (fun x => x.balance)
                              (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner) ∧
                          (↑s.executionEnv.depth : Nat) < 1024 ∧
                            (s.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152) := by
                      intro h
                      exact hDepth_expanded ⟨h.1, by simpa using h.2.1, h.2.2⟩
                    by_cases hrefund :
                        (createState.machineState.gasAvailable + g').toNat <
                          L createState.machineState.gasAvailable.toNat
                    ·
                      have hrefund_expanded := hrefund
                      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                        hnonce, hnonce_expanded, hDepth, hDepth_expanded, hDepth_expanded_nat, hperm_true] at hrefund_expanded
                      simp [Id.run, Stack.pop4, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                        Except.bind,
                        memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ,
                        σStar, createResult, g', hnonce, hnonce_expanded, hDepth, hDepth_expanded, hrefund,
                        hrefund_expanded]
                      conv_lhs =>
                        simp [bind, Except.bind]
                      simp [hDepth_expanded, hDepth_expanded_nat, hrefund_expanded]
                    ·
                      have hrefund_expanded := hrefund
                      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ, σStar, createResult, g',
                        hnonce, hnonce_expanded, hDepth, hDepth_expanded, hDepth_expanded_nat, hperm_true] at hrefund_expanded
                      have hrefund_expanded_not := not_lt.mpr hrefund_expanded
                      simp [Id.run, Stack.pop4, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                        Except.bind,
                        memoryExpansionCost, memoryExpansionCost.μᵢ', hstack, gasAvailable', gasCost,
                        createState, UInt256_ofNat_1, hdepth_eq, hperm_true, initCode, ζ, Iₐ, Iₒ, σ, σ_Iₐ,
                        σStar, createResult, g', hnonce, hnonce_expanded, hDepth, hDepth_expanded, hrefund,
                        hrefund_expanded, hrefund_expanded_not]
                      simp [hDepth_expanded, hDepth_expanded_nat, hrefund_expanded_not, Stack.push]

theorem step_selfdestruct : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SELFDESTRUCT, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | target :: t =>
        let gasCost := Cselfdestruct s
        if s.machineState.gasAvailable.toNat < gasCost then .error .OutOfGass
        else if s.machineState.stack.length - 1 + 0 > 1024 then .error .StackOverflow
        else if ¬ s.executionEnv.perm then .error .StaticModeViolation
        else
        let sdState :=
          {s with
            machineState.gasAvailable := s.machineState.gasAvailable.natSub gasCost
            machineState.execLength := s.machineState.execLength + 1}
        let Iₐ := sdState.executionEnv.codeOwner
        let r := AccountAddress.ofUInt256 target
        let substate :=
          if sdState.createdAccounts.contains Iₐ then
            {sdState.substate with
              selfDestructSet := sdState.substate.selfDestructSet.insert Iₐ
              accessedAccounts := sdState.substate.accessedAccounts.insert r}
          else
            {sdState.substate with
              accessedAccounts := sdState.substate.accessedAccounts.insert r}
        let accountMap :=
          if sdState.createdAccounts.contains Iₐ then
            match sdState.accountMap.find? Iₐ with
            | none => sdState.accountMap
            | some selfAcc =>
              match sdState.accountMap.find? r with
              | none =>
                if selfAcc.balance == ⟨0⟩ then sdState.accountMap
                else
                  sdState.accountMap.insert r {(default : Account) with balance := selfAcc.balance}
                    |>.insert Iₐ {selfAcc with balance := ⟨0⟩}
              | some targetAcc =>
                if r ≠ Iₐ then
                  sdState.accountMap.insert r {targetAcc with balance := targetAcc.balance + selfAcc.balance}
                    |>.insert Iₐ {selfAcc with balance := ⟨0⟩}
                else
                  sdState.accountMap.insert r {targetAcc with balance := ⟨0⟩}
                    |>.insert Iₐ {selfAcc with balance := ⟨0⟩}
          else
            match sdState.accountMap.find? Iₐ with
            | none => sdState.accountMap
            | some selfAcc =>
              match sdState.accountMap.find? r with
              | none =>
                if selfAcc.balance == ⟨0⟩ then sdState.accountMap
                else
                  sdState.accountMap.insert r {(default : Account) with balance := selfAcc.balance}
                    |>.insert Iₐ {selfAcc with balance := ⟨0⟩}
              | some targetAcc =>
                if r ≠ Iₐ then
                  sdState.accountMap.insert r {targetAcc with balance := targetAcc.balance + selfAcc.balance}
                    |>.insert Iₐ {selfAcc with balance := ⟨0⟩}
                else
                  sdState.accountMap
        .ok ({sdState with
                  accountMap := accountMap
                  substate := substate
                  machineState.stack := t
                  machineState.pc := sdState.machineState.pc + ⟨1⟩
                  executionEnv := s.executionEnv
                  }
                ,.some (true, .empty))
      | _ => .error .StackUnderflow
:= by
      -- SELFDESTRUCT bookkeeping is expensive to normalize directly; leave it folded for now.
      intros s I_b hselfdestruct
      simp [Xstep, Z, δ, I_b, hselfdestruct]
      match hstack : s.machineState.stack with
      | [] => simp
      | target :: t =>
        have hstacksize' : ¬ t.length + 1 < 1 := by simp
        simp [hstacksize']
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
        let chargedState : State :=
          {s with
            machineState :=
              {s.machineState with
                stack := target :: t
                gasAvailable := s.machineState.gasAvailable.natSub 0}}
        by_cases hgas :
            ((s.machineState.gasAvailable.natSub 0).toNat < Cselfdestruct chargedState)
        ·
          have hgas0 : s.machineState.gasAvailable.toNat < Cselfdestruct s := by
            simpa [chargedState, Cselfdestruct, hstack, UInt256_subzero'] using hgas
          simp [hgas, hgas0, C', hstack, chargedState]
        ·
          have hgas0 : ¬ s.machineState.gasAvailable.toNat < Cselfdestruct s := by
            simpa [chargedState, Cselfdestruct, hstack, UInt256_subzero'] using hgas
          simp [hgas, hgas0, C', hstack, chargedState]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [hoverflow]
          ·
            simp [hoverflow]
            by_cases hstatic : s.executionEnv.perm = false
            · simp [hstatic]
            ·
              have hperm : s.executionEnv.perm = true := by
                cases hp : s.executionEnv.perm
                · exact False.elim (hstatic hp)
                · rfl
              simp [hstatic, hperm, bind, Except.bind]
              let gasCost := Cselfdestruct s
              let sdState :=
                {s with
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub gasCost
                  machineState.execLength := s.machineState.execLength + 1}
              let Iₐ := sdState.executionEnv.codeOwner
              let r := AccountAddress.ofUInt256 target
              unfold step
              simp [Id.run, Stack.pop, Ethereum.State.replaceStackAndIncrPC,
                Ethereum.State.incrPC, Ethereum.State.lookupAccount,
                gasCost, sdState, Iₐ, r]
              cases hcreated : s.createdAccounts.contains s.executionEnv.codeOwner
              · have hcreated_mem : ¬ s.executionEnv.codeOwner ∈ s.createdAccounts := by
                  rw [← Batteries.RBSet.contains_iff]
                  simpa [hcreated]
                cases hself :
                    Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner with
                | none =>
                  simp [hcreated, hcreated_mem, hself, dbgTrace, sdState, Iₐ, r,
                    chargedState, Cselfdestruct, hstack, UInt256_subzero', UInt256_ofNat_1]
                | some selfAcc =>
                  simp [hcreated, hcreated_mem, hself, sdState, Iₐ, r]
                  cases htarget :
                      Batteries.RBMap.find? s.accountMap (AccountAddress.ofUInt256 target) with
                  | none =>
                    simp [hcreated, hcreated_mem, htarget, sdState, Iₐ, r]
                    cases hbal : (selfAcc.balance == (⟨0⟩ : UInt256)) <;>
                      simp [hcreated, hcreated_mem, hbal, sdState, Iₐ, r,
                        chargedState, Cselfdestruct, hstack, UInt256_subzero', UInt256_ofNat_1]
                  | some targetAcc =>
                    simp [hcreated, hcreated_mem, htarget, sdState, Iₐ, r]
                    by_cases hneq : AccountAddress.ofUInt256 target ≠ s.executionEnv.codeOwner
                    · simp [hcreated, hcreated_mem, hneq, sdState, Iₐ, r,
                        chargedState, Cselfdestruct, hstack, UInt256_subzero', UInt256_ofNat_1]
                    · simp [hcreated, hcreated_mem, hneq, sdState, Iₐ, r,
                        chargedState, Cselfdestruct, hstack, UInt256_subzero', UInt256_ofNat_1]
              · have hcreated_mem : s.executionEnv.codeOwner ∈ s.createdAccounts := by
                  rw [← Batteries.RBSet.contains_iff]
                  simpa [hcreated]
                cases hself :
                    Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner with
                | none =>
                  simp [hcreated, hcreated_mem, hself, dbgTrace, sdState, Iₐ, r,
                    chargedState, Cselfdestruct, hstack, UInt256_subzero', UInt256_ofNat_1]
                | some selfAcc =>
                  simp [hcreated, hcreated_mem, hself, sdState, Iₐ, r]
                  cases htarget :
                      Batteries.RBMap.find? s.accountMap (AccountAddress.ofUInt256 target) with
                  | none =>
                    simp [hcreated, hcreated_mem, htarget, sdState, Iₐ, r]
                    cases hbal : (selfAcc.balance == (⟨0⟩ : UInt256)) <;>
                      simp [hcreated, hcreated_mem, hbal, sdState, Iₐ, r,
                        chargedState, Cselfdestruct, hstack, UInt256_subzero', UInt256_ofNat_1]
                  | some targetAcc =>
                    simp [hcreated, hcreated_mem, htarget, sdState, Iₐ, r]
                    by_cases hneq : AccountAddress.ofUInt256 target ≠ s.executionEnv.codeOwner
                    · simp [hcreated, hcreated_mem, hneq, sdState, Iₐ, r,
                        chargedState, Cselfdestruct, hstack, UInt256_subzero', UInt256_ofNat_1]
                    · simp [hcreated, hcreated_mem, hneq, sdState, Iₐ, r,
                        chargedState, Cselfdestruct, hstack, UInt256_subzero', UInt256_ofNat_1]

theorem step_pc : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PC, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := s.machineState.pc :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hpc
    simp [Xstep, Z, δ, I_b, hpc]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_msize : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.MSIZE, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := (s.machineState.activeWords * ⟨32⟩) :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hmsize
    simp [Xstep, Z, δ, I_b, hmsize]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.machineStateOp, Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push, MachineState.msize]
          rw [UInt256_subzero']

theorem step_gas : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.GAS, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack :=
                  (s.machineState.gasAvailable.natSub GasConstants.Gbase) :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hgasop
    simp [Xstep, Z, δ, I_b, hgasop]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Id.run, EVM.machineStateOp, Ethereum.State.replaceStackAndIncrPC, MachineState.gas]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

theorem step_jumpdest : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.JUMPDEST, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gjumpdest then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 0 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gjumpdest
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hjumpdest
    simp [Xstep, Z, δ, I_b, hjumpdest]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C']
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gjumpdest)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gjumpdest := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gjumpdest := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · rw [UInt256_subzero']

theorem step_jump : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.JUMP, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gmid then .error .OutOfGass
        else if ¬ (D_J I_b ⟨0⟩).contains a then .error .BadJumpDestination
        else
        if s.machineState.stack.length - 1 + 0 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gmid
                  machineState.pc := a
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hjump
    simp [Xstep, Z, δ, I_b, hjump]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
      by_cases hgas :
          ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gmid)
      · have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gmid := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gmid := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, hstack]
        cases hcontains : (D_J I_b ⟨0⟩).contains a
        · simp [Z.notIn, Z.belongs, I_b, hcontains]
        · simp [Z.notIn, Z.belongs, hcontains]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [I_b, hcontains, hoverflow]
          ·
            simp [I_b, hcontains, hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Stack.pop, UInt256_subzero']

theorem step_jumpi : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.JUMPI, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Ghigh then .error .OutOfGass
        else if b != ⟨0⟩ ∧ ¬ (D_J I_b ⟨0⟩).contains a then .error .BadJumpDestination
        else
        if s.machineState.stack.length - 2 + 0 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Ghigh
                  machineState.pc := if b != ⟨0⟩ then a else s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hjumpi
    simp [Xstep, Z, δ, I_b, hjumpi]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
      by_cases hgas :
          ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Ghigh)
      · have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Ghigh := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Ghigh := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, hstack]
        cases hb : (b != (⟨0⟩ : UInt256))
        ·
          have hbeq : b = (⟨0⟩ : UInt256) :=
            UInt256_bne_zero_eq_false_eq b hb
          have hzero_bne : ((⟨0⟩ : UInt256) != (⟨0⟩ : UInt256)) = false := by
            decide
          simp [Z.notIn, Z.belongs, I_b, hb, hbeq]
          simp [α, Operation.isCreate]
          by_cases hoverflow : 1024 < t.length
          · simp [I_b, hb, hbeq, hoverflow]
          ·
            simp [I_b, hb, hbeq, hoverflow]
            simp [bind, Except.bind]
            unfold step
            simp [Stack.pop2, hb, hbeq, hzero_bne, UInt256_subzero']
        ·
          have hbne : b ≠ (⟨0⟩ : UInt256) :=
            UInt256_bne_zero_eq_true_ne b hb
          cases hcontains : (D_J I_b ⟨0⟩).contains a
          · simp [Z.notIn, Z.belongs, I_b, hb, hbne, hcontains]
          · simp [Z.notIn, Z.belongs, I_b, hb, hbne, hcontains]
            simp [α, Operation.isCreate]
            by_cases hoverflow : 1024 < t.length
            · simp [I_b, hb, hbne, hcontains, hoverflow]
            ·
              simp [I_b, hb, hbne, hcontains, hoverflow]
              simp [bind, Except.bind]
              unfold step
              simp [Stack.pop2, hb, hbne, UInt256_subzero']

theorem step_push0 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH0, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gbase then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := ⟨0⟩ :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gbase
                machineState.pc := s.machineState.pc + ⟨1⟩
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s I_b hpush0
    simp [Xstep, Z, δ, I_b, hpush0]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
      , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
      , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
    by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gbase)
    · simp [hgas]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow]
        simp [bind, Except.bind]
        unfold step
        simp [Ethereum.State.replaceStackAndIncrPC]
        unfold Ethereum.State.incrPC
        simp
        apply And.intro
        · simp [UInt256.ofNat, Id.run]; rfl
        · simp [Stack.push]
          rw [UInt256_subzero']

set_option maxHeartbeats 2000000 in
theorem step_push : ∀ (s : State) (op : Operation.POp) (arg : UInt256) (argWidth : Nat),
  op ≠ .PUSH0
  → let I_b := s.executionEnv.code
    decode I_b s.machineState.pc = some (.Push op, .some (arg, argWidth))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else
      if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else
      .ok ({s with
                machineState.stack := arg :: s.machineState.stack,
                machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                machineState.pc := s.machineState.pc + UInt256.ofNat argWidth.succ
                machineState.execLength := s.machineState.execLength + 1
                }
              ,.none)
:= by
    intros s op arg argWidth hpush0 I_b hpush
    let chargedState : State :=
      {s with
        machineState :=
          {s.machineState with
            gasAvailable := s.machineState.gasAvailable.natSub 0}}
    have hcostCharged : C' chargedState (.Push op) = GasConstants.Gverylow := by
      cases op
      · contradiction
      all_goals
        simp [chargedState, C', InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
          InstructionGasGroups.Wzero, InstructionGasGroups.Wbase,
          InstructionGasGroups.Wverylow, InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
          InstructionGasGroups.Wverylow.dupInstrs, InstructionGasGroups.Wverylow.swapInstrs]
    simp [Xstep, Z, δ, I_b, hpush]
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hcostCharged]
    by_cases hgas :
      ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
    · simp [hgas, hcostCharged, chargedState]
      have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas0]
    · have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
        simpa [UInt256_subzero'] using hgas
      simp [hgas, hgas0, hcostCharged, chargedState, α, Operation.isCreate]
      by_cases hoverflow : 1024 < s.machineState.stack.length + 1
      · simp [hoverflow]
      ·
        simp [hoverflow, bind, Except.bind]
        unfold step
        cases op
        · contradiction
        all_goals
          simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            Stack.push, UInt256_subzero', Id.run]

theorem step_push1 : ∀ (s : State) (arg : UInt256),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH1, .some (arg, 1))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := arg :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 2
        machineState.execLength := s.machineState.execLength + 1}, .none)
:= by
    intros s arg I_b hpush
    simpa using step_push s .PUSH1 arg 1 (by decide) hpush

theorem step_push2 : ∀ (s : State) (arg : UInt256),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH2, .some (arg, 2))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := arg :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 3
        machineState.execLength := s.machineState.execLength + 1}, .none)
:= by
    intros s arg I_b hpush
    simpa using step_push s .PUSH2 arg 2 (by decide) hpush

theorem step_push3 : ∀ (s : State) (arg : UInt256),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH3, .some (arg, 3))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := arg :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 4
        machineState.execLength := s.machineState.execLength + 1}, .none)
:= by
    intros s arg I_b hpush
    simpa using step_push s .PUSH3 arg 3 (by decide) hpush

theorem step_push4 : ∀ (s : State) (arg : UInt256),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH4, .some (arg, 4))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := arg :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 5
        machineState.execLength := s.machineState.execLength + 1}, .none)
:= by
    intros s arg I_b hpush
    simpa using step_push s .PUSH4 arg 4 (by decide) hpush

theorem step_push5 : ∀ (s : State) (arg : UInt256),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH5, .some (arg, 5))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := arg :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 6
        machineState.execLength := s.machineState.execLength + 1}, .none)
:= by
    intros s arg I_b hpush
    simpa using step_push s .PUSH5 arg 5 (by decide) hpush

theorem step_push6 : ∀ (s : State) (arg : UInt256),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH6, .some (arg, 6))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := arg :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 7
        machineState.execLength := s.machineState.execLength + 1}, .none)
:= by
    intros s arg I_b hpush
    simpa using step_push s .PUSH6 arg 6 (by decide) hpush

theorem step_push7 : ∀ (s : State) (arg : UInt256),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH7, .some (arg, 7))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := arg :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 8
        machineState.execLength := s.machineState.execLength + 1}, .none)
:= by
    intros s arg I_b hpush
    simpa using step_push s .PUSH7 arg 7 (by decide) hpush

theorem step_push8 : ∀ (s : State) (arg : UInt256),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH8, .some (arg, 8))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := arg :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 9
        machineState.execLength := s.machineState.execLength + 1}, .none)
:= by
    intros s arg I_b hpush
    simpa using step_push s .PUSH8 arg 8 (by decide) hpush

theorem step_push9 : ∀ (s : State) (arg : UInt256),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH9, .some (arg, 9))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := arg :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 10
        machineState.execLength := s.machineState.execLength + 1}, .none)
:= by
    intros s arg I_b hpush
    simpa using step_push s .PUSH9 arg 9 (by decide) hpush

theorem step_push10 : ∀ (s : State) (arg : UInt256),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.PUSH10, .some (arg, 10))
  → Xstep (D_J I_b ⟨0⟩) s =
      if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length - 0 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := arg :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 11
        machineState.execLength := s.machineState.execLength + 1}, .none)
:= by
    intros s arg I_b hpush
    simpa using step_push s .PUSH10 arg 10 (by decide) hpush
theorem step_dup1 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP1, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 1 + 2 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := a :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup1
    simp [Xstep, Z, δ, I_b, hdup1]
    match hstack : s.machineState.stack with
    | [] => simp
    | a :: t =>
      have hstacksize' : ¬ t.length + 1 < 1 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 2
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup2 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP2, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 3 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := b :: a :: b :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup2
    simp [Xstep, Z, δ, I_b, hdup2]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 3
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap1 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP1, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 2 + 2 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := b :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap1
    simp [Xstep, Z, δ, I_b, hswap1]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | a :: b :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 < 2 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 2
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']
theorem step_swap2 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP2, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 3 + 3 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := c :: b :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap2
    simp [Xstep, Z, δ, I_b, hswap2]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | a :: b :: c :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 < 3 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 3
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup3 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP3, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 3 + 4 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := c :: a :: b :: c :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup3
    simp [Xstep, Z, δ, I_b, hdup3]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | a :: b :: c :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 < 3 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 4
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap3 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP3, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 4 + 4 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := d :: b :: c :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap3
    simp [Xstep, Z, δ, I_b, hswap3]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 < 4 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 4
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup4 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP4, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 4 + 5 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := d :: a :: b :: c :: d :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup4
    simp [Xstep, Z, δ, I_b, hdup4]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 < 4 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 5
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap4 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP4, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 5 + 5 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := e :: b :: c :: d :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap4
    simp [Xstep, Z, δ, I_b, hswap4]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 < 5 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 5
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup5 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP5, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 5 + 6 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := e :: a :: b :: c :: d :: e :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup5
    simp [Xstep, Z, δ, I_b, hdup5]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 < 5 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 6
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap5 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP5, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 6 + 6 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := f :: b :: c :: d :: e :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap5
    simp [Xstep, Z, δ, I_b, hswap5]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 < 6 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 6
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup6 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP6, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 6 + 7 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := f :: a :: b :: c :: d :: e :: f :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup6
    simp [Xstep, Z, δ, I_b, hdup6]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 < 6 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 7
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap6 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP6, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 7 + 7 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := g :: b :: c :: d :: e :: f :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap6
    simp [Xstep, Z, δ, I_b, hswap6]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 7 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 7
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup7 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP7, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 7 + 8 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := g :: a :: b :: c :: d :: e :: f :: g :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup7
    simp [Xstep, Z, δ, I_b, hdup7]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 7 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 8
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap7 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP7, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 8 + 8 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := h :: b :: c :: d :: e :: f :: g :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap7
    simp [Xstep, Z, δ, I_b, hswap7]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 8 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 8
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup8 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP8, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 8 + 9 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := h :: a :: b :: c :: d :: e :: f :: g :: h :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup8
    simp [Xstep, Z, δ, I_b, hdup8]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 8 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 9
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap8 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP8, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 9 + 9 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := i :: b :: c :: d :: e :: f :: g :: h :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap8
    simp [Xstep, Z, δ, I_b, hswap8]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: t =>
      have hstacksize' : ¬ t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 9 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 9
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup9 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP9, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 9 + 10 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := i :: a :: b :: c :: d :: e :: f :: g :: h :: i :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup9
    simp [Xstep, Z, δ, I_b, hdup9]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 9 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 10
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap9 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP9, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 10 + 10 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := j :: b :: c :: d :: e :: f :: g :: h :: i :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap9
    simp [Xstep, Z, δ, I_b, hswap9]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 10 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 10
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup10 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP10, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 10 + 11 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := j :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup10
    simp [Xstep, Z, δ, I_b, hdup10]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 10 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 11
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap10 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP10, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 11 + 11 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := k :: b :: c :: d :: e :: f :: g :: h :: i :: j :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap10
    simp [Xstep, Z, δ, I_b, hswap10]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 11 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 11
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup11 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP11, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 11 + 12 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := k :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup11
    simp [Xstep, Z, δ, I_b, hdup11]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 11 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 12
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap11 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP11, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 12 + 12 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := l :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap11
    simp [Xstep, Z, δ, I_b, hswap11]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 12 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 12
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup12 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP12, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 12 + 13 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := l :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup12
    simp [Xstep, Z, δ, I_b, hdup12]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 12 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 13
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap12 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP12, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 13 + 13 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := m :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap12
    simp [Xstep, Z, δ, I_b, hswap12]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 13 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 13
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup13 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP13, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 13 + 14 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := m :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup13
    simp [Xstep, Z, δ, I_b, hdup13]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 13 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 14
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap13 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP13, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 14 + 14 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := n :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap13
    simp [Xstep, Z, δ, I_b, hswap13]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 14 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 14
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup14 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP14, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 14 + 15 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := n :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup14
    simp [Xstep, Z, δ, I_b, hdup14]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 14 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 15
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap14 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP14, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 15 + 15 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := o :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap14
    simp [Xstep, Z, δ, I_b, hswap14]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 15 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 15
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup15 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP15, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 15 + 16 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := o :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup15
    simp [Xstep, Z, δ, I_b, hdup15]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 15 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 16
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap15 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP15, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: p :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 16 + 16 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := p :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap15
    simp [Xstep, Z, δ, I_b, hswap15]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: p :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 16 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 16
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_dup16 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.DUP16, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: p :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 16 + 17 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := p :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: p :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hdup16
    simp [Xstep, Z, δ, I_b, hdup16]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: p :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 16 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 17
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']

theorem step_swap16 : ∀ (s : State),
  let I_b := s.executionEnv.code
  decode I_b s.machineState.pc = some (.SWAP16, .none)
  → Xstep (D_J I_b ⟨0⟩) s =
      match s.machineState.stack with
      | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: p :: q :: t =>
        if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
        else
        if s.machineState.stack.length - 17 + 17 > 1024 then .error .StackOverflow
        else
        .ok ({s with
                  machineState.stack := q :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: p :: a :: t,
                  machineState.gasAvailable := s.machineState.gasAvailable.natSub GasConstants.Gverylow
                  machineState.pc := s.machineState.pc + ⟨1⟩
                  machineState.execLength := s.machineState.execLength + 1
                  }
                ,.none)
      | _ => .error .StackUnderflow
:= by
    intros s I_b hswap16
    simp [Xstep, Z, δ, I_b, hswap16]
    match hstack : s.machineState.stack with
    | [] => simp
    | _ :: [] => simp
    | _ :: _ :: [] => simp
    | _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => simp
    | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: p :: q :: t =>
      have hstacksize' : ¬ t.length  + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 17 := by simp
      simp [hstacksize']
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', C'
        , InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount
        , InstructionGasGroups.Wzero, InstructionGasGroups.Wbase
        , InstructionGasGroups.Wverylow
        , InstructionGasGroups.Wverylow.pushInstrsWithoutZero
        , InstructionGasGroups.Wverylow.dupInstrs
        , InstructionGasGroups.Wverylow.swapInstrs]
      by_cases hgas: ((s.machineState.gasAvailable.natSub 0).toNat < GasConstants.Gverylow)
      · simp [hgas]
        have hgas0 : s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas0]
      ·
        have hgas0 : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
          simpa [UInt256_subzero'] using hgas
        simp [hgas, hgas0, α, Operation.isCreate]
        by_cases hoverflow : 1024 < t.length + 17
        · simp [hoverflow]
        ·
          simp [hoverflow]
          simp [bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC]
          unfold Ethereum.State.incrPC
          simp
          apply And.intro
          · simp [UInt256.ofNat, Id.run]; rfl
          · rw [UInt256_subzero']
