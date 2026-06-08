import Ethereum.Symbolic.SymExec

open Ethereum.EVM

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Ethereum

namespace Symbolic

namespace SymExecProofs

lemma match_list_len_lt_2 {A B : Type} {b : B} {f : A → A → List A → B} : ∀ (l : List A),
    List.length l < 2 →
    (match l with
    | x :: y :: t => f x y t
    | _ => b) = b := by
      intro l hlen
      cases l with
      | nil => rfl
      | cons _ t =>
          cases t with
          | nil => rfl
          | cons _ t =>
              simp at hlen
              omega

lemma list_len_ge_2_to_match {α : Type} {l : List α} :
    2 ≤ List.length l →
    ∃ a b t, l = a :: b :: t := by
      intro h
      match l with
      | [] => simp at h
      | _ :: [] => simp at h
      | a :: b :: t => simp

lemma list_get_dropped {α : Type} {a : α} {t l : List α} {n : Nat} :
    a :: t = List.drop n l → l[n]? = .some a := by
  intro h
  rw [List.drop_eq_getElem_cons] at h
  simp at h
  symm
  rw [h.left]
  rw [List.some_getElem_eq_getElem?_iff]
  · simp
  · apply List.length_lt_of_drop_ne_nil; simp [← h]

lemma if_and_eq_of_prop_eq
    {α : Type} {p q r : Prop} [Decidable p] [Decidable q] [Decidable r]
    (a b : α) (h : p = q) :
    (if p ∧ r then a else b) = (if q ∧ r then a else b) := by
  by_cases hp : p
  · have hq : q := by simpa [h] using hp
    simp [hp, hq]
  · have hq : ¬ q := by
      intro hq
      exact hp (by simpa [h] using hq)
    simp [hp, hq]

lemma if_and_eq_of_iff
    {α : Type} {p q r : Prop} [Decidable p] [Decidable q] [Decidable r]
    (a b : α) (h : p ↔ q) :
    (if p ∧ r then a else b) = (if q ∧ r then a else b) := by
  by_cases hp : p
  · have hq : q := h.mp hp
    simp [hp, hq]
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

lemma list_getElem!_eq_of_getElem?_some
    {α : Type} [Inhabited α] {l : List α} {idx : Nat} {a : α}
    (hidx : l[idx]? = some a) :
    l[idx]! = a := by
  obtain ⟨hvalid, hget⟩ := List.getElem_of_getElem? hidx
  rw [getElem!_pos l idx hvalid]
  exact hget

lemma UInt256_beq_zero_false_of_ne
    (u : UInt256)
    (hne : u ≠ (⟨0⟩ : UInt256)) :
    (u == (⟨0⟩ : UInt256)) = false := by
  cases u with
  | mk uv =>
      cases uv with
      | mk n hn =>
          simp at hne ⊢
          change (⟨n, hn⟩ == (0 : Fin UInt256.size)) = false
          simp [hne]

lemma UInt256_ne_zero_of_beq_false
    (u : UInt256)
    (hbeq : (u == (⟨0⟩ : UInt256)) = false) :
    u ≠ (⟨0⟩ : UInt256) := by
  cases u with
  | mk uv =>
      cases uv with
      | mk n hn =>
          change (⟨n, hn⟩ == (0 : Fin UInt256.size)) = false at hbeq
          intro hz
          cases hz
          have hfin : (⟨0, hn⟩ : Fin UInt256.size) = (0 : Fin UInt256.size) := by
            ext
            rfl
          rw [hfin] at hbeq
          have htrue :
              ((0 : Fin UInt256.size) == (0 : Fin UInt256.size)) = true := by
            decide
          rw [htrue] at hbeq
          contradiction

lemma UInt256_beq_zero_eq_decide (u : UInt256) :
    (u == (⟨0⟩ : UInt256)) = decide (u = (⟨0⟩ : UInt256)) := by
  by_cases h : u = (⟨0⟩ : UInt256)
  · subst u
    rfl
  · have hb : (u == (⟨0⟩ : UInt256)) = false :=
      UInt256_beq_zero_false_of_ne u h
    simp [h, hb]

lemma UInt256_deadFlag_bne_zero_bool (b : Bool) :
    ((if b then (⟨1⟩ : UInt256) else (⟨0⟩ : UInt256)) !=
      (⟨0⟩ : UInt256)) = b := by
  cases b
  · rfl
  · rfl

lemma UInt256_deadFlag_bne_zero_prop (p : Prop) [Decidable p] :
    ((if p then (⟨1⟩ : UInt256) else (⟨0⟩ : UInt256)) !=
      (⟨0⟩ : UInt256)) = decide p := by
  by_cases h : p
  · simp [h]
    rfl
  · simp [h]
    rfl

lemma UInt256_bne_zero_eq_decide_ne (u : UInt256) :
    (u != (⟨0⟩ : UInt256)) = decide (u ≠ (⟨0⟩ : UInt256)) := by
  by_cases h : u = (⟨0⟩ : UInt256)
  · subst u
    rfl
  · have hne : u ≠ (⟨0⟩ : UInt256) := h
    simp [hne]
    cases hbne : (u != (⟨0⟩ : UInt256)) with
    | false =>
        have hz := UInt256_bne_zero_eq_false_eq u hbne
        contradiction
    | true => rfl

lemma UInt256_not_decide_eq_zero_eq_bne_zero (u : UInt256) :
    (!decide (u = (⟨0⟩ : UInt256))) = (u != (⟨0⟩ : UInt256)) := by
  rw [UInt256_bne_zero_eq_decide_ne]
  by_cases h : u = (⟨0⟩ : UInt256) <;> simp [h]

lemma UInt256_bne_zero_eq_bool_iff_ne {u : UInt256} {b : Bool}
    (h : (u != (⟨0⟩ : UInt256)) = b) :
    (u ≠ (⟨0⟩ : UInt256)) ↔ b = true := by
  rw [UInt256_bne_zero_eq_decide_ne] at h
  cases b <;> simp at h ⊢
  · exact h
  · exact h

lemma operation_isCreate_eq_true_iff (w : Operation) :
    w.isCreate = true ↔ w = .CREATE ∨ w = .CREATE2 := by
  cases w <;> (try rename_i op) <;> (try cases op) <;>
    simp [Operation.isCreate]

lemma concretizeSym_addCondition_error
    {s b : Nat}
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {c : Condition s b}
    {h : s ≤ sym.n}
    {e : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hcond : ∀ hs, checkCondition concrete validJumps c hs = .error e) :
    concretizeSym concrete validJumps (addCondition sym c h) = .error e := by
  cases hconds : checkConditions concrete validJumps sym.conditions with
  | error e' =>
      simp [concretizeSym, hconds, Except.bind, bind] at hbase
  | ok condsProofs =>
      simp [concretizeSym, addCondition, checkConditions, hconds,
        hcond (Nat.le_trans h condsProofs.down), Except.bind, bind]

lemma concretizeSym_addCondition_preserve_error
    {s b : Nat}
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {c : Condition s b}
    {h : s ≤ sym.n}
    {e : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error e) :
    concretizeSym concrete validJumps (addCondition sym c h) = .error e := by
  cases hconds : checkConditions concrete validJumps sym.conditions with
  | error e' =>
      simpa [concretizeSym, addCondition, checkConditions, hconds, Except.bind, bind]
        using hbase
  | ok condsProofs =>
      simp [concretizeSym, hconds, Except.bind, bind] at hbase

lemma concretizeSym_update_gas_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {e : Expr .word}
    {h : e.consumeStack ≤ sym.n}
    {err : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error err) :
    concretizeSym concrete validJumps (update_gas sym e h) = .error err := by
  cases hconds : checkConditions concrete validJumps sym.conditions with
  | error e' =>
      simpa [concretizeSym, update_gas, hconds, Except.bind, bind]
        using hbase
  | ok condsProofs =>
      simp [concretizeSym, hconds, Except.bind, bind] at hbase

lemma concretizeExpr_proof_irrel
    {τ : EType}
    {concrete : Ethereum.State}
    {expr : Expr τ}
    {h₁ h₂ : expr.consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete expr h₁ = concretizeExpr concrete expr h₂ := by
  exact congrArg (fun h => concretizeExpr concrete expr h) (Subsingleton.elim h₁ h₂)

lemma concretizeExpr_stackItem_of_lt
    {concrete : Ethereum.State}
    {idx : Nat}
    {h : (Expr.StackItem idx).consumeStack ≤ concrete.machineState.stack.length}
    (hidx : idx < concrete.machineState.stack.length) :
    concretizeExpr concrete (Expr.StackItem idx) h =
      concrete.machineState.stack[idx]'hidx := by
  rw [concretizeExpr.eq_def]
  simp
  rw [List.getElem?_eq_getElem hidx]
  simp

lemma concretizeExpr_natLit
    {concrete : Ethereum.State}
    {n : Nat}
    {h : (Expr.NatLit n).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.NatLit n) h = n := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_sub
    {concrete : Ethereum.State}
    {a b : Expr .word}
    {h : (Expr.Sub a b).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.Sub a b) h =
      (let a' : UInt256 := concretizeExpr concrete a
        (by simp [Expr.consumeStack] at h; exact h.left)
       let b' : UInt256 := concretizeExpr concrete b
        (by simp [Expr.consumeStack] at h; exact h.right)
       a' - b') := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_subNat
    {concrete : Ethereum.State}
    {a b : Expr .num}
    {h : (Expr.SubNat a b).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.SubNat a b) h =
      (let a' : Nat := concretizeExpr concrete a
        (by simp [Expr.consumeStack] at h; exact h.left)
       let b' : Nat := concretizeExpr concrete b
        (by simp [Expr.consumeStack] at h; exact h.right)
       a' - b') := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_cₘ
    {concrete : Ethereum.State}
    {a : Expr .num}
    {h : (Expr.Cₘ a).consumeStack ≤ concrete.machineState.stack.length} :
      concretizeExpr concrete (Expr.Cₘ a) h =
        (let a' : Nat := concretizeExpr concrete a
          (by simpa [Expr.consumeStack] using h)
         Cₘ (UInt256.ofNat a')) := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_addNat
    {concrete : Ethereum.State}
    {a b : Expr .num}
    {h : (Expr.AddNat a b).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.AddNat a b) h =
      (let a' : Nat := concretizeExpr concrete a (by simp at h; exact h.left)
       let b' : Nat := concretizeExpr concrete b (by simp at h; exact h.right)
       a' + b') := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_toNat
    {concrete : Ethereum.State}
    {a : Expr .word}
    {h : (Expr.toNat a).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.toNat a) h =
      (concretizeExpr concrete a
        (by simpa [Expr.consumeStack] using h)).toNat := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_bufLengthNat
    {concrete : Ethereum.State}
    {b : Expr .buf}
    {h : (Expr.BufLengthNat b).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.BufLengthNat b) h =
      (concretizeExpr concrete b (by simpa [Expr.consumeStack] using h)).size := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_m
    {concrete : Ethereum.State}
    {a b c : Expr .word}
    {h : (Expr.M a b c).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.M a b c) h =
      (let a' : UInt256 := concretizeExpr concrete a
        (by simp [Expr.consumeStack] at h; exact h.left)
       let b' : UInt256 := concretizeExpr concrete b
        (by simp [Expr.consumeStack] at h; exact h.right.left)
       let c' : UInt256 := concretizeExpr concrete c
        (by simp [Expr.consumeStack] at h; exact h.right.right)
       MachineState.M a'.toNat b'.toNat c'.toNat) := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_lit
    {concrete : Ethereum.State}
    {lit : UInt256}
    {h : (Expr.Lit lit).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.Lit lit) h = lit := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_addrOfWord
    {concrete : Ethereum.State}
    {a : Expr .word}
    {h : (Expr.AddrOfWord a).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.AddrOfWord a) h =
      AccountAddress.ofUInt256 (concretizeExpr concrete a (by simpa using h)) := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_address
    {concrete : Ethereum.State}
    {h : Expr.Address.consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete Expr.Address h = concrete.executionEnv.codeOwner := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_ofNat
    {concrete : Ethereum.State}
    {a : Expr .num}
    {h : (Expr.ofNat a).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.ofNat a) h =
      UInt256.ofNat (concretizeExpr concrete a
        (by simpa [Expr.consumeStack] using h)) := by
  rw [concretizeExpr.eq_def]

lemma UInt256_max_toNat (a b : UInt256) :
    (max a b).toNat = max a.toNat b.toNat := by
  change (if a ≤ b then b else a).toNat = max a.toNat b.toNat
  by_cases h : a ≤ b
  · simp [h, UInt256.toNat]
    exact h
  · simp [h, UInt256.toNat]
    have hnot : ¬ a.val ≤ b.val := by exact h
    omega

lemma concretizeExpr_max
    {concrete : Ethereum.State}
    {a b : Expr .word}
    {h : (Expr.Max a b).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.Max a b) h =
        (max
          (concretizeExpr concrete a (by simp [Expr.consumeStack] at h; exact h.left))
          (concretizeExpr concrete b (by simp [Expr.consumeStack] at h; exact h.right)) : UInt256) := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_cexp
    {concrete : Ethereum.State}
    {a : Expr .word}
    {h : (Expr.Cexp a).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.Cexp a) h =
      (let a' : UInt256 := concretizeExpr concrete a (by simpa using h)
         if a' == ⟨0⟩ then GasConstants.Gexp
         else GasConstants.Gexp + GasConstants.Gexpbyte * (1 + Nat.log 256 a'.toNat)) := by
  rw [concretizeExpr.eq_def]
  congr

lemma concretizeExpr_cwordCost
    {concrete : Ethereum.State}
    {base wordCost : Nat}
    {a : Expr .word}
    {h : (Expr.CwordCost base wordCost a).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.CwordCost base wordCost a) h =
      base + wordCost *
        ((((concretizeExpr concrete a (by simpa using h)) : UInt256).toNat + 31) / 32) := by
  rw [concretizeExpr.eq_def]

lemma concretizeExpr_cbyteCost
    {concrete : Ethereum.State}
    {base byteCost : Nat}
    {a : Expr .word}
    {h : (Expr.CbyteCost base byteCost a).consumeStack ≤ concrete.machineState.stack.length} :
    concretizeExpr concrete (Expr.CbyteCost base byteCost a) h =
      base + byteCost * (((concretizeExpr concrete a (by simpa using h)) : UInt256).toNat) := by
  rw [concretizeExpr.eq_def]

lemma concretizeSym_ok_stack_bound
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    sym.n ≤ concrete.machineState.stack.length := by
  cases hconds : checkConditions concrete validJumps sym.conditions with
  | error e' =>
      simp [concretizeSym, hconds, Except.bind, bind] at hbase
  | ok condsProofs =>
      exact condsProofs.down

lemma concretizeSym_update_gas_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {e : Expr .word}
    {h : e.consumeStack ≤ sym.n}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    concretizeSym concrete validJumps (update_gas sym e h) =
      .ok ({ state with
        machineState := { state.machineState with
          gasAvailable := concretizeExpr concrete e (by
            exact Nat.le_trans h (concretizeSym_ok_stack_bound hbase)) } }, o) := by
  cases hconds : checkConditions concrete validJumps sym.conditions with
  | error e' =>
      simp [concretizeSym, hconds, Except.bind, bind] at hbase
  | ok condsProofs =>
      have hbase' := hbase
      simp [concretizeSym, hconds, Except.bind, bind] at hbase'
      simp [concretizeSym, update_gas, hconds, Except.bind, bind]
      rcases hbase' with ⟨hstate, ho⟩
      subst o
      subst state
      simp [concretizeState, concretizeMachineState, concretizeExpr_proof_irrel]

lemma concretizeState_proof_irrel
    {concrete : Ethereum.State}
    {sym : State}
    {h₁ h₂ : sym.consumeStack ≤ concrete.machineState.stack.length} :
    concretizeState concrete sym h₁ = concretizeState concrete sym h₂ := by
  exact congrArg (fun h => concretizeState concrete sym h) (Subsingleton.elim h₁ h₂)

lemma concretizeAccountMap_proof_irrel
    {concrete : Ethereum.State}
    {σ : AccountMap}
    {h₁ h₂ : σ.consumeStack ≤ concrete.machineState.stack.length} :
    concretizeAccountMap concrete σ h₁ = concretizeAccountMap concrete σ h₂ := by
  exact congrArg (fun h => concretizeAccountMap concrete σ h) (Subsingleton.elim h₁ h₂)

lemma concretizeAccount_proof_irrel
    {concrete : Ethereum.State}
    {account : Account}
    {h₁ h₂ : account.consumeStack ≤ concrete.machineState.stack.length} :
    concretizeAccount concrete account h₁ = concretizeAccount concrete account h₂ := by
  exact congrArg (fun h => concretizeAccount concrete account h) (Subsingleton.elim h₁ h₂)

lemma concretizeSubstate_proof_irrel
    {concrete : Ethereum.State}
    {σ : Substate}
    {h₁ h₂ : σ.consumeStack ≤ concrete.machineState.stack.length} :
    concretizeSubstate concrete σ h₁ = concretizeSubstate concrete σ h₂ := by
  exact congrArg (fun h => concretizeSubstate concrete σ h) (Subsingleton.elim h₁ h₂)

lemma concretizeMachineState_proof_irrel
    {concrete : Ethereum.State}
    {μ : MachineState}
    {h₁ h₂ : μ.consumeStack ≤ concrete.machineState.stack.length} :
    concretizeMachineState concrete μ h₁ = concretizeMachineState concrete μ h₂ := by
  exact congrArg (fun h => concretizeMachineState concrete μ h) (Subsingleton.elim h₁ h₂)

lemma accountConsumeStack_of_find?
    {σ : AccountMap}
    {addr : Expr .addr}
    {account : Account}
    {n : Nat}
    (hstack : σ.consumeStack ≤ n)
    (hfind : σ.find? addr = some account) :
    account.consumeStack ≤ n := by
  obtain ⟨key, hmem, _⟩ := Batteries.RBMap.find?_some_mem_toList hfind
  exact accountConsumeStack_of_mem
    (by simpa [AccountMap.consumeStack] using hstack) hmem

def AccountMapFindSound
    (concrete : Ethereum.State)
    (σ : AccountMap) : Prop :=
  (∀ (hσ : σ.consumeStack ≤ concrete.machineState.stack.length)
      (addr : Expr .addr)
      (haddr : addr.consumeStack ≤ concrete.machineState.stack.length),
      σ.find? addr = none →
        (concretizeAccountMap concrete σ hσ).find?
          (concretizeExpr concrete addr haddr) = none) ∧
  (∀ (hσ : σ.consumeStack ≤ concrete.machineState.stack.length)
      (addr : Expr .addr)
      (account : Account)
      (haddr : addr.consumeStack ≤ concrete.machineState.stack.length)
      (hfind : σ.find? addr = some account),
        (concretizeAccountMap concrete σ hσ).find?
          (concretizeExpr concrete addr haddr) =
            some (concretizeAccount concrete account
              (accountConsumeStack_of_find? hσ hfind)))

def CurrentAccountFound (σ : AccountMap) : Prop :=
  ∃ account, σ.find? Expr.Address = some account

lemma concretizeRuntimeCode_isEmpty
    (concrete : Ethereum.State)
    (code : RuntimeCode) :
    (concretizeRuntimeCode concrete code).isEmpty = code.isEmpty := by
  cases code with
  | concrete code => simp [concretizeRuntimeCode, RuntimeCode.isEmpty]
  | symbolic code =>
      by_cases h : code.isEmpty
      · simp [concretizeRuntimeCode, RuntimeCode.isEmpty, h]
        rfl
      · simp [concretizeRuntimeCode, RuntimeCode.isEmpty, h]
        rfl

lemma concretizeAccount_emptyAccount
    {concrete : Ethereum.State}
    {account : Account}
    {h : account.consumeStack ≤ concrete.machineState.stack.length} :
    (concretizeAccount concrete account h).emptyAccount =
      (account.code.isEmpty &&
        (concretizeExpr concrete account.nonce
          (by simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at h; omega) == ⟨0⟩) &&
        (concretizeExpr concrete account.balance
          (by simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at h; omega) == ⟨0⟩)) := by
  simp [concretizeAccount, Ethereum.Account.emptyAccount,
    concretizeRuntimeCode_isEmpty, Bool.and_assoc]
  set nval : UInt256 :=
    concretizeExpr concrete account.nonce
      (by simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at h; omega)
  set bval : UInt256 :=
    concretizeExpr concrete account.balance
      (by simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at h; omega)
  change
    (account.code.isEmpty &&
        (decide (nval = (⟨0⟩ : UInt256)) &&
          decide (bval = (⟨0⟩ : UInt256)))) =
      (account.code.isEmpty &&
        (nval == (⟨0⟩ : UInt256) && bval == (⟨0⟩ : UInt256)))
  rw [UInt256_beq_zero_eq_decide nval, UInt256_beq_zero_eq_decide bval]

lemma concretizeSym_ok_output_none
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    o = .none := by
  cases hconds : checkConditions concrete validJumps sym.conditions with
  | error e' =>
      simp [concretizeSym, hconds, Except.bind, bind] at hbase
  | ok condsProofs =>
      simp [concretizeSym, hconds, Except.bind, bind] at hbase
      exact hbase.2.symm

@[simp] lemma concretizeExprList_length
    {τ : EType}
    {concrete : Ethereum.State}
    {exprs : List (Expr τ)}
    {hstack : Expr.maxConsumesStackList exprs ≤ concrete.machineState.stack.length} :
    (concretizeExprList concrete exprs hstack).length = exprs.length := by
  simp [concretizeExprList]

lemma concretizeExprList_getElem?_some
    {τ : EType}
    {concrete : Ethereum.State}
    {exprs : List (Expr τ)}
    {hstack : Expr.maxConsumesStackList exprs ≤ concrete.machineState.stack.length}
    {idx : Nat}
    {expr : Expr τ}
    (hidx : exprs[idx]? = some expr) :
    (concretizeExprList concrete exprs hstack)[idx]? =
      some (concretizeExpr concrete expr
        (maxListConsume_elem_consume hstack expr (List.mem_of_getElem? hidx))) := by
  simp [concretizeExprList, List.getElem?_map, List.getElem?_attach, hidx,
    concretizeExpr_proof_irrel]

lemma concretizeExprList_proof_irrel
    {τ : EType}
    {concrete : Ethereum.State}
    {exprs : List (Expr τ)}
    {h₁ h₂ : Expr.maxConsumesStackList exprs ≤ concrete.machineState.stack.length} :
    concretizeExprList concrete exprs h₁ = concretizeExprList concrete exprs h₂ := by
  exact congrArg (fun h => concretizeExprList concrete exprs h) (Subsingleton.elim h₁ h₂)

lemma concretizeStack_proof_irrel
    {concrete : Ethereum.State}
    {stack : Expr .stack}
    {h₁ h₂ : stack.consumeStack ≤ concrete.machineState.stack.length} :
    concretizeStack concrete stack h₁ = concretizeStack concrete stack h₂ := by
  exact congrArg (fun h => concretizeStack concrete stack h) (Subsingleton.elim h₁ h₂)

lemma concretizeStack_length
    {concrete : Ethereum.State}
    {known : List (Expr .word)}
    {asp : Nat}
    {hstack : (Expr.Stack known asp).consumeStack ≤ concrete.machineState.stack.length} :
    List.length (concretizeStack concrete (Expr.Stack known asp) hstack) =
      known.length + (concrete.machineState.stack.length - asp) := by
  simp [concretizeStack, List.length_drop]
  exact concretizeExprList_length

lemma concretizeState_stack_length
    {concrete : Ethereum.State}
    {sym : State}
    {known : List (Expr .word)}
    {asp : Nat}
    {hstack : sym.consumeStack ≤ concrete.machineState.stack.length}
    (hstackeq : sym.machineState.stack = Expr.Stack known asp) :
    List.length (concretizeState concrete sym hstack).machineState.stack =
      known.length + (concrete.machineState.stack.length - asp) := by
  simp [concretizeState, concretizeMachineState, hstackeq, concretizeStack_length]

lemma concretizeSym_gasAvailable_eq
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    state.machineState.gasAvailable =
      concretizeExpr concrete sym.evm.machineState.gasAvailable
        (Nat.le_trans (gasAvailable_consumption sym) (concretizeSym_ok_stack_bound hbase)) := by
  obtain ⟨hs, hstate⟩ := if_concretizeOk_then_state hbase
  subst state
  simp [concretizeState, concretizeMachineState, concretizeExpr_proof_irrel]

lemma concretizeSym_activeWords_eq
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    state.machineState.activeWords =
      concretizeExpr concrete sym.evm.machineState.activeWords
        (Nat.le_trans (activeWords_consumption sym) (concretizeSym_ok_stack_bound hbase)) := by
  obtain ⟨hs, hstate⟩ := if_concretizeOk_then_state hbase
  subst state
  simp [concretizeState, concretizeMachineState, concretizeExpr_proof_irrel]

lemma concretizeSym_returnData_eq
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    state.machineState.returnData =
      concretizeExpr concrete sym.evm.machineState.returnData
        (Nat.le_trans (returnData_consumption sym) (concretizeSym_ok_stack_bound hbase)) := by
  obtain ⟨hs, hstate⟩ := if_concretizeOk_then_state hbase
  subst state
  simp [concretizeState, concretizeMachineState, concretizeExpr_proof_irrel]

lemma concretizeSym_accountMap_eq
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    state.accountMap =
      concretizeAccountMap concrete sym.evm.accountMap
        (by
          exact Nat.le_trans
            (by
              have hstate := sym.hevm
              simp [State.consumeStack, maxList] at hstate
              omega)
            (concretizeSym_ok_stack_bound hbase)) := by
  obtain ⟨hs, hstate⟩ := if_concretizeOk_then_state hbase
  subst state
  simp [concretizeState, concretizeAccountMap_proof_irrel]

lemma accountMapFindSound_balanceExpr
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {addr : Expr .addr}
    {haddr : addr.consumeStack ≤ concrete.machineState.stack.length}
    {hbalance : (sym.accountBalanceExpr addr).consumeStack ≤ concrete.machineState.stack.length}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsound : AccountMapFindSound concrete sym.evm.accountMap) :
    concretizeExpr concrete (sym.accountBalanceExpr addr) hbalance =
      (state.accountMap.find? (concretizeExpr concrete addr haddr)).option ⟨0⟩ (·.balance) := by
  have hmapBound : sym.evm.accountMap.consumeStack ≤ concrete.machineState.stack.length := by
    exact Nat.le_trans
      (by
        have hstate := sym.hevm
        simp [State.consumeStack, maxList] at hstate
        omega)
      (concretizeSym_ok_stack_bound hbase)
  have hstateMap := concretizeSym_accountMap_eq hbase
  rw [hstateMap]
  cases hfind : sym.evm.accountMap.find? addr with
  | none =>
      have hs := hsound.1 hmapBound addr haddr hfind
      simp [SymState.accountBalanceExpr, SymState.accountSummary, hfind,
        AccountSummary.missing, AccountSummary.balanceExpr, hs,
        concretizeExpr_lit, concretizeAccountMap_proof_irrel, Option.option]
  | some account =>
      have hs := hsound.2 hmapBound addr account haddr hfind
      simp [SymState.accountBalanceExpr, SymState.accountSummary, hfind,
        Account.summary, AccountSummary.balanceExpr, hs,
        concretizeAccount, concretizeAccount_proof_irrel,
        concretizeAccountMap_proof_irrel, concretizeExpr_proof_irrel, Option.option]

lemma accountMapFindSound_deadExpr_ne_zero
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {addr : Expr .addr}
    {haddr : addr.consumeStack ≤ concrete.machineState.stack.length}
    {hdead : (sym.accountDeadExpr addr).consumeStack ≤
      concrete.machineState.stack.length}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsound : AccountMapFindSound concrete sym.evm.accountMap) :
    (concretizeExpr concrete (sym.accountDeadExpr addr) hdead !=
        (⟨0⟩ : UInt256)) =
      State.dead state.accountMap (concretizeExpr concrete addr haddr) := by
  have hmapBound : sym.evm.accountMap.consumeStack ≤ concrete.machineState.stack.length := by
    exact Nat.le_trans
      (by
        have hstate := sym.hevm
        simp [State.consumeStack, maxList] at hstate
        omega)
      (concretizeSym_ok_stack_bound hbase)
  have hsummaryBound :
      Expr.consumeStackAccountSummary (sym.accountSummary addr) ≤
        concrete.machineState.stack.length := by
    simpa [SymState.accountDeadExpr, AccountSummary.deadExpr, Expr.consumeStack] using hdead
  have hsummary :
      (concretizeAccountSummaryDead concrete (sym.accountSummary addr) hsummaryBound !=
          (⟨0⟩ : UInt256)) =
        State.dead state.accountMap (concretizeExpr concrete addr haddr) := by
    have hstateMap := concretizeSym_accountMap_eq hbase
    rw [hstateMap]
    cases hfind : sym.evm.accountMap.find? addr with
    | none =>
        have hs := hsound.1 hmapBound addr haddr hfind
        simp [SymState.accountSummary, hfind,
          concretizeAccountSummaryDead, AccountSummary.missing, State.dead,
          concretizeExpr_lit, UInt256_ofNat_1, hs,
          concretizeAccountMap_proof_irrel, Option.option]
        rfl
    | some account =>
        have hs := hsound.2 hmapBound addr account haddr hfind
        simp [SymState.accountSummary, hfind,
          concretizeAccountSummaryDead, Account.summary, State.dead,
          concretizeAccount_emptyAccount, concretizeAccount_proof_irrel,
          UInt256_beq_zero_eq_decide, UInt256_ofNat_1, hs,
          concretizeAccountMap_proof_irrel, Option.option,
          UInt256_deadFlag_bne_zero_bool, UInt256_deadFlag_bne_zero_prop,
          Bool.and_assoc]
        set nval : UInt256 :=
          concretizeExpr concrete account.nonce
            (by
              have hacc := accountConsumeStack_of_find? hmapBound hfind
              simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at hacc
              omega)
        set bval : UInt256 :=
          concretizeExpr concrete account.balance
            (by
              have hacc := accountConsumeStack_of_find? hmapBound hfind
              simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at hacc
              omega)
        change
          (account.code.isEmpty &&
              (decide (nval = (⟨0⟩ : UInt256)) &&
                decide (bval = (⟨0⟩ : UInt256)))) =
            (account.code.isEmpty &&
              (nval == (⟨0⟩ : UInt256) && bval == (⟨0⟩ : UInt256)))
        rw [UInt256_beq_zero_eq_decide nval, UInt256_beq_zero_eq_decide bval]
  rw [concretizeExpr.eq_def]
  simpa [SymState.accountDeadExpr, AccountSummary.deadExpr, concretizeExpr_proof_irrel]
    using hsummary

lemma concretizeSym_substate_eq
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    state.substate =
      concretizeSubstate concrete sym.evm.substate
        (by
          exact Nat.le_trans
            (by
              have hstate := sym.hevm
              simp [State.consumeStack, maxList] at hstate
              omega)
            (concretizeSym_ok_stack_bound hbase)) := by
  obtain ⟨hs, hstate⟩ := if_concretizeOk_then_state hbase
  subst state
  simp [concretizeState, concretizeSubstate_proof_irrel]

lemma concretizeSym_machineState_eq
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    state.machineState =
      concretizeMachineState concrete sym.evm.machineState
        (by
          exact Nat.le_trans
            (by
              have hstate := sym.hevm
              simp [State.consumeStack, maxList] at hstate
              omega)
            (concretizeSym_ok_stack_bound hbase)) := by
  obtain ⟨hs, hstate⟩ := if_concretizeOk_then_state hbase
  subst state
  simp [concretizeState, concretizeMachineState_proof_irrel]

lemma concretizeSym_executionEnv_eq
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    state.executionEnv = concrete.executionEnv := by
  obtain ⟨hs, hstate⟩ := if_concretizeOk_then_state hbase
  subst state
  simp [concretizeState]

lemma accountMapFindSound_current_storage
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {hstorage : (sym.accountStorageExpr Expr.Address).consumeStack ≤
      concrete.machineState.stack.length}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsound : AccountMapFindSound concrete sym.evm.accountMap)
    (hcurrent : CurrentAccountFound sym.evm.accountMap) :
    (state.accountMap.find! state.executionEnv.codeOwner).storage =
      concretizeExpr concrete (sym.accountStorageExpr Expr.Address) hstorage := by
  rcases hcurrent with ⟨account, hfind⟩
  have hmapBound : sym.evm.accountMap.consumeStack ≤ concrete.machineState.stack.length := by
    exact Nat.le_trans
      (by
        have hstate := sym.hevm
        simp [State.consumeStack, maxList] at hstate
        omega)
      (concretizeSym_ok_stack_bound hbase)
  have hstateMap := concretizeSym_accountMap_eq hbase
  have hexec := concretizeSym_executionEnv_eq hbase
  have hlookup :=
    hsound.2 hmapBound Expr.Address account
      (by simp [Expr.consumeStack]) hfind
  rw [hstateMap, hexec]
  have hlookup' :
      (concretizeAccountMap concrete sym.evm.accountMap hmapBound).find?
        concrete.executionEnv.codeOwner =
        some (concretizeAccount concrete account
          (accountConsumeStack_of_find? hmapBound hfind)) := by
    simpa [concretizeExpr_address, concretizeExpr_proof_irrel] using hlookup
  simp [SymState.accountStorageExpr, hfind, Batteries.RBMap.find!, hlookup',
    concretizeAccount, concretizeAccount_proof_irrel, concretizeExpr_proof_irrel]

lemma concretizeSym_σ₀_eq
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    state.σ₀ = concrete.σ₀ := by
  obtain ⟨hs, hstate⟩ := if_concretizeOk_then_state hbase
  subst state
  simp [concretizeState]

lemma concretizeSym_stack_eq
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    state.machineState.stack =
      concretizeStack concrete sym.evm.machineState.stack
        (Nat.le_trans (stack_consumption sym) (concretizeSym_ok_stack_bound hbase)) := by
  obtain ⟨hs, hstate⟩ := if_concretizeOk_then_state hbase
  subst state
  simp [concretizeState, concretizeMachineState, concretizeState_proof_irrel]

lemma stack_underflow_bound
    {knownLen asp required concreteLen stateLen : Nat}
    (hknown : knownLen < required)
    (hstateLen : stateLen < required)
    (hstateLen_eq : stateLen = knownLen + (concreteLen - asp)) :
    concreteLen < asp + (required - knownLen) := by
  omega

lemma stack_no_underflow_bound
    {knownLen asp required concreteLen stateLen : Nat}
    (hknown : knownLen < required)
    (hasp : asp ≤ concreteLen)
    (hstateLen : ¬ stateLen < required)
    (hstateLen_eq : stateLen = knownLen + (concreteLen - asp)) :
    ¬ concreteLen < asp + (required - knownLen) := by
  omega

lemma stack_overflow_bound
    {knownLen asp concreteLen stateLen δ α : Nat}
    (hasp : asp ≤ concreteLen)
    (hstateLen_eq : stateLen = knownLen + (concreteLen - asp))
    (hδle : δ ≤ stateLen)
    (hoverflow : 1024 < stateLen - δ + α) :
    concreteLen ≥ asp + (1025 + δ - α - knownLen) := by
  have hrest : 1025 + δ - α - knownLen ≤ concreteLen - asp := by
    rw [hstateLen_eq] at hoverflow hδle
    omega
  omega

lemma stack_no_overflow_bound
    {knownLen asp concreteLen stateLen δ α : Nat}
    (hasp : asp ≤ concreteLen)
    (hstateLen_eq : stateLen = knownLen + (concreteLen - asp))
    (hδle : δ ≤ stateLen)
    (hnotOverflow : ¬ 1024 < stateLen - δ + α) :
    ¬ concreteLen ≥ asp + (1025 + δ - α - knownLen) := by
  intro h
  have hrest : 1025 + δ - α - knownLen ≤ concreteLen - asp := by
    omega
  apply hnotOverflow
  rw [hstateLen_eq]
  omega

lemma concretizeSym_stack_length
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    ∃ known asp,
      sym.evm.machineState.stack = Expr.Stack known asp ∧
      List.length state.machineState.stack =
        known.length + (concrete.machineState.stack.length - asp) ∧
      asp ≤ concrete.machineState.stack.length := by
  obtain ⟨hs, hstate⟩ := if_concretizeOk_then_state hbase
  cases hstackeq : sym.evm.machineState.stack with
  | Stack known asp =>
      refine ⟨known, asp, rfl, ?_, ?_⟩
      · rw [← hstate]
        exact concretizeState_stack_length hstackeq
      · have hs' := hs
        simp [State.consumeStack, MachineState.consumeStack, maxList, hstackeq, Expr.consumeStack] at hs'
        omega

lemma concretizeSym_stackAt_eq
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {idx : Nat}
    {e : { e : Expr .word // e.consumeStack ≤ sym.n }}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hstackAt : sym.stackAt idx = .ok e) :
    concretizeExpr concrete e.1
      (Nat.le_trans e.2 (concretizeSym_ok_stack_bound hbase)) =
      state.machineState.stack[idx]! := by
  obtain ⟨known, asp, hstackExpr, _hlen, _hasp⟩ := concretizeSym_stack_length hbase
  obtain ⟨hs, hstateEq⟩ := if_concretizeOk_then_state hbase
  have hstackBound :
      (Expr.Stack known asp).consumeStack ≤ concrete.machineState.stack.length := by
    simpa [hstackExpr] using
      (Nat.le_trans (stack_consumption sym) (concretizeSym_ok_stack_bound hbase))
  have hstackEq :
      state.machineState.stack =
        concretizeStack concrete (Expr.Stack known asp) hstackBound := by
    subst state
    simp [concretizeState, concretizeMachineState, hstackExpr, concretizeStack_proof_irrel]
  have hknownBound : Expr.maxConsumesStackList known ≤ concrete.machineState.stack.length := by
    have h := hstackBound
    simp [Expr.consumeStack] at h
    exact h.left
  let knownConcrete : List UInt256 := concretizeExprList concrete known hknownBound
  have hknownConcrete_length : knownConcrete.length = known.length := by
    dsimp [knownConcrete, concretizeExprList]
    exact concretizeExprList_length
  simp [SymState.stackAt, SymState.asp, SymState.knownStack, hstackExpr] at hstackAt
  split at hstackAt
  · rename_i hpos
    cases hknown : known[idx]? with
    | some knownExpr =>
        simp [hknown] at hstackAt
        cases hstackAt
        rw [hstackEq]
        have hknownConcr :
            knownConcrete[idx]? =
              some (concretizeExpr concrete knownExpr
                (maxListConsume_elem_consume
                  hknownBound knownExpr (List.mem_of_getElem? hknown))) := by
          dsimp [knownConcrete]
          exact concretizeExprList_getElem?_some
            (concrete := concrete) (hstack := hknownBound) hknown
        have hidxlt : idx < known.length := by
          obtain ⟨hidxlt, _⟩ := List.getElem_of_getElem? hknown
          exact hidxlt
        have hstackOpt :
            (concretizeStack concrete (Expr.Stack known asp) hstackBound)[idx]? =
              some (concretizeExpr concrete knownExpr
                (maxListConsume_elem_consume
                  hknownBound
                  knownExpr
                  (List.mem_of_getElem? hknown))) := by
          change
            (knownConcrete ++ List.drop asp concrete.machineState.stack)[idx]? =
              some (concretizeExpr concrete knownExpr
                (maxListConsume_elem_consume
                  hknownBound
                  knownExpr
                  (List.mem_of_getElem? hknown)))
          rw [List.getElem?_append_left]
          · exact hknownConcr
          · rw [hknownConcrete_length]
            exact hidxlt
        exact Eq.trans concretizeExpr_proof_irrel
          (list_getElem!_eq_of_getElem?_some hstackOpt).symm
    | none =>
        simp [hknown] at hstackAt
        cases hstackAt
        rw [hstackEq]
        let pos := asp + (idx - known.length)
        have hidxge : known.length ≤ idx := List.getElem?_eq_none_iff.mp hknown
        have hposConcrete : pos < concrete.machineState.stack.length := by
          exact Nat.lt_of_lt_of_le hpos (concretizeSym_ok_stack_bound hbase)
        have hstackOpt :
            (concretizeStack concrete (Expr.Stack known asp) hstackBound)[idx]? =
              some (concrete.machineState.stack[pos]) := by
          have hright :
              (concretizeStack concrete (Expr.Stack known asp) hstackBound)[idx]? =
                concrete.machineState.stack[pos]? := by
            change
              (knownConcrete ++ List.drop asp concrete.machineState.stack)[idx]? =
                concrete.machineState.stack[pos]?
            rw [List.getElem?_append_right]
            · rw [List.getElem?_drop]
              congr 1
              rw [hknownConcrete_length]
            · rw [hknownConcrete_length]
              exact hidxge
          rw [hright, List.getElem?_eq_getElem hposConcrete]
        calc
          concretizeExpr concrete (Expr.StackItem (asp + (idx - known.length))) _ =
              concrete.machineState.stack[pos] := by
            simpa [pos] using
              concretizeExpr_stackItem_of_lt
                (concrete := concrete)
                (idx := pos)
                hposConcrete
          _ = (concretizeStack concrete (Expr.Stack known asp) hstackBound)[idx]! :=
              (list_getElem!_eq_of_getElem?_some hstackOpt).symm
  · simp at hstackAt

lemma concretizeExpr_caccess_state
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {addr : Expr .addr}
    {h : (Expr.Caccess addr sym.evm.substate.accessedAccounts).consumeStack ≤
      concrete.machineState.stack.length}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o)) :
    concretizeExpr concrete (Expr.Caccess addr sym.evm.substate.accessedAccounts) h =
      Caccess
        (concretizeExpr concrete addr (by
          have h' := h
          simp [Expr.consumeStack] at h'
          exact h'.left))
        state.substate := by
  rw [concretizeExpr.eq_def]
  simp [Caccess, concretizeSym_substate_eq hbase, concretizeSubstate,
    concretizeExprList_proof_irrel, concretizeExpr_proof_irrel]
  congr

lemma concretizeExpr_csload_state
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {slot : Expr .word}
    {h : (Expr.Csload slot sym.evm.substate.accessedStorageKeys).consumeStack ≤
      concrete.machineState.stack.length}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hslot :
      concretizeExpr concrete slot (by
        have h' := h
        simp [Expr.consumeStack] at h'
        exact h'.left) =
      state.machineState.stack[0]!) :
    concretizeExpr concrete (Expr.Csload slot sym.evm.substate.accessedStorageKeys) h =
      Csload state.machineState.stack state.substate state.executionEnv := by
  rw [concretizeExpr.eq_def]
  simp [Csload, concretizeSym_substate_eq hbase, concretizeSym_executionEnv_eq hbase,
    concretizeSubstate, concretizeExprList_proof_irrel, concretizeExpr_proof_irrel,
    hslot]
  congr

lemma concretizeSym_addCondition_ok
    {s b : Nat}
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {c : Condition s b}
    {h : s ≤ sym.n}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hcond : ∀ hs, (checkCondition concrete validJumps c hs).isOk = true) :
    concretizeSym concrete validJumps (addCondition sym c h) = .ok (state, o) := by
  cases hconds : checkConditions concrete validJumps sym.conditions with
  | error e' =>
      simp [concretizeSym, hconds, Except.bind, bind] at hbase
  | ok condsProofs =>
      have hbase' := hbase
      simp [concretizeSym, hconds, Except.bind, bind] at hbase'
      cases hcheck : checkCondition concrete validJumps c (Nat.le_trans h condsProofs.down) with
      | error e =>
          have hcond' := hcond (Nat.le_trans h condsProofs.down)
          simp [hcheck, Except.isOk, Except.toBool] at hcond'
      | ok condProof =>
          simp [concretizeSym, addCondition, checkConditions, hconds, hcheck, Except.bind, bind]
          simpa [concretizeState_proof_irrel] using hbase'

lemma checkCondition_stackGE_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {n : Nat}
    {hs : 0 ≤ concrete.machineState.stack.length}
    (hlen : concrete.machineState.stack.length < n) :
    checkCondition concrete validJumps (.stackGE n) hs = .error .StackUnderflow := by
  simp [checkCondition, hlen]
  rfl

lemma checkCondition_stackGE_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {n : Nat}
    {hs : 0 ≤ concrete.machineState.stack.length}
    (hlen : ¬ concrete.machineState.stack.length < n) :
    (checkCondition concrete validJumps (.stackGE n) hs).isOk = true := by
  simp [checkCondition, hlen, Except.isOk, Except.toBool]

lemma concretizeSym_stackGE_underflow_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {required : Nat}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hknown : sym.knownStack.length < required)
    (hstateLen : List.length state.machineState.stack < required) :
    concretizeSym concrete validJumps
      (addCondition sym
        (.stackGE (sym.asp + (required - sym.knownStack.length)))
        (by simp)) =
      .error .StackUnderflow := by
  apply concretizeSym_addCondition_error hbase
  intro hs
  apply checkCondition_stackGE_error
  obtain ⟨known, asp, hstackeq, hlen, _hasp⟩ := concretizeSym_stack_length hbase
  simp [SymState.knownStack, SymState.asp, hstackeq] at hknown ⊢
  exact stack_underflow_bound hknown hstateLen hlen

lemma concretizeSym_stackGE_no_underflow_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {required : Nat}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hknown : sym.knownStack.length < required)
    (hstateLen : ¬ List.length state.machineState.stack < required) :
    concretizeSym concrete validJumps
      (addCondition sym
        (.stackGE (sym.asp + (required - sym.knownStack.length)))
        (by simp)) =
      .ok (state, o) := by
  apply concretizeSym_addCondition_ok hbase
  intro hs
  obtain ⟨known, asp, hstackeq, hlen, hasp⟩ := concretizeSym_stack_length hbase
  have hknown' : known.length < required := by
    simpa [SymState.knownStack, hstackeq] using hknown
  have hnot : ¬ concrete.machineState.stack.length < asp + (required - known.length) :=
    stack_no_underflow_bound hknown' hasp hstateLen hlen
  unfold SymState.knownStack SymState.asp
  rw [hstackeq]
  exact checkCondition_stackGE_ok (validJumps := validJumps) (hs := hs) hnot

lemma concretizeSym_stackUnderflowCondition_no_underflow_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hstateLen : ¬ List.length state.machineState.stack < (δ w).getD 0) :
    concretizeSym concrete validJumps
      (symZApplyStackUnderflowCondition w sym) =
      .ok (state, o) := by
  unfold symZApplyStackUnderflowCondition
  by_cases hknown : sym.knownStack.length < (δ w).getD 0
  · simp [hknown]
    exact concretizeSym_stackGE_no_underflow_ok hbase hknown hstateLen
  · simp [hknown, hbase]

lemma knownStack_lt_of_state_stack_underflow
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {required : Nat}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hstateLen : List.length state.machineState.stack < required) :
    sym.knownStack.length < required := by
  obtain ⟨known, asp, hstackeq, hlen, _hasp⟩ := concretizeSym_stack_length hbase
  simp [SymState.knownStack, hstackeq]
  omega

lemma checkCondition_stackLT_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {n : Nat}
    {hs : 0 ≤ concrete.machineState.stack.length}
    (hlen : concrete.machineState.stack.length ≥ n) :
    checkCondition concrete validJumps (.stackLT n) hs = .error .StackOverflow := by
  simp [checkCondition, hlen]
  rfl

lemma checkCondition_stackLT_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {n : Nat}
    {hs : 0 ≤ concrete.machineState.stack.length}
    (hlen : ¬ concrete.machineState.stack.length ≥ n) :
    (checkCondition concrete validJumps (.stackLT n) hs).isOk = true := by
  simp [checkCondition, hlen, Except.isOk, Except.toBool]

lemma checkCondition_staticMode_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {hs : 0 ≤ concrete.machineState.stack.length}
    (hperm : ¬ concrete.executionEnv.perm) :
    checkCondition concrete validJumps .staticMode hs = .error .StaticModeViolation := by
  simp [checkCondition, hperm]
  rfl

lemma checkCondition_staticMode_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {hs : 0 ≤ concrete.machineState.stack.length}
    (hperm : concrete.executionEnv.perm) :
    (checkCondition concrete validJumps .staticMode hs).isOk = true := by
  simp [checkCondition, hperm, Except.isOk, Except.toBool]

lemma checkCondition_staticModeIfNonzero_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {e : Expr .word}
    {hs : e.consumeStack ≤ concrete.machineState.stack.length}
    (hperm : ¬ concrete.executionEnv.perm)
    (hnz : (concretizeExpr concrete e hs == (⟨0⟩ : UInt256)) = false) :
    checkCondition concrete validJumps (.staticModeIfNonzero e) hs =
      .error .StaticModeViolation := by
  simp [checkCondition, hperm, hnz]
  rfl

lemma checkCondition_staticModeIfNonzero_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {e : Expr .word}
    {hs : e.consumeStack ≤ concrete.machineState.stack.length}
    (hok : concrete.executionEnv.perm ∨
      (concretizeExpr concrete e hs == (⟨0⟩ : UInt256)) = true) :
    (checkCondition concrete validJumps (.staticModeIfNonzero e) hs).isOk = true := by
  cases hok with
  | inl hperm =>
      simp [checkCondition, hperm, Except.isOk, Except.toBool]
  | inr hz =>
      simp [checkCondition, hz, Except.isOk, Except.toBool]

lemma checkCondition_jumpValid_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {d : Expr .word}
    {hs : d.consumeStack ≤ concrete.machineState.stack.length}
    (hbad : notIn (.some (concretizeExpr concrete d hs)) validJumps = true) :
    checkCondition concrete validJumps (.jumpValid d) hs =
      .error .BadJumpDestination := by
  simp [checkCondition, hbad]
  rfl

lemma checkCondition_jumpValid_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {d : Expr .word}
    {hs : d.consumeStack ≤ concrete.machineState.stack.length}
    (hok : notIn (.some (concretizeExpr concrete d hs)) validJumps = false) :
    (checkCondition concrete validJumps (.jumpValid d) hs).isOk = true := by
  simp [checkCondition, hok, Except.isOk, Except.toBool]

lemma checkCondition_jumpiValid_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {d jc : Expr .word}
    {hs : max d.consumeStack jc.consumeStack ≤ concrete.machineState.stack.length}
    (hjcnz :
      ((concretizeExpr concrete jc (by
        exact le_of_max_le_right hs)) == (⟨0⟩ : UInt256)) = false)
    (hbad :
      notIn (.some (concretizeExpr concrete d (by
        exact le_of_max_le_left hs))) validJumps = true) :
    checkCondition concrete validJumps (.jumpiValid d jc) hs =
      .error .BadJumpDestination := by
  simp [checkCondition, hjcnz, hbad]
  rfl

lemma checkCondition_jumpiValid_ok_zero
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {d jc : Expr .word}
    {hs : max d.consumeStack jc.consumeStack ≤ concrete.machineState.stack.length}
    (hjcz :
      ((concretizeExpr concrete jc (by
        exact le_of_max_le_right hs)) == (⟨0⟩ : UInt256)) = true) :
    (checkCondition concrete validJumps (.jumpiValid d jc) hs).isOk = true := by
  simp [checkCondition, hjcz, Except.isOk, Except.toBool]

lemma checkCondition_jumpiValid_ok_valid
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {d jc : Expr .word}
    {hs : max d.consumeStack jc.consumeStack ≤ concrete.machineState.stack.length}
    (hjcnz :
      ((concretizeExpr concrete jc (by
        exact le_of_max_le_right hs)) == (⟨0⟩ : UInt256)) = false)
    (hok :
      notIn (.some (concretizeExpr concrete d (by
        exact le_of_max_le_left hs))) validJumps = false) :
    (checkCondition concrete validJumps (.jumpiValid d jc) hs).isOk = true := by
  simp [checkCondition, hjcnz, hok, Except.isOk, Except.toBool]

lemma checkCondition_assert_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {assertion : Assertion}
    {failure : Failure}
    {hs : assertion.consumeStack ≤ concrete.machineState.stack.length}
    (hassert : concretizeAssertion concrete assertion hs = false) :
    checkCondition concrete validJumps (.assert ⟨assertion, by rfl⟩ failure) hs =
      match failure with
      | .exception e => .error e := by
  cases failure with
  | exception e =>
      simp [checkCondition, hassert]
      rfl

lemma checkCondition_assert_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {assertion : Assertion}
    {failure : Failure}
    {hs : assertion.consumeStack ≤ concrete.machineState.stack.length}
    (hassert : concretizeAssertion concrete assertion hs = true) :
    (checkCondition concrete validJumps (.assert ⟨assertion, by rfl⟩ failure) hs).isOk = true := by
  cases failure with
  | exception e =>
      simp [checkCondition, hassert, Except.isOk, Except.toBool]

lemma concretizeSym_addAssertion_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {assertion : Assertion}
    {failure : Failure}
    {h : assertion.consumeStack ≤ sym.n}
    {e : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hfailure : failure = .exception e)
    (hassert : ∀ hs, concretizeAssertion concrete assertion hs = false) :
    concretizeSym concrete validJumps
      (addCondition sym (.assert ⟨assertion, by rfl⟩ failure) h) =
      .error e := by
  subst failure
  apply concretizeSym_addCondition_error hbase
  intro hs
  exact checkCondition_assert_error (validJumps := validJumps) (failure := .exception e) (hassert hs)

lemma concretizeSym_addAssertion_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {assertion : Assertion}
    {failure : Failure}
    {h : assertion.consumeStack ≤ sym.n}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hassert : ∀ hs, concretizeAssertion concrete assertion hs = true) :
    concretizeSym concrete validJumps
      (addCondition sym (.assert ⟨assertion, by rfl⟩ failure) h) =
      .ok (state, o) := by
  apply concretizeSym_addCondition_ok hbase
  intro hs
  exact checkCondition_assert_ok (validJumps := validJumps) (failure := failure) (hassert hs)

lemma concretizeAssertion_pleq_true
    {concrete : Ethereum.State}
    {a b : Expr .word}
    {hs : (Assertion.PLEq a b).consumeStack ≤ concrete.machineState.stack.length}
    (hle :
      (show UInt256 from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left)) ≤
      (show UInt256 from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right))) :
    concretizeAssertion concrete (.PLEq a b) hs = true := by
  simp [concretizeAssertion, hle]

lemma concretizeAssertion_pleq_false
    {concrete : Ethereum.State}
    {a b : Expr .word}
    {hs : (Assertion.PLEq a b).consumeStack ≤ concrete.machineState.stack.length}
    (hgt :
      (show UInt256 from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right)) <
      (show UInt256 from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left))) :
    concretizeAssertion concrete (.PLEq a b) hs = false := by
  have hnot :
      ¬ (show UInt256 from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left)) ≤
        (show UInt256 from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right)) := by
    intro hle
    exact (Nat.not_le_of_gt hgt) hle
  simp [concretizeAssertion, hnot]

lemma concretizeAssertion_pgeqnat_true
    {concrete : Ethereum.State}
    {a b : Expr .num}
    {hs : (Assertion.PGEqnat a b).consumeStack ≤ concrete.machineState.stack.length}
    (hge :
      (show Nat from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left)) ≥
      (show Nat from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right))) :
    concretizeAssertion concrete (.PGEqnat a b) hs = true := by
  simp [concretizeAssertion, hge]

lemma concretizeAssertion_pgeqnat_false
    {concrete : Ethereum.State}
    {a b : Expr .num}
    {hs : (Assertion.PGEqnat a b).consumeStack ≤ concrete.machineState.stack.length}
    (hlt :
      (show Nat from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left)) <
      (show Nat from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right))) :
    concretizeAssertion concrete (.PGEqnat a b) hs = false := by
  have hnot :
      ¬ (show Nat from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left)) ≥
        (show Nat from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right)) := by
    omega
  simp [concretizeAssertion, hnot]

lemma concretizeAssertion_pgtnat_true
    {concrete : Ethereum.State}
    {a b : Expr .num}
    {hs : (Assertion.PGTnat a b).consumeStack ≤ concrete.machineState.stack.length}
    (hgt :
      (show Nat from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left)) >
      (show Nat from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right))) :
    concretizeAssertion concrete (.PGTnat a b) hs = true := by
  simp [concretizeAssertion, hgt]

lemma concretizeAssertion_pgtnat_false
    {concrete : Ethereum.State}
    {a b : Expr .num}
    {hs : (Assertion.PGTnat a b).consumeStack ≤ concrete.machineState.stack.length}
    (hle :
      (show Nat from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left)) ≤
      (show Nat from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right))) :
    concretizeAssertion concrete (.PGTnat a b) hs = false := by
  have hnot :
      ¬ (show Nat from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left)) >
        (show Nat from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right)) := by
    omega
  simp [concretizeAssertion, hnot]

lemma concretizeAssertion_pleqnat_true
    {concrete : Ethereum.State}
    {a b : Expr .num}
    {hs : (Assertion.PLEqnat a b).consumeStack ≤ concrete.machineState.stack.length}
    (hle :
      (show Nat from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left)) ≤
      (show Nat from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right))) :
    concretizeAssertion concrete (.PLEqnat a b) hs = true := by
  simp [concretizeAssertion, hle]

lemma concretizeAssertion_pleqnat_false
    {concrete : Ethereum.State}
    {a b : Expr .num}
    {hs : (Assertion.PLEqnat a b).consumeStack ≤ concrete.machineState.stack.length}
    (hgt :
      (show Nat from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right)) <
      (show Nat from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left))) :
    concretizeAssertion concrete (.PLEqnat a b) hs = false := by
  have hnot :
      ¬ (show Nat from concretizeExpr concrete a (by simp [Assertion.consumeStack] at hs; exact hs.left)) ≤
        (show Nat from concretizeExpr concrete b (by simp [Assertion.consumeStack] at hs; exact hs.right)) := by
    omega
  simp [concretizeAssertion, hnot]

lemma symZApplyMemoryExpansionAndCharge_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }}
    {err : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error err) :
    concretizeSym concrete validJumps
      (symZApplyMemoryExpansionAndCharge sym cost₁?) = .error err := by
  cases cost₁? with
  | none =>
      simp [symZApplyMemoryExpansionAndCharge, symZApplyMemoryExpansionCondition]
      exact concretizeSym_update_gas_preserve_error hbase
  | some cost₁ =>
      simp [symZApplyMemoryExpansionAndCharge, symZApplyMemoryExpansionCondition]
      apply concretizeSym_update_gas_preserve_error
      apply concretizeSym_addCondition_preserve_error hbase

lemma symZApplyCostCondition_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {cost₂ : { e : Expr .num // e.consumeStack ≤ sym.n }}
    {err : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error err) :
    concretizeSym concrete validJumps
      (symZApplyCostCondition sym cost₂) = .error err := by
  simp [symZApplyCostCondition]
  apply concretizeSym_addCondition_preserve_error hbase

lemma symZApplyStackOverflowCondition_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {w : Operation}
    {err : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error err) :
    concretizeSym concrete validJumps
      (symZApplyStackOverflowCondition w sym) = .error err := by
  simp [symZApplyStackOverflowCondition]
  apply concretizeSym_addCondition_preserve_error hbase

lemma symZApplyStackOverflowCondition_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hδle : (δ w).getD 0 ≤ state.machineState.stack.length)
    (hoverflow :
      1024 < state.machineState.stack.length - (δ w).getD 0 + (α w).getD 0) :
    concretizeSym concrete validJumps
      (symZApplyStackOverflowCondition w sym) = .error .StackOverflow := by
  simp [symZApplyStackOverflowCondition]
  apply concretizeSym_addCondition_error hbase
  intro hs
  apply checkCondition_stackLT_error
  obtain ⟨known, asp, hstackeq, hlen, hasp⟩ := concretizeSym_stack_length hbase
  simp [SymState.knownStack, SymState.asp, hstackeq]
  exact stack_overflow_bound hasp hlen hδle hoverflow

lemma symZApplyStackOverflowCondition_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hδle : (δ w).getD 0 ≤ state.machineState.stack.length)
    (hnotOverflow :
      ¬ 1024 < state.machineState.stack.length - (δ w).getD 0 + (α w).getD 0) :
    concretizeSym concrete validJumps
      (symZApplyStackOverflowCondition w sym) = .ok (state, o) := by
  simp [symZApplyStackOverflowCondition]
  apply concretizeSym_addCondition_ok hbase
  intro hs
  obtain ⟨known, asp, hstackeq, hlen, hasp⟩ := concretizeSym_stack_length hbase
  simp [SymState.knownStack, SymState.asp, hstackeq]
  exact checkCondition_stackLT_ok (validJumps := validJumps) (hs := hs)
    (stack_no_overflow_bound hasp hlen hδle hnotOverflow)

lemma symZApplySstoreStipendCondition_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {w : Operation}
    {err : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error err) :
    concretizeSym concrete validJumps
      (symZApplySstoreStipendCondition w sym) = .error err := by
  by_cases hw : w = .SSTORE
  · simp [symZApplySstoreStipendCondition, hw]
    apply concretizeSym_addCondition_preserve_error hbase
  · simp [symZApplySstoreStipendCondition, hw, hbase]

lemma symZApplySstoreStipendCondition_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hw : w = .SSTORE)
    (hle : state.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend) :
    concretizeSym concrete validJumps
      (symZApplySstoreStipendCondition w sym) = .error .OutOfGass := by
  subst w
  simp [symZApplySstoreStipendCondition]
  apply concretizeSym_addAssertion_error hbase rfl
  intro hs
  apply concretizeAssertion_pgtnat_false
  rw [concretizeExpr_toNat]
  rw [concretizeExpr_natLit]
  simp [concretizeExpr_proof_irrel, ← concretizeSym_gasAvailable_eq hbase]
  exact hle

lemma symZApplySstoreStipendCondition_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hok : w = .SSTORE → GasConstants.Gcallstipend < state.machineState.gasAvailable.toNat) :
    concretizeSym concrete validJumps
      (symZApplySstoreStipendCondition w sym) = .ok (state, o) := by
  by_cases hw : w = .SSTORE
  · subst w
    simp [symZApplySstoreStipendCondition]
    apply concretizeSym_addAssertion_ok hbase
    intro hs
    apply concretizeAssertion_pgtnat_true
    rw [concretizeExpr_toNat]
    rw [concretizeExpr_natLit]
    simp [concretizeExpr_proof_irrel, ← concretizeSym_gasAvailable_eq hbase]
    exact hok rfl
  · simp [symZApplySstoreStipendCondition, hw, hbase]

lemma symZApplyJumpCondition_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {w : Operation}
    {err : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error err)
    (hsym : symZApplyJumpCondition w sym = .ok sym') :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZApplyJumpCondition at hsym
  by_cases hw : w = Operation.JUMP
  · simp [hw, Except.bind, bind] at hsym
    cases hstack : sym.stackAt 0 with
    | error e =>
        simp [hstack, Except.bind, bind] at hsym
    | ok dest =>
        simp [hstack, Except.bind, bind] at hsym
        cases hsym
        apply concretizeSym_addCondition_preserve_error hbase
  · simp [hw, Except.bind, bind] at hsym
    cases hsym
    exact hbase

lemma symZApplyJumpCondition_jump_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyJumpCondition .JUMP sym = .ok sym')
    (hbad : notIn (.some state.machineState.stack[0]!) validJumps = true) :
    concretizeSym concrete validJumps sym' =
      .error .BadJumpDestination := by
  unfold symZApplyJumpCondition at hsym
  simp [Except.bind, bind] at hsym
  cases hdest : sym.stackAt 0 with
  | error e =>
      simp [hdest, Except.bind, bind] at hsym
  | ok dest =>
      simp [hdest, Except.bind, bind] at hsym
      cases hsym
      apply concretizeSym_addCondition_error hbase
      intro hs
      apply checkCondition_jumpValid_error
      have hdestEq :
          concretizeExpr concrete dest.1 hs = state.machineState.stack[0]! := by
        exact Eq.trans concretizeExpr_proof_irrel
          (concretizeSym_stackAt_eq hbase hdest)
      simpa [hdestEq] using hbad

lemma symZApplyJumpCondition_jump_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyJumpCondition .JUMP sym = .ok sym')
    (hok : notIn (.some state.machineState.stack[0]!) validJumps = false) :
    concretizeSym concrete validJumps sym' = .ok (state, o) := by
  unfold symZApplyJumpCondition at hsym
  simp [Except.bind, bind] at hsym
  cases hdest : sym.stackAt 0 with
  | error e =>
      simp [hdest, Except.bind, bind] at hsym
  | ok dest =>
      simp [hdest, Except.bind, bind] at hsym
      cases hsym
      apply concretizeSym_addCondition_ok hbase
      intro hs
      apply checkCondition_jumpValid_ok
      have hdestEq :
          concretizeExpr concrete dest.1 hs = state.machineState.stack[0]! := by
        exact Eq.trans concretizeExpr_proof_irrel
          (concretizeSym_stackAt_eq hbase hdest)
      simpa [hdestEq] using hok

lemma symZApplyJumpCondition_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {w : Operation}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyJumpCondition w sym = .ok sym')
    (hnotbad :
      ¬ (w = .JUMP ∧ notIn (.some state.machineState.stack[0]!) validJumps = true)) :
    concretizeSym concrete validJumps sym' = .ok (state, o) := by
  unfold symZApplyJumpCondition at hsym
  by_cases hw : w = .JUMP
  · subst w
    simp [Except.bind, bind] at hsym
    cases hdest : sym.stackAt 0 with
    | error e =>
        simp [hdest, Except.bind, bind] at hsym
    | ok dest =>
        simp [hdest, Except.bind, bind] at hsym
        cases hsym
        apply concretizeSym_addCondition_ok hbase
        intro hs
        apply checkCondition_jumpValid_ok
        have hdestEq :
            concretizeExpr concrete dest.1 hs = state.machineState.stack[0]! := by
          exact Eq.trans concretizeExpr_proof_irrel
            (concretizeSym_stackAt_eq hbase hdest)
        have hok : notIn (.some state.machineState.stack[0]!) validJumps = false := by
          have hnot : ¬ notIn (.some state.machineState.stack[0]!) validJumps = true := by
            intro hbad
            exact hnotbad ⟨rfl, hbad⟩
          exact Bool.eq_false_of_not_eq_true hnot
        simpa [hdestEq] using hok
  · simp [hw, Except.bind, bind] at hsym
    cases hsym
    exact hbase

lemma symZApplyJumpiCondition_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {w : Operation}
    {err : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error err)
    (hsym : symZApplyJumpiCondition w sym = .ok sym') :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZApplyJumpiCondition at hsym
  by_cases hw : w = Operation.JUMPI
  · simp [hw, Except.bind, bind] at hsym
    cases hdest : sym.stackAt 0 with
    | error e =>
        simp [hdest, Except.bind, bind] at hsym
    | ok dest =>
        simp [hdest, Except.bind, bind] at hsym
        cases hjcond : sym.stackAt 1 with
        | error e =>
            simp [hjcond, Except.bind, bind] at hsym
        | ok jcond =>
            simp [hjcond, Except.bind, bind] at hsym
            cases hsym
            apply concretizeSym_addCondition_preserve_error hbase
  · simp [hw, Except.bind, bind] at hsym
    cases hsym
    exact hbase

lemma symZApplyJumpiCondition_jumpi_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyJumpiCondition .JUMPI sym = .ok sym')
    (hjcnz : (state.machineState.stack[1]! == (⟨0⟩ : UInt256)) = false)
    (hbad : notIn (.some state.machineState.stack[0]!) validJumps = true) :
    concretizeSym concrete validJumps sym' =
      .error .BadJumpDestination := by
  unfold symZApplyJumpiCondition at hsym
  simp [Except.bind, bind] at hsym
  cases hdest : sym.stackAt 0 with
  | error e =>
      simp [hdest, Except.bind, bind] at hsym
  | ok dest =>
      simp [hdest, Except.bind, bind] at hsym
      cases hjcond : sym.stackAt 1 with
      | error e =>
          simp [hjcond, Except.bind, bind] at hsym
      | ok jcond =>
          simp [hjcond, Except.bind, bind] at hsym
          cases hsym
          apply concretizeSym_addCondition_error hbase
          intro hs
          apply checkCondition_jumpiValid_error
          · have hjcondEq :
                concretizeExpr concrete jcond.1 (le_of_max_le_right hs) =
                  state.machineState.stack[1]! := by
              exact Eq.trans concretizeExpr_proof_irrel
                (concretizeSym_stackAt_eq hbase hjcond)
            simpa [hjcondEq] using hjcnz
          · have hdestEq :
                concretizeExpr concrete dest.1 (le_of_max_le_left hs) =
                  state.machineState.stack[0]! := by
              exact Eq.trans concretizeExpr_proof_irrel
                (concretizeSym_stackAt_eq hbase hdest)
            simpa [hdestEq] using hbad

lemma symZApplyJumpiCondition_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {w : Operation}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyJumpiCondition w sym = .ok sym')
    (hok :
      w = .JUMPI →
        ((state.machineState.stack[1]! == (⟨0⟩ : UInt256)) = true ∨
          notIn (.some state.machineState.stack[0]!) validJumps = false)) :
    concretizeSym concrete validJumps sym' = .ok (state, o) := by
  unfold symZApplyJumpiCondition at hsym
  by_cases hw : w = .JUMPI
  · subst w
    simp [Except.bind, bind] at hsym
    cases hdest : sym.stackAt 0 with
    | error e =>
        simp [hdest, Except.bind, bind] at hsym
    | ok dest =>
        simp [hdest, Except.bind, bind] at hsym
        cases hjcond : sym.stackAt 1 with
        | error e =>
            simp [hjcond, Except.bind, bind] at hsym
        | ok jcond =>
            simp [hjcond, Except.bind, bind] at hsym
            cases hsym
            apply concretizeSym_addCondition_ok hbase
            intro hs
            have hdestEq :
                concretizeExpr concrete dest.1 (le_of_max_le_left hs) =
                  state.machineState.stack[0]! := by
              exact Eq.trans concretizeExpr_proof_irrel
                (concretizeSym_stackAt_eq hbase hdest)
            have hjcondEq :
                concretizeExpr concrete jcond.1 (le_of_max_le_right hs) =
                  state.machineState.stack[1]! := by
              exact Eq.trans concretizeExpr_proof_irrel
                (concretizeSym_stackAt_eq hbase hjcond)
            rcases hok rfl with hjcz | hdestOk
            · apply checkCondition_jumpiValid_ok_zero
              simpa [hjcondEq] using hjcz
            · by_cases hjczActual :
                  ((concretizeExpr concrete jcond.1 (le_of_max_le_right hs)) ==
                    (⟨0⟩ : UInt256)) = true
              · exact checkCondition_jumpiValid_ok_zero hjczActual
              · apply checkCondition_jumpiValid_ok_valid
                · exact Bool.eq_false_of_not_eq_true hjczActual
                · simpa [hdestEq] using hdestOk
  · simp [hw, Except.bind, bind] at hsym
    cases hsym
    exact hbase

lemma symZApplyReturnDataCopyCondition_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {w : Operation}
    {err : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error err)
    (hsym : symZApplyReturnDataCopyCondition w sym = .ok sym') :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZApplyReturnDataCopyCondition at hsym
  by_cases hw : w = Operation.RETURNDATACOPY
  · simp [hw, Except.bind, bind] at hsym
    cases hs1 : sym.stackAt 1 with
    | error e =>
        simp [hs1, Except.bind, bind] at hsym
    | ok s1 =>
        simp [hs1, Except.bind, bind] at hsym
        cases hs2 : sym.stackAt 2 with
        | error e =>
            simp [hs2, Except.bind, bind] at hsym
        | ok s2 =>
            simp [hs2, Except.bind, bind] at hsym
            cases hsym
            apply concretizeSym_addCondition_preserve_error hbase
  · simp [hw, Except.bind, bind] at hsym
    cases hsym
    exact hbase

lemma symZApplyReturnDataCopyCondition_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyReturnDataCopyCondition .RETURNDATACOPY sym = .ok sym')
    (hgt :
      state.machineState.returnData.size <
        (state.machineState.stack.getD 1 ⟨0⟩).toNat +
          (state.machineState.stack.getD 2 ⟨0⟩).toNat) :
    concretizeSym concrete validJumps sym' = .error .InvalidMemoryAccess := by
  unfold symZApplyReturnDataCopyCondition at hsym
  simp [Except.bind, bind] at hsym
  cases hs1 : sym.stackAt 1 with
  | error e =>
      simp [hs1, Except.bind, bind] at hsym
  | ok s1 =>
      simp [hs1, Except.bind, bind] at hsym
      cases hs2 : sym.stackAt 2 with
      | error e =>
          simp [hs2, Except.bind, bind] at hsym
      | ok s2 =>
          simp [hs2, Except.bind, bind] at hsym
          cases hsym
          apply concretizeSym_addAssertion_error hbase rfl
          intro hs
          apply concretizeAssertion_pleqnat_false
          rw [concretizeExpr_addNat]
          rw [concretizeExpr_toNat]
          rw [concretizeExpr_toNat]
          rw [concretizeExpr_bufLengthNat]
          simp [concretizeExpr_proof_irrel,
            concretizeSym_stackAt_eq hbase hs1,
            concretizeSym_stackAt_eq hbase hs2,
            ← concretizeSym_returnData_eq hbase]
          exact hgt

lemma symZApplyReturnDataCopyCondition_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyReturnDataCopyCondition w sym = .ok sym')
    (hok :
      w = .RETURNDATACOPY →
        (state.machineState.stack.getD 1 ⟨0⟩).toNat +
            (state.machineState.stack.getD 2 ⟨0⟩).toNat ≤
          state.machineState.returnData.size) :
    concretizeSym concrete validJumps sym' = .ok (state, o) := by
  unfold symZApplyReturnDataCopyCondition at hsym
  by_cases hw : w = Operation.RETURNDATACOPY
  · simp [hw, Except.bind, bind] at hsym
    cases hs1 : sym.stackAt 1 with
    | error e =>
        simp [hs1, Except.bind, bind] at hsym
    | ok s1 =>
        simp [hs1, Except.bind, bind] at hsym
        cases hs2 : sym.stackAt 2 with
        | error e =>
            simp [hs2, Except.bind, bind] at hsym
        | ok s2 =>
            simp [hs2, Except.bind, bind] at hsym
            cases hsym
            apply concretizeSym_addAssertion_ok hbase
            intro hs
            apply concretizeAssertion_pleqnat_true
            rw [concretizeExpr_addNat]
            rw [concretizeExpr_toNat]
            rw [concretizeExpr_toNat]
            rw [concretizeExpr_bufLengthNat]
            simp [concretizeExpr_proof_irrel,
              concretizeSym_stackAt_eq hbase hs1,
              concretizeSym_stackAt_eq hbase hs2,
              ← concretizeSym_returnData_eq hbase]
            exact hok hw
  · simp [hw, Except.bind, bind] at hsym
    cases hsym
    exact hbase

lemma symZApplyStaticModeCondition_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {w : Operation}
    {err : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error err)
    (hsym : symZApplyStaticModeCondition w sym = .ok sym') :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZApplyStaticModeCondition at hsym
  by_cases hstatic :
      w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE]
  · simp [hstatic, Except.bind, bind] at hsym
    cases hsym
    apply concretizeSym_addCondition_preserve_error hbase
  · simp [hstatic, Except.bind, bind] at hsym
    by_cases hcall : w = .CALL
    · simp [hcall, Except.bind, bind] at hsym
      cases hvalue : sym.stackAt 2 with
      | error e =>
          simp [hvalue, Except.bind, bind] at hsym
      | ok value =>
          simp [hvalue, Except.bind, bind] at hsym
          cases hsym
          apply concretizeSym_addCondition_preserve_error hbase
    · simp [hcall, Except.bind, bind] at hsym
      cases hsym
      exact hbase

lemma symZApplyStaticModeCondition_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyStaticModeCondition w sym = .ok sym')
    (hperm : ¬ state.executionEnv.perm)
    (hviol :
      w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
        (w = .CALL ∧ (state.machineState.stack[2]! == (⟨0⟩ : UInt256)) = false)) :
    concretizeSym concrete validJumps sym' = .error .StaticModeViolation := by
  have hpermConcrete : ¬ concrete.executionEnv.perm := by
    simpa [← concretizeSym_executionEnv_eq hbase] using hperm
  unfold symZApplyStaticModeCondition at hsym
  by_cases hstatic :
      w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE]
  · simp [hstatic, Except.bind, bind] at hsym
    cases hsym
    apply concretizeSym_addCondition_error hbase
    intro hs
    exact checkCondition_staticMode_error (validJumps := validJumps) hpermConcrete
  · simp [hstatic, Except.bind, bind] at hsym
    rcases hviol with hviolStatic | hviolCall
    · exact False.elim (hstatic hviolStatic)
    · rcases hviolCall with ⟨hcall, hvalueNeZero⟩
      simp [hcall, Except.bind, bind] at hsym
      cases hvalue : sym.stackAt 2 with
      | error e =>
          simp [hvalue, Except.bind, bind] at hsym
      | ok value =>
          simp [hvalue, Except.bind, bind] at hsym
          cases hsym
          apply concretizeSym_addCondition_error hbase
          intro hs
          apply checkCondition_staticModeIfNonzero_error hpermConcrete
          have hvalueEq :
              concretizeExpr concrete value.1
                (Nat.le_trans value.2 (concretizeSym_ok_stack_bound hbase)) =
                state.machineState.stack[2]! :=
            concretizeSym_stackAt_eq hbase hvalue
          simpa [concretizeExpr_proof_irrel, hvalueEq] using hvalueNeZero

lemma symZApplyStaticModeCondition_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyStaticModeCondition w sym = .ok sym')
    (hok :
      state.executionEnv.perm ∨
        (w ∉ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT,
            .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∧
          (w = .CALL →
            (state.machineState.stack[2]! == (⟨0⟩ : UInt256)) = true))) :
    concretizeSym concrete validJumps sym' = .ok (state, o) := by
  have hpermConcrete :
      state.executionEnv.perm → concrete.executionEnv.perm := by
    intro hperm
    simpa [← concretizeSym_executionEnv_eq hbase] using hperm
  unfold symZApplyStaticModeCondition at hsym
  by_cases hstatic :
      w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE]
  · simp [hstatic, Except.bind, bind] at hsym
    cases hsym
    rcases hok with hperm | hnot
    · apply concretizeSym_addCondition_ok hbase
      intro hs
      exact checkCondition_staticMode_ok (validJumps := validJumps) (hpermConcrete hperm)
    · exact False.elim (hnot.1 hstatic)
  · simp [hstatic, Except.bind, bind] at hsym
    by_cases hcall : w = .CALL
    · simp [hcall, Except.bind, bind] at hsym
      cases hvalue : sym.stackAt 2 with
      | error e =>
          simp [hvalue, Except.bind, bind] at hsym
      | ok value =>
          simp [hvalue, Except.bind, bind] at hsym
          cases hsym
          apply concretizeSym_addCondition_ok hbase
          intro hs
          apply checkCondition_staticModeIfNonzero_ok
          rcases hok with hperm | hnot
          · exact Or.inl (hpermConcrete hperm)
          · right
            have hvalueEq :
                concretizeExpr concrete value.1
                  (Nat.le_trans value.2 (concretizeSym_ok_stack_bound hbase)) =
                  state.machineState.stack[2]! :=
              concretizeSym_stackAt_eq hbase hvalue
            simpa [concretizeExpr_proof_irrel, hvalueEq] using hnot.2 hcall
    · simp [hcall, Except.bind, bind] at hsym
      cases hsym
      exact hbase

lemma symZApplyCreateSizeCondition_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {w : Operation}
    {err : ExecutionException}
  (hbase : concretizeSym concrete validJumps sym = .error err)
    (hsym : symZApplyCreateSizeCondition w sym = .ok sym') :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZApplyCreateSizeCondition at hsym
  by_cases hcreate : w = .CREATE ∨ w = .CREATE2
  · simp [hcreate, Except.bind, bind] at hsym
    cases hs2 : sym.stackAt 2 with
    | error e =>
        simp [hs2, Except.bind, bind] at hsym
    | ok s2 =>
        simp [hs2, Except.bind, bind] at hsym
        cases hsym
        apply concretizeSym_addCondition_preserve_error hbase
  · simp [hcreate, Except.bind, bind] at hsym
    cases hsym
    exact hbase

lemma symZApplyCreateSizeCondition_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyCreateSizeCondition w sym = .ok sym')
    (hcreate : w = .CREATE ∨ w = .CREATE2)
    (hgt : state.machineState.stack[2]! > (⟨49152⟩ : UInt256)) :
    concretizeSym concrete validJumps sym' = .error .OutOfGass := by
  unfold symZApplyCreateSizeCondition at hsym
  simp [hcreate, Except.bind, bind] at hsym
  cases hs2 : sym.stackAt 2 with
  | error e =>
      simp [hs2, Except.bind, bind] at hsym
  | ok s2 =>
      simp [hs2, Except.bind, bind] at hsym
      cases hsym
      apply concretizeSym_addAssertion_error hbase rfl
      intro hs
      apply concretizeAssertion_pleq_false
      rw [concretizeExpr_lit]
      have hs2Eq :
          concretizeExpr concrete s2.1
            (by simp [Assertion.consumeStack] at hs; exact hs.left) =
          state.machineState.stack[2]! := by
        exact Eq.trans concretizeExpr_proof_irrel
          (concretizeSym_stackAt_eq hbase hs2)
      simpa [hs2Eq] using hgt

lemma symZApplyCreateSizeCondition_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsym : symZApplyCreateSizeCondition w sym = .ok sym')
    (hok :
      w = .CREATE ∨ w = .CREATE2 →
        state.machineState.stack[2]! ≤ (⟨49152⟩ : UInt256)) :
    concretizeSym concrete validJumps sym' = .ok (state, o) := by
  unfold symZApplyCreateSizeCondition at hsym
  by_cases hcreate : w = .CREATE ∨ w = .CREATE2
  · simp [hcreate, Except.bind, bind] at hsym
    cases hs2 : sym.stackAt 2 with
    | error e =>
        simp [hs2, Except.bind, bind] at hsym
    | ok s2 =>
        simp [hs2, Except.bind, bind] at hsym
        cases hsym
        apply concretizeSym_addAssertion_ok hbase
        intro hs
        apply concretizeAssertion_pleq_true
        rw [concretizeExpr_lit]
        have hs2Eq :
            concretizeExpr concrete s2.1
              (by simp [Assertion.consumeStack] at hs; exact hs.left) =
            state.machineState.stack[2]! := by
          exact Eq.trans concretizeExpr_proof_irrel
            (concretizeSym_stackAt_eq hbase hs2)
        simpa [hs2Eq] using hok hcreate
  · simp [hcreate, Except.bind, bind] at hsym
    cases hsym
    exact hbase

lemma symZCore_preserve_concretize_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {w : Operation}
    {cost₂ : Expr .num}
    {err : ExecutionException}
    (hbase : concretizeSym concrete validJumps sym = .error err)
    (hsym : symZCore w sym = .ok (cost₂, sym')) :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZCore at hsym
  cases hmem : symMemoryExpansionCost sym w with
  | error e =>
      simp [hmem, Except.bind, bind] at hsym
  | ok cost₁ =>
      let sym1 := symZApplyMemoryExpansionAndCharge sym cost₁
      have h1 : concretizeSym concrete validJumps sym1 = .error err := by
        dsimp [sym1]
        exact symZApplyMemoryExpansionAndCharge_preserve_error hbase
      cases hc2 : symC' sym1 w with
      | error e =>
          simp [hmem, sym1, hc2, Except.bind, bind] at hsym
      | ok cost₂' =>
          let sym2 := symZApplyCostCondition sym1 cost₂'
          have h2 : concretizeSym concrete validJumps sym2 = .error err := by
            dsimp [sym2]
            exact symZApplyCostCondition_preserve_error h1
          cases hjump : symZApplyJumpCondition w sym2 with
          | error e =>
              simp [hmem, sym1, hc2, sym2, hjump, Except.bind, bind] at hsym
          | ok sym3 =>
              have h3 : concretizeSym concrete validJumps sym3 = .error err :=
                symZApplyJumpCondition_preserve_error h2 hjump
              cases hjumpi : symZApplyJumpiCondition w sym3 with
              | error e =>
                  simp [hmem, sym1, hc2, sym2, hjump, hjumpi, Except.bind, bind] at hsym
              | ok sym4 =>
                  have h4 : concretizeSym concrete validJumps sym4 = .error err :=
                    symZApplyJumpiCondition_preserve_error h3 hjumpi
                  cases hret : symZApplyReturnDataCopyCondition w sym4 with
                  | error e =>
                      simp [hmem, sym1, hc2, sym2, hjump, hjumpi, hret, Except.bind, bind] at hsym
                  | ok sym5 =>
                      have h5 : concretizeSym concrete validJumps sym5 = .error err :=
                        symZApplyReturnDataCopyCondition_preserve_error h4 hret
                      let sym6 := symZApplyStackOverflowCondition w sym5
                      have h6 : concretizeSym concrete validJumps sym6 = .error err := by
                        dsimp [sym6]
                        exact symZApplyStackOverflowCondition_preserve_error h5
                      cases hstatic : symZApplyStaticModeCondition w sym6 with
                      | error e =>
                          simp [hmem, sym1, hc2, sym2, hjump, hjumpi, hret, sym6, hstatic,
                            Except.bind, bind] at hsym
                      | ok sym7 =>
                          have h7 : concretizeSym concrete validJumps sym7 = .error err :=
                            symZApplyStaticModeCondition_preserve_error h6 hstatic
                          let sym8 := symZApplySstoreStipendCondition w sym7
                          have h8 : concretizeSym concrete validJumps sym8 = .error err := by
                            dsimp [sym8]
                            exact symZApplySstoreStipendCondition_preserve_error h7
                          cases hcreate : symZApplyCreateSizeCondition w sym8 with
                          | error e =>
                              simp [hmem, sym1, hc2, sym2, hjump, hjumpi, hret, sym6, hstatic,
                                sym8, hcreate, Except.bind, bind] at hsym
                          | ok sym9 =>
                              have h9 : concretizeSym concrete validJumps sym9 = .error err :=
                                symZApplyCreateSizeCondition_preserve_error h8 hcreate
                              simp [hmem, sym1, hc2, sym2, hjump, hjumpi, hret, sym6, hstatic,
                                sym8, hcreate, Except.bind, bind] at hsym
                              cases hsym
                              exact h9

lemma symZCore_memoryExpansionCost_ok
    {sym sym' : SymState}
    {w : Operation}
    {cost₂ : Expr .num}
    (hcore : symZCore w sym = .ok (cost₂, sym')) :
    ∃ cost₁?, symMemoryExpansionCost sym w = .ok cost₁? := by
  unfold symZCore at hcore
  cases hmem : symMemoryExpansionCost sym w with
  | error e =>
      simp [hmem, Except.bind, bind] at hcore
  | ok cost₁? =>
      exact ⟨cost₁?, rfl⟩

lemma memoryExpansionCost_zero_of_symMemoryExpansionCost_none
    {sym : SymState}
    {state : Ethereum.State}
    {w : Operation}
    (hmem : symMemoryExpansionCost sym w = .ok none) :
    memoryExpansionCost state w = 0 := by
  cases w <;> (try rename_i op) <;> (try cases op) <;>
    simp [symMemoryExpansionCost, symMemoryExpansionCost.memExpandWith,
      symMemoryExpansionCost.memExpandCall, memoryExpansionCost, memoryExpansionCost.μᵢ',
      Except.bind, bind, pure] at hmem ⊢
  all_goals
    repeat
      first
      | cases hmem
      | split at hmem
      | simp [pure] at hmem

@[simp] lemma Cₘ_ofNat_toNat (u : UInt256) :
    Cₘ (UInt256.ofNat u.toNat) = Cₘ u := by
  simp [Cₘ, UInt256.ofNat, UInt256.toNat, Id.run]

lemma UInt256_toNat_lt_size (u : UInt256) :
    u.toNat < UInt256.size := by
  simp [UInt256.toNat, u.val.2]

lemma UInt256_ofNat_toNat_of_lt {n : Nat} (hn : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  simp [UInt256.ofNat, UInt256.toNat, Id.run, Nat.mod_eq_of_lt hn]

lemma MachineState_M_lt_uint256_size {s f l : Nat}
    (hs : s < UInt256.size)
    (hf : f < UInt256.size)
    (hl : l < UInt256.size) :
    MachineState.M s f l < UInt256.size := by
  unfold MachineState.M
  split
  · exact hs
  · apply max_lt hs
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
    have hf' : f ≤ UInt256.size - 1 := Nat.le_pred_of_lt hf
    have hl' : l ≤ UInt256.size - 1 := Nat.le_pred_of_lt hl
    have hsum : f + l + 31 ≤ (UInt256.size - 1) + (UInt256.size - 1) + 31 := by
      exact Nat.add_le_add_right (Nat.add_le_add hf' hl') 31
    have hsize : (UInt256.size - 1) + (UInt256.size - 1) + 31 < UInt256.size * 32 := by
      unfold UInt256.size
      norm_num
    exact Nat.lt_of_le_of_lt hsum hsize

lemma concretize_memExpandWith_cost
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {i j : Nat}
    {si sj : { e : Expr .word // e.consumeStack ≤ sym.n }}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsi : sym.stackAt i = .ok si)
    (hsj : sym.stackAt j = .ok sj)
    {hcost :
      (Expr.SubNat
        (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords si sj))
        (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords))).consumeStack ≤
        concrete.machineState.stack.length} :
    concretizeExpr concrete
      (Expr.SubNat
        (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords si sj))
        (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords)))
      hcost =
      Cₘ (UInt256.ofNat
        (MachineState.M state.machineState.activeWords.toNat
          state.machineState.stack[i]!.toNat
          state.machineState.stack[j]!.toNat)) -
        Cₘ state.machineState.activeWords := by
  rw [concretizeExpr_subNat, concretizeExpr_cₘ, concretizeExpr_m, concretizeExpr_cₘ,
    concretizeExpr_toNat]
  simp [concretizeExpr_proof_irrel, Cₘ_ofNat_toNat,
    ← concretizeSym_activeWords_eq hbase,
    concretizeSym_stackAt_eq hbase hsi,
    concretizeSym_stackAt_eq hbase hsj]

lemma concretize_memExpandLit_cost
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {i : Nat}
    {si : { e : Expr .word // e.consumeStack ≤ sym.n }}
    {lit : UInt256}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsi : sym.stackAt i = .ok si)
    {hcost :
      (Expr.SubNat
        (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords si (Expr.Lit lit)))
        (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords))).consumeStack ≤
        concrete.machineState.stack.length} :
    concretizeExpr concrete
      (Expr.SubNat
        (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords si (Expr.Lit lit)))
        (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords)))
      hcost =
      Cₘ (UInt256.ofNat
        (MachineState.M state.machineState.activeWords.toNat
          state.machineState.stack[i]!.toNat
          lit.toNat)) -
        Cₘ state.machineState.activeWords := by
  rw [concretizeExpr_subNat, concretizeExpr_cₘ, concretizeExpr_m,
    concretizeExpr_lit, concretizeExpr_cₘ, concretizeExpr_toNat]
  simp [concretizeExpr_proof_irrel, Cₘ_ofNat_toNat,
    ← concretizeSym_activeWords_eq hbase,
    concretizeSym_stackAt_eq hbase hsi]

lemma concretize_memExpandMcopy_cost
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {s0 s1 s2 : { e : Expr .word // e.consumeStack ≤ sym.n }}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hs0 : sym.stackAt 0 = .ok s0)
    (hs1 : sym.stackAt 1 = .ok s1)
    (hs2 : sym.stackAt 2 = .ok s2)
    {hcost :
      (Expr.SubNat
        (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords (Expr.Max s0 s1) s2))
        (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords))).consumeStack ≤
        concrete.machineState.stack.length} :
    concretizeExpr concrete
      (Expr.SubNat
        (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords (Expr.Max s0 s1) s2))
        (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords)))
      hcost =
      Cₘ (UInt256.ofNat
        (MachineState.M state.machineState.activeWords.toNat
          (max state.machineState.stack[0]!.toNat state.machineState.stack[1]!.toNat)
          state.machineState.stack[2]!.toNat)) -
        Cₘ state.machineState.activeWords := by
  rw [concretizeExpr_subNat, concretizeExpr_cₘ, concretizeExpr_m,
    concretizeExpr_max, concretizeExpr_cₘ, concretizeExpr_toNat]
  simp [concretizeExpr_proof_irrel, Cₘ_ofNat_toNat, UInt256_max_toNat,
    ← concretizeSym_activeWords_eq hbase,
    concretizeSym_stackAt_eq hbase hs0,
    concretizeSym_stackAt_eq hbase hs1,
    concretizeSym_stackAt_eq hbase hs2]

lemma concretize_memExpandCall_cost
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {i j k l : Nat}
    {si sj sk sl : { e : Expr .word // e.consumeStack ≤ sym.n }}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsi : sym.stackAt i = .ok si)
    (hsj : sym.stackAt j = .ok sj)
    (hsk : sym.stackAt k = .ok sk)
    (hsl : sym.stackAt l = .ok sl)
    {hcost :
      (Expr.SubNat
        (Expr.Cₘ
          (Expr.M
            (Expr.ofNat (Expr.M sym.evm.machineState.activeWords si sj))
            sk sl))
        (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords))).consumeStack ≤
        concrete.machineState.stack.length} :
    concretizeExpr concrete
      (Expr.SubNat
        (Expr.Cₘ
          (Expr.M
            (Expr.ofNat (Expr.M sym.evm.machineState.activeWords si sj))
            sk sl))
        (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords)))
      hcost =
      Cₘ (UInt256.ofNat
        (MachineState.M
          (MachineState.M state.machineState.activeWords.toNat
            state.machineState.stack[i]!.toNat
            state.machineState.stack[j]!.toNat)
          state.machineState.stack[k]!.toNat
          state.machineState.stack[l]!.toNat)) -
        Cₘ state.machineState.activeWords := by
  rw [concretizeExpr_subNat, concretizeExpr_cₘ, concretizeExpr_m,
    concretizeExpr_ofNat, concretizeExpr_m, concretizeExpr_cₘ,
    concretizeExpr_toNat]
  simp [concretizeExpr_proof_irrel, Cₘ_ofNat_toNat,
    ← concretizeSym_activeWords_eq hbase,
    concretizeSym_stackAt_eq hbase hsi,
    concretizeSym_stackAt_eq hbase hsj,
    concretizeSym_stackAt_eq hbase hsk,
    concretizeSym_stackAt_eq hbase hsl]
  rw [UInt256_ofNat_toNat_of_lt (MachineState_M_lt_uint256_size
    (UInt256_toNat_lt_size state.machineState.activeWords)
    (UInt256_toNat_lt_size (state.machineState.stack[i]?.getD default))
    (UInt256_toNat_lt_size (state.machineState.stack[j]?.getD default)))]

lemma symMemoryExpansionCost_some_concretize
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    {cost₁ : { e : Expr .num // e.consumeStack ≤ sym.n }}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hmem : symMemoryExpansionCost sym w = .ok (some cost₁)) :
    concretizeExpr concrete cost₁.1
      (Nat.le_trans cost₁.2 (concretizeSym_ok_stack_bound hbase)) =
      memoryExpansionCost state w := by
  cases w <;> (try rename_i op) <;> (try cases op) <;>
    simp [symMemoryExpansionCost, symMemoryExpansionCost.memExpandWith,
      symMemoryExpansionCost.memExpandCall, memoryExpansionCost, memoryExpansionCost.μᵢ',
      Except.bind, bind, pure] at hmem ⊢
  all_goals
    repeat
      first
      | cases hmem
      | split at hmem
      | simp [pure] at hmem
  all_goals
    first
    | simpa using (concretize_memExpandWith_cost hbase (by assumption) (by assumption))
    | simpa using (concretize_memExpandLit_cost hbase (lit := ⟨32⟩) (by assumption))
    | simpa using (concretize_memExpandLit_cost hbase (lit := ⟨1⟩) (by assumption))
    | simpa using (concretize_memExpandMcopy_cost hbase (by assumption) (by assumption) (by assumption))
    | simpa using (concretize_memExpandCall_cost hbase (by assumption) (by assumption) (by assumption) (by assumption))

lemma symZCore_after_memory_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {w : Operation}
    {cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }}
    {cost₂ : Expr .num}
    {err : ExecutionException}
    (hmem : symMemoryExpansionCost sym w = .ok cost₁?)
    (hbase :
      concretizeSym concrete validJumps
        (symZApplyMemoryExpansionAndCharge sym cost₁?) = .error err)
    (hcore : symZCore w sym = .ok (cost₂, sym')) :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZCore at hcore
  simp [hmem, Except.bind, bind] at hcore
  cases hc2 : symC' (symZApplyMemoryExpansionAndCharge sym cost₁?) w with
  | error e =>
      simp [hc2, Except.bind, bind] at hcore
  | ok cost₂' =>
      simp [hc2, Except.bind, bind] at hcore
      let sym2 := symZApplyCostCondition (symZApplyMemoryExpansionAndCharge sym cost₁?) cost₂'
      have h2 : concretizeSym concrete validJumps sym2 = .error err := by
        dsimp [sym2]
        exact symZApplyCostCondition_preserve_error hbase
      cases hjump : symZApplyJumpCondition w sym2 with
      | error e =>
          simp [sym2, hjump, Except.bind, bind] at hcore
      | ok sym3 =>
          have h3 : concretizeSym concrete validJumps sym3 = .error err :=
            symZApplyJumpCondition_preserve_error h2 hjump
          cases hjumpi : symZApplyJumpiCondition w sym3 with
          | error e =>
              simp [sym2, hjump, hjumpi, Except.bind, bind] at hcore
          | ok sym4 =>
              have h4 : concretizeSym concrete validJumps sym4 = .error err :=
                symZApplyJumpiCondition_preserve_error h3 hjumpi
              cases hret : symZApplyReturnDataCopyCondition w sym4 with
              | error e =>
                  simp [sym2, hjump, hjumpi, hret, Except.bind, bind] at hcore
              | ok sym5 =>
                  have h5 : concretizeSym concrete validJumps sym5 = .error err :=
                    symZApplyReturnDataCopyCondition_preserve_error h4 hret
                  let sym6 := symZApplyStackOverflowCondition w sym5
                  have h6 : concretizeSym concrete validJumps sym6 = .error err := by
                    dsimp [sym6]
                    exact symZApplyStackOverflowCondition_preserve_error h5
                  cases hstatic : symZApplyStaticModeCondition w sym6 with
                  | error e =>
                      simp [sym2, hjump, hjumpi, hret, sym6, hstatic, Except.bind, bind] at hcore
                  | ok sym7 =>
                      have h7 : concretizeSym concrete validJumps sym7 = .error err :=
                        symZApplyStaticModeCondition_preserve_error h6 hstatic
                      let sym8 := symZApplySstoreStipendCondition w sym7
                      have h8 : concretizeSym concrete validJumps sym8 = .error err := by
                        dsimp [sym8]
                        exact symZApplySstoreStipendCondition_preserve_error h7
                      cases hcreate : symZApplyCreateSizeCondition w sym8 with
                      | error e =>
                          simp [sym2, hjump, hjumpi, hret, sym6, hstatic, sym8, hcreate,
                            Except.bind, bind] at hcore
                      | ok sym9 =>
                          have h9 : concretizeSym concrete validJumps sym9 = .error err :=
                            symZApplyCreateSizeCondition_preserve_error h8 hcreate
                          simp [sym2, hjump, hjumpi, hret, sym6, hstatic, sym8, hcreate,
                            Except.bind, bind] at hcore
                          cases hcore
                          exact h9

lemma symZApplyMemoryExpansionAndCharge_mem_oog
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    {cost₁ : { e : Expr .num // e.consumeStack ≤ sym.n }}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hcost :
      concretizeExpr concrete cost₁.1
        (Nat.le_trans cost₁.2 (concretizeSym_ok_stack_bound hbase)) =
        memoryExpansionCost state w)
    (hlt : state.machineState.gasAvailable.toNat < memoryExpansionCost state w) :
    concretizeSym concrete validJumps
      (symZApplyMemoryExpansionAndCharge sym (some cost₁)) =
      .error .OutOfGass := by
  simp [symZApplyMemoryExpansionAndCharge, symZApplyMemoryExpansionCondition]
  apply concretizeSym_update_gas_preserve_error
  apply concretizeSym_addAssertion_error hbase rfl
  intro hs
  apply concretizeAssertion_pgeqnat_false
  rw [concretizeExpr_toNat]
  simp [concretizeExpr_proof_irrel, ← concretizeSym_gasAvailable_eq hbase, hcost]
  exact hlt

lemma symZApplyMemoryExpansionAndCharge_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    {cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hmem : symMemoryExpansionCost sym w = .ok cost₁?)
    (hgas : ¬ state.machineState.gasAvailable.toNat < memoryExpansionCost state w) :
    concretizeSym concrete validJumps
      (symZApplyMemoryExpansionAndCharge sym cost₁?) =
      .ok ({ state with machineState := { state.machineState with
        gasAvailable := state.machineState.gasAvailable - UInt256.ofNat (memoryExpansionCost state w) } }, o) := by
  cases cost₁? with
  | none =>
      have hzero : memoryExpansionCost state w = 0 :=
        memoryExpansionCost_zero_of_symMemoryExpansionCost_none hmem
      simp [symZApplyMemoryExpansionAndCharge, symZApplyMemoryExpansionCondition]
      have hupdate := concretizeSym_update_gas_ok
        (concrete := concrete) (validJumps := validJumps) (sym := sym)
        (state := state) (o := o)
        (e := Expr.Sub sym.evm.machineState.gasAvailable (Expr.Lit ⟨0⟩))
        (h := by
          simp [Expr.consumeStack]
          exact gasAvailable_consumption sym)
        hbase
      simpa [hzero, Option.option, concretizeExpr_sub, concretizeExpr_lit,
        concretizeExpr_proof_irrel, ← concretizeSym_gasAvailable_eq hbase,
        UInt256_subzero, UInt256_subzero'] using hupdate
  | some cost₁ =>
      have hcost :
          concretizeExpr concrete cost₁.1
            (Nat.le_trans cost₁.2 (concretizeSym_ok_stack_bound hbase)) =
            memoryExpansionCost state w :=
        symMemoryExpansionCost_some_concretize hbase hmem
      simp [symZApplyMemoryExpansionAndCharge, symZApplyMemoryExpansionCondition]
      have hcond :
          concretizeSym concrete validJumps
            (addCondition sym
              (.assert
                ⟨Assertion.PGEqnat (Expr.toNat sym.evm.machineState.gasAvailable) cost₁, by rfl⟩
                (.exception .OutOfGass))
              (by
                simp [Assertion.consumeStack, Expr.consumeStack]
                exact ⟨gasAvailable_consumption sym, cost₁.2⟩)) =
            .ok (state, o) := by
        apply concretizeSym_addAssertion_ok hbase
        intro hs
        apply concretizeAssertion_pgeqnat_true
        rw [concretizeExpr_toNat]
        simp [concretizeExpr_proof_irrel, ← concretizeSym_gasAvailable_eq hbase, hcost]
        omega
      have hupdate := concretizeSym_update_gas_ok
        (concrete := concrete) (validJumps := validJumps)
        (sym := addCondition sym
          (.assert
            ⟨Assertion.PGEqnat (Expr.toNat sym.evm.machineState.gasAvailable) cost₁, by rfl⟩
            (.exception .OutOfGass))
          (by
            simp [Assertion.consumeStack, Expr.consumeStack]
            exact ⟨gasAvailable_consumption sym, cost₁.2⟩))
        (state := state) (o := o)
        (e := Expr.Sub sym.evm.machineState.gasAvailable (Expr.ofNat cost₁.1))
        (h := by
          simp [Expr.consumeStack, addCondition]
          exact ⟨gasAvailable_consumption sym, cost₁.2⟩)
        hcond
      simpa [concretizeExpr_sub, concretizeExpr_ofNat, concretizeExpr_proof_irrel,
        ← concretizeSym_gasAvailable_eq hbase, hcost] using hupdate

lemma symZApplyCostCondition_oog
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {cost₂ : { e : Expr .num // e.consumeStack ≤ sym.n }}
    {concreteCost : Nat}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hcost :
      concretizeExpr concrete cost₂.1
        (Nat.le_trans cost₂.2 (concretizeSym_ok_stack_bound hbase)) =
        concreteCost)
    (hlt : state.machineState.gasAvailable.toNat < concreteCost) :
    concretizeSym concrete validJumps
      (symZApplyCostCondition sym cost₂) =
      .error .OutOfGass := by
  simp [symZApplyCostCondition]
  apply concretizeSym_addAssertion_error hbase rfl
  intro hs
  apply concretizeAssertion_pgeqnat_false
  rw [concretizeExpr_toNat]
  simp [concretizeExpr_proof_irrel, ← concretizeSym_gasAvailable_eq hbase, hcost]
  exact hlt

lemma symZApplyCostCondition_ok
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {cost₂ : { e : Expr .num // e.consumeStack ≤ sym.n }}
    {concreteCost : Nat}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hcost :
      concretizeExpr concrete cost₂.1
        (Nat.le_trans cost₂.2 (concretizeSym_ok_stack_bound hbase)) =
        concreteCost)
    (hge : ¬ state.machineState.gasAvailable.toNat < concreteCost) :
    concretizeSym concrete validJumps
      (symZApplyCostCondition sym cost₂) =
      .ok (state, o) := by
  simp [symZApplyCostCondition]
  apply concretizeSym_addAssertion_ok hbase
  intro hs
  apply concretizeAssertion_pgeqnat_true
  rw [concretizeExpr_toNat]
  simp [concretizeExpr_proof_irrel, ← concretizeSym_gasAvailable_eq hbase, hcost]
  omega

lemma symZCore_after_cost_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' : SymState}
    {w : Operation}
    {cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }}
    {cost₂' : { e : Expr .num // e.consumeStack ≤ (symZApplyMemoryExpansionAndCharge sym cost₁?).n }}
    {cost₂ : Expr .num}
    {err : ExecutionException}
    (hmem : symMemoryExpansionCost sym w = .ok cost₁?)
    (hc2 : symC' (symZApplyMemoryExpansionAndCharge sym cost₁?) w = .ok cost₂')
    (hbase :
      concretizeSym concrete validJumps
        (symZApplyCostCondition (symZApplyMemoryExpansionAndCharge sym cost₁?) cost₂') =
        .error err)
    (hcore : symZCore w sym = .ok (cost₂, sym')) :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZCore at hcore
  simp [hmem, hc2, Except.bind, bind] at hcore
  let sym2 := symZApplyCostCondition (symZApplyMemoryExpansionAndCharge sym cost₁?) cost₂'
  cases hjump : symZApplyJumpCondition w sym2 with
  | error e =>
      simp [sym2, hjump, Except.bind, bind] at hcore
  | ok sym3 =>
      have h3 : concretizeSym concrete validJumps sym3 = .error err :=
        symZApplyJumpCondition_preserve_error hbase hjump
      cases hjumpi : symZApplyJumpiCondition w sym3 with
      | error e =>
          simp [sym2, hjump, hjumpi, Except.bind, bind] at hcore
      | ok sym4 =>
          have h4 : concretizeSym concrete validJumps sym4 = .error err :=
            symZApplyJumpiCondition_preserve_error h3 hjumpi
          cases hret : symZApplyReturnDataCopyCondition w sym4 with
          | error e =>
              simp [sym2, hjump, hjumpi, hret, Except.bind, bind] at hcore
          | ok sym5 =>
              have h5 : concretizeSym concrete validJumps sym5 = .error err :=
                symZApplyReturnDataCopyCondition_preserve_error h4 hret
              let sym6 := symZApplyStackOverflowCondition w sym5
              have h6 : concretizeSym concrete validJumps sym6 = .error err := by
                dsimp [sym6]
                exact symZApplyStackOverflowCondition_preserve_error h5
              cases hstatic : symZApplyStaticModeCondition w sym6 with
              | error e =>
                  simp [sym2, hjump, hjumpi, hret, sym6, hstatic, Except.bind, bind] at hcore
              | ok sym7 =>
                  have h7 : concretizeSym concrete validJumps sym7 = .error err :=
                    symZApplyStaticModeCondition_preserve_error h6 hstatic
                  let sym8 := symZApplySstoreStipendCondition w sym7
                  have h8 : concretizeSym concrete validJumps sym8 = .error err := by
                    dsimp [sym8]
                    exact symZApplySstoreStipendCondition_preserve_error h7
                  cases hcreate : symZApplyCreateSizeCondition w sym8 with
                  | error e =>
                      simp [sym2, hjump, hjumpi, hret, sym6, hstatic, sym8, hcreate,
                        Except.bind, bind] at hcore
                  | ok sym9 =>
                      have h9 : concretizeSym concrete validJumps sym9 = .error err :=
                        symZApplyCreateSizeCondition_preserve_error h8 hcreate
                      simp [sym2, hjump, hjumpi, hret, sym6, hstatic, sym8, hcreate,
                        Except.bind, bind] at hcore
                      cases hcore
                      exact h9

lemma symZCore_after_jump_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' sym3 : SymState}
    {w : Operation}
    {cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }}
    {cost₂' : { e : Expr .num // e.consumeStack ≤ (symZApplyMemoryExpansionAndCharge sym cost₁?).n }}
    {cost₂ : Expr .num}
    {err : ExecutionException}
    (hmem : symMemoryExpansionCost sym w = .ok cost₁?)
    (hc2 : symC' (symZApplyMemoryExpansionAndCharge sym cost₁?) w = .ok cost₂')
    (hjump :
      symZApplyJumpCondition w
        (symZApplyCostCondition
          (symZApplyMemoryExpansionAndCharge sym cost₁?) cost₂') =
        .ok sym3)
    (hbase : concretizeSym concrete validJumps sym3 = .error err)
    (hcore : symZCore w sym = .ok (cost₂, sym')) :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZCore at hcore
  simp [hmem, hc2, hjump, Except.bind, bind] at hcore
  cases hjumpi : symZApplyJumpiCondition w sym3 with
  | error e =>
      simp [hjumpi, Except.bind, bind] at hcore
  | ok sym4 =>
      have h4 : concretizeSym concrete validJumps sym4 = .error err :=
        symZApplyJumpiCondition_preserve_error hbase hjumpi
      cases hret : symZApplyReturnDataCopyCondition w sym4 with
      | error e =>
          simp [hjumpi, hret, Except.bind, bind] at hcore
      | ok sym5 =>
          have h5 : concretizeSym concrete validJumps sym5 = .error err :=
            symZApplyReturnDataCopyCondition_preserve_error h4 hret
          let sym6 := symZApplyStackOverflowCondition w sym5
          have h6 : concretizeSym concrete validJumps sym6 = .error err := by
            dsimp [sym6]
            exact symZApplyStackOverflowCondition_preserve_error h5
          cases hstatic : symZApplyStaticModeCondition w sym6 with
          | error e =>
              simp [hjumpi, hret, sym6, hstatic, Except.bind, bind] at hcore
          | ok sym7 =>
              have h7 : concretizeSym concrete validJumps sym7 = .error err :=
                symZApplyStaticModeCondition_preserve_error h6 hstatic
              let sym8 := symZApplySstoreStipendCondition w sym7
              have h8 : concretizeSym concrete validJumps sym8 = .error err := by
                dsimp [sym8]
                exact symZApplySstoreStipendCondition_preserve_error h7
              cases hcreate : symZApplyCreateSizeCondition w sym8 with
              | error e =>
                  simp [hjumpi, hret, sym6, hstatic, sym8, hcreate,
                    Except.bind, bind] at hcore
              | ok sym9 =>
                  have h9 : concretizeSym concrete validJumps sym9 = .error err :=
                    symZApplyCreateSizeCondition_preserve_error h8 hcreate
                  simp [hjumpi, hret, sym6, hstatic, sym8, hcreate,
                    Except.bind, bind] at hcore
                  cases hcore
                  exact h9

lemma symZCore_after_jumpi_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' sym3 sym4 : SymState}
    {w : Operation}
    {cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }}
    {cost₂' : { e : Expr .num // e.consumeStack ≤ (symZApplyMemoryExpansionAndCharge sym cost₁?).n }}
    {cost₂ : Expr .num}
    {err : ExecutionException}
    (hmem : symMemoryExpansionCost sym w = .ok cost₁?)
    (hc2 : symC' (symZApplyMemoryExpansionAndCharge sym cost₁?) w = .ok cost₂')
    (hjump :
      symZApplyJumpCondition w
        (symZApplyCostCondition
          (symZApplyMemoryExpansionAndCharge sym cost₁?) cost₂') =
        .ok sym3)
    (hjumpi : symZApplyJumpiCondition w sym3 = .ok sym4)
    (hbase : concretizeSym concrete validJumps sym4 = .error err)
    (hcore : symZCore w sym = .ok (cost₂, sym')) :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZCore at hcore
  simp [hmem, hc2, hjump, hjumpi, Except.bind, bind] at hcore
  cases hret : symZApplyReturnDataCopyCondition w sym4 with
  | error e =>
      simp [hret, Except.bind, bind] at hcore
  | ok sym5 =>
      have h5 : concretizeSym concrete validJumps sym5 = .error err :=
        symZApplyReturnDataCopyCondition_preserve_error hbase hret
      let sym6 := symZApplyStackOverflowCondition w sym5
      have h6 : concretizeSym concrete validJumps sym6 = .error err := by
        dsimp [sym6]
        exact symZApplyStackOverflowCondition_preserve_error h5
      cases hstatic : symZApplyStaticModeCondition w sym6 with
      | error e =>
          simp [hret, sym6, hstatic, Except.bind, bind] at hcore
      | ok sym7 =>
          have h7 : concretizeSym concrete validJumps sym7 = .error err :=
            symZApplyStaticModeCondition_preserve_error h6 hstatic
          let sym8 := symZApplySstoreStipendCondition w sym7
          have h8 : concretizeSym concrete validJumps sym8 = .error err := by
            dsimp [sym8]
            exact symZApplySstoreStipendCondition_preserve_error h7
          cases hcreate : symZApplyCreateSizeCondition w sym8 with
          | error e =>
              simp [hret, sym6, hstatic, sym8, hcreate, Except.bind, bind] at hcore
          | ok sym9 =>
              have h9 : concretizeSym concrete validJumps sym9 = .error err :=
                symZApplyCreateSizeCondition_preserve_error h8 hcreate
              simp [hret, sym6, hstatic, sym8, hcreate, Except.bind, bind] at hcore
              cases hcore
              exact h9

lemma symZCore_after_returnDataCopy_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' sym3 sym4 sym5 : SymState}
    {w : Operation}
    {cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }}
    {cost₂' : { e : Expr .num // e.consumeStack ≤ (symZApplyMemoryExpansionAndCharge sym cost₁?).n }}
    {cost₂ : Expr .num}
    {err : ExecutionException}
    (hmem : symMemoryExpansionCost sym w = .ok cost₁?)
    (hc2 : symC' (symZApplyMemoryExpansionAndCharge sym cost₁?) w = .ok cost₂')
    (hjump :
      symZApplyJumpCondition w
        (symZApplyCostCondition
          (symZApplyMemoryExpansionAndCharge sym cost₁?) cost₂') =
        .ok sym3)
    (hjumpi : symZApplyJumpiCondition w sym3 = .ok sym4)
    (hret : symZApplyReturnDataCopyCondition w sym4 = .ok sym5)
    (hbase : concretizeSym concrete validJumps sym5 = .error err)
    (hcore : symZCore w sym = .ok (cost₂, sym')) :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZCore at hcore
  simp [hmem, hc2, hjump, hjumpi, hret, Except.bind, bind] at hcore
  let sym6 := symZApplyStackOverflowCondition w sym5
  have h6 : concretizeSym concrete validJumps sym6 = .error err := by
    dsimp [sym6]
    exact symZApplyStackOverflowCondition_preserve_error hbase
  cases hstatic : symZApplyStaticModeCondition w sym6 with
  | error e =>
      simp [sym6, hstatic, Except.bind, bind] at hcore
  | ok sym7 =>
      have h7 : concretizeSym concrete validJumps sym7 = .error err :=
        symZApplyStaticModeCondition_preserve_error h6 hstatic
      let sym8 := symZApplySstoreStipendCondition w sym7
      have h8 : concretizeSym concrete validJumps sym8 = .error err := by
        dsimp [sym8]
        exact symZApplySstoreStipendCondition_preserve_error h7
      cases hcreate : symZApplyCreateSizeCondition w sym8 with
      | error e =>
          simp [sym6, hstatic, sym8, hcreate, Except.bind, bind] at hcore
      | ok sym9 =>
          have h9 : concretizeSym concrete validJumps sym9 = .error err :=
            symZApplyCreateSizeCondition_preserve_error h8 hcreate
          simp [sym6, hstatic, sym8, hcreate, Except.bind, bind] at hcore
          cases hcore
          exact h9

lemma symZCore_after_stackOverflow_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' sym3 sym4 sym5 : SymState}
    {w : Operation}
    {cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }}
    {cost₂' : { e : Expr .num // e.consumeStack ≤ (symZApplyMemoryExpansionAndCharge sym cost₁?).n }}
    {cost₂ : Expr .num}
    {err : ExecutionException}
    (hmem : symMemoryExpansionCost sym w = .ok cost₁?)
    (hc2 : symC' (symZApplyMemoryExpansionAndCharge sym cost₁?) w = .ok cost₂')
    (hjump :
      symZApplyJumpCondition w
        (symZApplyCostCondition
          (symZApplyMemoryExpansionAndCharge sym cost₁?) cost₂') =
        .ok sym3)
    (hjumpi : symZApplyJumpiCondition w sym3 = .ok sym4)
    (hret : symZApplyReturnDataCopyCondition w sym4 = .ok sym5)
    (hbase :
      concretizeSym concrete validJumps
        (symZApplyStackOverflowCondition w sym5) = .error err)
    (hcore : symZCore w sym = .ok (cost₂, sym')) :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZCore at hcore
  simp [hmem, hc2, hjump, hjumpi, hret, Except.bind, bind] at hcore
  let sym6 := symZApplyStackOverflowCondition w sym5
  have h6 : concretizeSym concrete validJumps sym6 = .error err := by
    simpa [sym6] using hbase
  cases hstatic : symZApplyStaticModeCondition w sym6 with
  | error e =>
      simp [sym6, hstatic, Except.bind, bind] at hcore
  | ok sym7 =>
      have h7 : concretizeSym concrete validJumps sym7 = .error err :=
        symZApplyStaticModeCondition_preserve_error h6 hstatic
      let sym8 := symZApplySstoreStipendCondition w sym7
      have h8 : concretizeSym concrete validJumps sym8 = .error err := by
        dsimp [sym8]
        exact symZApplySstoreStipendCondition_preserve_error h7
      cases hcreate : symZApplyCreateSizeCondition w sym8 with
      | error e =>
          simp [sym6, hstatic, sym8, hcreate, Except.bind, bind] at hcore
      | ok sym9 =>
          have h9 : concretizeSym concrete validJumps sym9 = .error err :=
            symZApplyCreateSizeCondition_preserve_error h8 hcreate
          simp [sym6, hstatic, sym8, hcreate, Except.bind, bind] at hcore
          cases hcore
          exact h9

lemma symZCore_after_staticMode_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' sym3 sym4 sym5 sym6 sym7 : SymState}
    {w : Operation}
    {cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }}
    {cost₂' : { e : Expr .num // e.consumeStack ≤ (symZApplyMemoryExpansionAndCharge sym cost₁?).n }}
    {cost₂ : Expr .num}
    {err : ExecutionException}
    (hmem : symMemoryExpansionCost sym w = .ok cost₁?)
    (hc2 : symC' (symZApplyMemoryExpansionAndCharge sym cost₁?) w = .ok cost₂')
    (hjump :
      symZApplyJumpCondition w
        (symZApplyCostCondition
          (symZApplyMemoryExpansionAndCharge sym cost₁?) cost₂') =
        .ok sym3)
    (hjumpi : symZApplyJumpiCondition w sym3 = .ok sym4)
    (hret : symZApplyReturnDataCopyCondition w sym4 = .ok sym5)
    (hstack : symZApplyStackOverflowCondition w sym5 = sym6)
    (hstatic : symZApplyStaticModeCondition w sym6 = .ok sym7)
    (hbase : concretizeSym concrete validJumps sym7 = .error err)
    (hcore : symZCore w sym = .ok (cost₂, sym')) :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZCore at hcore
  subst sym6
  simp [hmem, hc2, hjump, hjumpi, hret, hstatic, Except.bind, bind] at hcore
  let sym8 := symZApplySstoreStipendCondition w sym7
  have h8 : concretizeSym concrete validJumps sym8 = .error err := by
    dsimp [sym8]
    exact symZApplySstoreStipendCondition_preserve_error hbase
  cases hcreate : symZApplyCreateSizeCondition w sym8 with
  | error e =>
      simp [sym8, hcreate, Except.bind, bind] at hcore
  | ok sym9 =>
      have h9 : concretizeSym concrete validJumps sym9 = .error err :=
        symZApplyCreateSizeCondition_preserve_error h8 hcreate
      simp [sym8, hcreate, Except.bind, bind] at hcore
      cases hcore
      exact h9

lemma symZCore_after_sstoreStipend_preserve_error
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym sym' sym3 sym4 sym5 sym6 sym7 : SymState}
    {w : Operation}
    {cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }}
    {cost₂' : { e : Expr .num // e.consumeStack ≤ (symZApplyMemoryExpansionAndCharge sym cost₁?).n }}
    {cost₂ : Expr .num}
    {err : ExecutionException}
    (hmem : symMemoryExpansionCost sym w = .ok cost₁?)
    (hc2 : symC' (symZApplyMemoryExpansionAndCharge sym cost₁?) w = .ok cost₂')
    (hjump :
      symZApplyJumpCondition w
        (symZApplyCostCondition
          (symZApplyMemoryExpansionAndCharge sym cost₁?) cost₂') =
        .ok sym3)
    (hjumpi : symZApplyJumpiCondition w sym3 = .ok sym4)
    (hret : symZApplyReturnDataCopyCondition w sym4 = .ok sym5)
    (hstack : symZApplyStackOverflowCondition w sym5 = sym6)
    (hstatic : symZApplyStaticModeCondition w sym6 = .ok sym7)
    (hbase :
      concretizeSym concrete validJumps
        (symZApplySstoreStipendCondition w sym7) = .error err)
    (hcore : symZCore w sym = .ok (cost₂, sym')) :
    concretizeSym concrete validJumps sym' = .error err := by
  unfold symZCore at hcore
  subst sym6
  simp [hmem, hc2, hjump, hjumpi, hret, hstatic, Except.bind, bind] at hcore
  let sym8 := symZApplySstoreStipendCondition w sym7
  have h8 : concretizeSym concrete validJumps sym8 = .error err := by
    simpa [sym8] using hbase
  cases hcreate : symZApplyCreateSizeCondition w sym8 with
  | error e =>
      simp [sym8, hcreate, Except.bind, bind] at hcore
  | ok sym9 =>
      have h9 : concretizeSym concrete validJumps sym9 = .error err :=
        symZApplyCreateSizeCondition_preserve_error h8 hcreate
      simp [sym8, hcreate, Except.bind, bind] at hcore
      cases hcore
      exact h9

lemma symC'_concretize
    {concrete : Ethereum.State}
    {validJumps : Array UInt256}
    {sym : SymState}
    {state : Ethereum.State}
    {o : Option (Bool × ByteArray)}
    {w : Operation}
    {cost : { e : Expr .num // e.consumeStack ≤ sym.n }}
    (hbase : concretizeSym concrete validJumps sym = .ok (state, o))
    (hsound : AccountMapFindSound concrete sym.evm.accountMap)
    (hcurrent : CurrentAccountFound sym.evm.accountMap)
    (hc : symC' sym w = .ok cost) :
    concretizeExpr concrete cost.1
      (Nat.le_trans cost.2 (concretizeSym_ok_stack_bound hbase)) =
      C' state w := by
  cases w <;> rename_i op <;> cases op <;>
    simp [symC', C', Ethereum.EVM.InstructionGasGroups.Wcopy,
      Ethereum.EVM.InstructionGasGroups.Wextaccount,
      Ethereum.EVM.InstructionGasGroups.Wzero,
      Ethereum.EVM.InstructionGasGroups.Wbase,
      Ethereum.EVM.InstructionGasGroups.Wverylow,
      Ethereum.EVM.InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
      Ethereum.EVM.InstructionGasGroups.Wverylow.dupInstrs,
      Ethereum.EVM.InstructionGasGroups.Wverylow.swapInstrs,
      Ethereum.EVM.InstructionGasGroups.Wlow,
      Ethereum.EVM.InstructionGasGroups.Wmid,
      Ethereum.EVM.InstructionGasGroups.Whigh] at hc ⊢
    <;> try (cases hc; simp [concretizeExpr_natLit, Ctstore])
  case StopArith.EXP =>
    cases hs1 : sym.stackAt 1 with
    | error e => simp [hs1] at hc
    | ok s1 =>
        simp [hs1] at hc
        cases hc
        rw [concretizeExpr_cexp]
        rw [concretizeSym_stackAt_eq hbase hs1]
        simp [concretizeExpr_proof_irrel]
  case Keccak.KECCAK256 =>
    cases hs1 : sym.stackAt 1 with
    | error e => simp [hs1] at hc
    | ok s1 =>
        simp [hs1] at hc
        cases hc
        rw [concretizeExpr_cwordCost]
        rw [concretizeSym_stackAt_eq hbase hs1]
        simp [concretizeExpr_proof_irrel]
  case Env.BALANCE =>
    cases hs0 : sym.stackAt 0 with
    | error e => simp [hs0] at hc
    | ok s0 =>
        simp [hs0] at hc
        cases hc
        rw [concretizeExpr_caccess_state hbase]
        rw [concretizeExpr_addrOfWord]
        rw [concretizeSym_stackAt_eq hbase hs0]
        simp [concretizeExpr_proof_irrel]
  case Env.CALLDATACOPY =>
    cases hs2 : sym.stackAt 2 with
    | error e => simp [hs2] at hc
    | ok s2 =>
        simp [hs2] at hc
        cases hc
        rw [concretizeExpr_cwordCost]
        rw [concretizeSym_stackAt_eq hbase hs2]
        simp [concretizeExpr_proof_irrel]
  case Env.CODECOPY =>
    cases hs2 : sym.stackAt 2 with
    | error e => simp [hs2] at hc
    | ok s2 =>
        simp [hs2] at hc
        cases hc
        rw [concretizeExpr_cwordCost]
        rw [concretizeSym_stackAt_eq hbase hs2]
        simp [concretizeExpr_proof_irrel]
  case Env.EXTCODESIZE =>
    cases hs0 : sym.stackAt 0 with
    | error e => simp [hs0] at hc
    | ok s0 =>
        simp [hs0] at hc
        cases hc
        rw [concretizeExpr_caccess_state hbase]
        rw [concretizeExpr_addrOfWord]
        rw [concretizeSym_stackAt_eq hbase hs0]
        simp [concretizeExpr_proof_irrel]
  case Env.EXTCODECOPY =>
    cases hs0 : sym.stackAt 0 with
    | error e =>
        rw [hs0] at hc
        simp [Except.bind, bind] at hc
    | ok s0 =>
        simp [hs0, Except.bind, bind] at hc
        cases hs3 : sym.stackAt 3 with
        | error e => simp [hs3] at hc
        | ok s3 =>
            simp [hs3] at hc
            cases hc
            rw [concretizeExpr_addNat]
            rw [concretizeExpr_caccess_state hbase]
            rw [concretizeExpr_addrOfWord]
            rw [concretizeExpr_cwordCost]
            rw [concretizeSym_stackAt_eq hbase hs0]
            rw [concretizeSym_stackAt_eq hbase hs3]
            simp [concretizeExpr_proof_irrel]
  case Env.RETURNDATACOPY =>
    cases hs2 : sym.stackAt 2 with
    | error e => simp [hs2] at hc
    | ok s2 =>
        simp [hs2] at hc
        cases hc
        rw [concretizeExpr_cwordCost]
        rw [concretizeSym_stackAt_eq hbase hs2]
        simp [concretizeExpr_proof_irrel]
  case Env.EXTCODEHASH =>
    cases hs0 : sym.stackAt 0 with
    | error e => simp [hs0] at hc
    | ok s0 =>
        simp [hs0] at hc
        cases hc
        rw [concretizeExpr_caccess_state hbase]
        rw [concretizeExpr_addrOfWord]
        rw [concretizeSym_stackAt_eq hbase hs0]
        simp [concretizeExpr_proof_irrel]
  case StackMemFlow.SLOAD =>
    cases hs0 : sym.stackAt 0 with
    | error e => simp [hs0] at hc
    | ok s0 =>
        simp [hs0] at hc
        cases hc
        apply concretizeExpr_csload_state hbase
        exact Eq.trans concretizeExpr_proof_irrel (concretizeSym_stackAt_eq hbase hs0)
  case StackMemFlow.SSTORE =>
    cases hs0 : sym.stackAt 0 with
    | error e => simp [symCsstore, hs0, Except.bind, bind] at hc
    | ok s0 =>
        simp [symCsstore, hs0, Except.bind, bind] at hc
        cases hs1 : sym.stackAt 1 with
        | error e => simp [hs1, Except.bind, bind] at hc
        | ok v' =>
            simp [hs1] at hc
            cases hc
            have hslot := concretizeSym_stackAt_eq hbase hs0
            have hnew := concretizeSym_stackAt_eq hbase hs1
            have hstorageBound :
                (sym.accountStorageExpr Expr.Address).consumeStack ≤
                  concrete.machineState.stack.length :=
              Nat.le_trans
                (accountStorageExpr_consumption sym Expr.Address)
                (concretizeSym_ok_stack_bound hbase)
            have hstorage :=
              accountMapFindSound_current_storage
                (hbase := hbase)
                (hsound := hsound)
                (hcurrent := hcurrent)
                (hstorage := hstorageBound)
            have hstorageConcrete :
                (state.accountMap.find! concrete.executionEnv.codeOwner).storage =
                  concretizeExpr concrete (sym.accountStorageExpr Expr.Address) hstorageBound := by
              simpa [concretizeSym_executionEnv_eq hbase] using hstorage
            have hloadBound :
                (Expr.SLoad s0.1 (sym.accountStorageExpr Expr.Address)).consumeStack ≤
                  concrete.machineState.stack.length := by
              simp [Expr.consumeStack]
              exact ⟨Nat.le_trans s0.2 (concretizeSym_ok_stack_bound hbase), hstorageBound⟩
            have hload :
                concretizeExpr concrete
                  (Expr.SLoad s0.1 (sym.accountStorageExpr Expr.Address)) hloadBound =
                  (state.accountMap.find! concrete.executionEnv.codeOwner).storage.findD
                    (state.machineState.stack[0]?.getD default) (⟨0⟩ : UInt256) := by
              rw [concretizeExpr.eq_def]
              simp [hslot, ← hstorageConcrete, concretizeExpr_proof_irrel]
            rw [concretizeExpr.eq_def]
            simp [Csstore, concretizeSym_substate_eq hbase,
              concretizeSym_executionEnv_eq hbase, concretizeSym_σ₀_eq hbase,
              concretizeSubstate, concretizeExprList_proof_irrel,
              concretizeExpr_proof_irrel, hslot, hnew, hstorage, hstorageConcrete,
              hload]
            rfl
  case StackMemFlow.MCOPY =>
    cases hs2 : sym.stackAt 2 with
    | error e => simp [hs2] at hc
    | ok s2 =>
        simp [hs2] at hc
        cases hc
        rw [concretizeExpr_cwordCost]
        rw [concretizeSym_stackAt_eq hbase hs2]
        simp [concretizeExpr_proof_irrel]
  case Log.LOG0 =>
    cases hs1 : sym.stackAt 1 with
    | error e => simp [symC'.logCost, hs1] at hc
    | ok s1 =>
        simp [symC'.logCost, hs1] at hc
        cases hc
        have hslot := concretizeSym_stackAt_eq hbase hs1
        rw [concretizeExpr_cbyteCost]
        simp [concretizeExpr_proof_irrel, hslot]
  case Log.LOG1 =>
    cases hs1 : sym.stackAt 1 with
    | error e => simp [symC'.logCost, hs1] at hc
    | ok s1 =>
        simp [symC'.logCost, hs1] at hc
        cases hc
        have hslot := concretizeSym_stackAt_eq hbase hs1
        rw [concretizeExpr_cbyteCost]
        simp [concretizeExpr_proof_irrel, hslot]
        ring_nf
  case Log.LOG2 =>
    cases hs1 : sym.stackAt 1 with
    | error e => simp [symC'.logCost, hs1] at hc
    | ok s1 =>
        simp [symC'.logCost, hs1] at hc
        cases hc
        have hslot := concretizeSym_stackAt_eq hbase hs1
        rw [concretizeExpr_cbyteCost]
        simp [concretizeExpr_proof_irrel, hslot]
        ring_nf
  case Log.LOG3 =>
    cases hs1 : sym.stackAt 1 with
    | error e => simp [symC'.logCost, hs1] at hc
    | ok s1 =>
        simp [symC'.logCost, hs1] at hc
        cases hc
        have hslot := concretizeSym_stackAt_eq hbase hs1
        rw [concretizeExpr_cbyteCost]
        simp [concretizeExpr_proof_irrel, hslot]
        ring_nf
  case Log.LOG4 =>
    cases hs1 : sym.stackAt 1 with
    | error e => simp [symC'.logCost, hs1] at hc
    | ok s1 =>
        simp [symC'.logCost, hs1] at hc
        cases hc
        have hslot := concretizeSym_stackAt_eq hbase hs1
        rw [concretizeExpr_cbyteCost]
        simp [concretizeExpr_proof_irrel, hslot]
        ring_nf
  case System.CREATE =>
    cases hs2 : sym.stackAt 2 with
    | error e => simp [hs2] at hc
    | ok s2 =>
        simp [hs2] at hc
        cases hc
        rw [concretizeExpr_cwordCost]
        rw [concretizeSym_stackAt_eq hbase hs2]
        simp [concretizeExpr_proof_irrel, R]
  case System.CALL =>
    cases hs0 : sym.stackAt 0 with
    | error e =>
        simp [symC'.callCost, hs0, Except.bind, bind] at hc
    | ok gas =>
        simp [symC'.callCost, hs0, Except.bind, bind] at hc
        cases hs1 : sym.stackAt 1 with
        | error e =>
            simp [hs1, Except.bind, bind] at hc
        | ok target =>
            simp [hs1, Except.bind, bind] at hc
            cases hs2 : sym.stackAt 2 with
            | error e =>
                simp [hs2, Except.bind, bind] at hc
            | ok value =>
                simp [hs2, Except.bind, bind] at hc
                cases hc
                have htarget := concretizeSym_stackAt_eq hbase hs1
                have hgas := concretizeSym_stackAt_eq hbase hs0
                have hvalue := concretizeSym_stackAt_eq hbase hs2
                have hrecipientDead :
                    (sym.accountDeadExpr (Expr.AddrOfWord target.1)).consumeStack ≤
                      concrete.machineState.stack.length :=
                  Nat.le_trans
                    (accountDeadExpr_consumption sym (Expr.AddrOfWord target.1))
                    (concretizeSym_ok_stack_bound hbase)
                have hdead :
                    (concretizeExpr concrete
                        (sym.accountDeadExpr (Expr.AddrOfWord target.1)) hrecipientDead !=
                      (⟨0⟩ : UInt256)) =
                      State.dead state.accountMap
                        (AccountAddress.ofUInt256 (state.machineState.stack[1]?.getD default)) := by
                  have h :=
                    accountMapFindSound_deadExpr_ne_zero
                      (hbase := hbase)
                      (hsound := hsound)
                      (addr := Expr.AddrOfWord target.1)
                      (haddr := by
                        simpa [Expr.consumeStack] using
                          Nat.le_trans target.2 (concretizeSym_ok_stack_bound hbase))
                      (hdead := hrecipientDead)
                  simpa [concretizeExpr_addrOfWord, concretizeExpr_proof_irrel,
                    htarget] using h
                have hdeadIff :
                    ∀ hdead',
                      (concretizeExpr concrete
                          (sym.accountDeadExpr (Expr.AddrOfWord target.1)) hdead' ≠
                        (⟨0⟩ : UInt256)) ↔
                        State.dead state.accountMap
                          (AccountAddress.ofUInt256 (state.machineState.stack[1]?.getD default)) = true := by
                  intro hdead'
                  simpa [concretizeExpr_proof_irrel] using
                    (UInt256_bne_zero_eq_bool_iff_ne hdead)
                have hdeadProp :
                    ∀ hdead',
                      (¬concretizeExpr concrete
                          (sym.accountDeadExpr (Expr.AddrOfWord target.1)) hdead' =
                        (⟨0⟩ : UInt256)) =
                        (State.dead state.accountMap
                          (AccountAddress.ofUInt256 (state.machineState.stack[1]?.getD default)) = true) := by
                  intro hdead'
                  exact propext (hdeadIff hdead')
                have hdeadBoolAny :
                    ∀ hdead',
                      (concretizeExpr concrete
                          (sym.accountDeadExpr (Expr.AddrOfWord target.1)) hdead' !=
                        (⟨0⟩ : UInt256)) =
                        State.dead state.accountMap
                          (AccountAddress.ofUInt256 (state.machineState.stack[1]?.getD default)) := by
                  intro hdead'
                  simpa [concretizeExpr_proof_irrel] using hdead
                have hdeadBoolTrueAny :
                    ∀ hdead',
                      ((concretizeExpr concrete
                          (sym.accountDeadExpr (Expr.AddrOfWord target.1)) hdead' !=
                        (⟨0⟩ : UInt256)) = true) =
                        (State.dead state.accountMap
                          (AccountAddress.ofUInt256 (state.machineState.stack[1]?.getD default)) = true) := by
                  intro hdead'
                  rw [hdeadBoolAny]
                have hdeadExprAny :
                    ∀ hdead',
                      concretizeExpr concrete
                        (sym.accountDeadExpr (Expr.AddrOfWord target.1)) hdead' =
                        concretizeExpr concrete
                          (sym.accountDeadExpr (Expr.AddrOfWord target.1)) hrecipientDead := by
                  intro hdead'
                  exact concretizeExpr_proof_irrel
                rw [concretizeExpr.eq_def]
                simp [Ccall, Cgascap, Cextra, Caccess, Cxfer, Cnew,
                  concretizeSym_substate_eq hbase, concretizeSubstate,
                  concretizeSym_gasAvailable_eq hbase,
                  concretizeExpr_addrOfWord, concretizeExprList_proof_irrel,
                  concretizeExpr_proof_irrel, htarget, hgas, hvalue, hdead, hdeadBoolAny,
                  hdeadBoolTrueAny, hdeadExprAny]
                cases hstateDead :
                  State.dead state.accountMap
                    (AccountAddress.ofUInt256
                      (state.machineState.stack[1]?.getD default))
                all_goals
                  have hraw := hdead.trans hstateDead
                  erw [hraw]
                  try simp [hstateDead, concretizeExpr_proof_irrel,
                    UInt256_bne_zero_eq_decide_ne]
  case System.CALLCODE =>
    cases hs0 : sym.stackAt 0 with
    | error e =>
        simp [symC'.callCost, hs0, Except.bind, bind] at hc
    | ok gas =>
        simp [symC'.callCost, hs0, Except.bind, bind] at hc
        cases hs1 : sym.stackAt 1 with
        | error e =>
            simp [hs1, Except.bind, bind] at hc
        | ok target =>
            simp [hs1, Except.bind, bind] at hc
            cases hs2 : sym.stackAt 2 with
            | error e =>
                simp [hs2, Except.bind, bind] at hc
            | ok value =>
                simp [hs2] at hc
                cases hc
                have htarget := concretizeSym_stackAt_eq hbase hs1
                have hgas := concretizeSym_stackAt_eq hbase hs0
                have hvalue := concretizeSym_stackAt_eq hbase hs2
                have hrecipientDead :
                    (sym.accountDeadExpr Expr.Address).consumeStack ≤
                      concrete.machineState.stack.length :=
                  Nat.le_trans
                    (accountDeadExpr_consumption sym Expr.Address)
                    (concretizeSym_ok_stack_bound hbase)
                have hdead :
                    (concretizeExpr concrete
                        (sym.accountDeadExpr Expr.Address) hrecipientDead !=
                      (⟨0⟩ : UInt256)) =
                      State.dead state.accountMap concrete.executionEnv.codeOwner := by
                  have h :=
                    accountMapFindSound_deadExpr_ne_zero
                      (hbase := hbase)
                      (hsound := hsound)
                      (addr := Expr.Address)
                      (haddr := by simp [Expr.consumeStack])
                      (hdead := hrecipientDead)
                  simpa [concretizeExpr_address, concretizeExpr_proof_irrel] using h
                have hdeadIff :
                    ∀ hdead',
                      (concretizeExpr concrete
                          (sym.accountDeadExpr Expr.Address) hdead' ≠
                        (⟨0⟩ : UInt256)) ↔
                        State.dead state.accountMap concrete.executionEnv.codeOwner = true := by
                  intro hdead'
                  simpa [concretizeExpr_proof_irrel] using
                    (UInt256_bne_zero_eq_bool_iff_ne hdead)
                have hdeadProp :
                    ∀ hdead',
                      (¬concretizeExpr concrete
                          (sym.accountDeadExpr Expr.Address) hdead' =
                        (⟨0⟩ : UInt256)) =
                        (State.dead state.accountMap concrete.executionEnv.codeOwner = true) := by
                  intro hdead'
                  exact propext (hdeadIff hdead')
                have hdeadBoolAny :
                    ∀ hdead',
                      (concretizeExpr concrete
                          (sym.accountDeadExpr Expr.Address) hdead' !=
                        (⟨0⟩ : UInt256)) =
                        State.dead state.accountMap concrete.executionEnv.codeOwner := by
                  intro hdead'
                  simpa [concretizeExpr_proof_irrel] using hdead
                have hdeadBoolTrueAny :
                    ∀ hdead',
                      ((concretizeExpr concrete
                          (sym.accountDeadExpr Expr.Address) hdead' !=
                        (⟨0⟩ : UInt256)) = true) =
                        (State.dead state.accountMap concrete.executionEnv.codeOwner = true) := by
                  intro hdead'
                  rw [hdeadBoolAny]
                have hdeadExprAny :
                    ∀ hdead',
                      concretizeExpr concrete
                        (sym.accountDeadExpr Expr.Address) hdead' =
                        concretizeExpr concrete
                          (sym.accountDeadExpr Expr.Address) hrecipientDead := by
                  intro hdead'
                  exact concretizeExpr_proof_irrel
                rw [concretizeExpr.eq_def]
                simp [Ccall, Cgascap, Cextra, Caccess, Cxfer, Cnew,
                  concretizeSym_substate_eq hbase, concretizeSubstate,
                  concretizeSym_gasAvailable_eq hbase,
                  concretizeSym_executionEnv_eq hbase,
                  concretizeExpr_addrOfWord, concretizeExprList_proof_irrel,
                  concretizeExpr_proof_irrel, htarget, hgas, hvalue, hdead, hdeadBoolAny,
                  hdeadBoolTrueAny, hdeadExprAny]
                cases hstateDead :
                  State.dead state.accountMap concrete.executionEnv.codeOwner
                all_goals
                  have hraw := hdead.trans hstateDead
                  erw [hraw]
                  try simp [hstateDead, concretizeExpr_proof_irrel,
                    UInt256_bne_zero_eq_decide_ne]
  case System.DELEGATECALL =>
    cases hs0 : sym.stackAt 0 with
    | error e =>
        simp [symC'.callCost, hs0, Except.bind, bind] at hc
    | ok gas =>
        simp [symC'.callCost, hs0, Except.bind, bind] at hc
        cases hs1 : sym.stackAt 1 with
        | error e =>
            simp [hs1, Except.bind, bind] at hc
        | ok target =>
            simp [hs1] at hc
            cases hc
            have htarget := concretizeSym_stackAt_eq hbase hs1
            have hgas := concretizeSym_stackAt_eq hbase hs0
            have hrecipientDead :
                (sym.accountDeadExpr Expr.Address).consumeStack ≤
                  concrete.machineState.stack.length :=
              Nat.le_trans
                (accountDeadExpr_consumption sym Expr.Address)
                (concretizeSym_ok_stack_bound hbase)
            have hdead :
                (concretizeExpr concrete
                    (sym.accountDeadExpr Expr.Address) hrecipientDead !=
                  (⟨0⟩ : UInt256)) =
                  State.dead state.accountMap concrete.executionEnv.codeOwner := by
              have h :=
                accountMapFindSound_deadExpr_ne_zero
                  (hbase := hbase)
                  (hsound := hsound)
                  (addr := Expr.Address)
                  (haddr := by simp [Expr.consumeStack])
                  (hdead := hrecipientDead)
              simpa [concretizeExpr_address, concretizeExpr_proof_irrel] using h
            have hdeadIff :
                ∀ hdead',
                  (concretizeExpr concrete
                      (sym.accountDeadExpr Expr.Address) hdead' ≠
                    (⟨0⟩ : UInt256)) ↔
                    State.dead state.accountMap concrete.executionEnv.codeOwner = true := by
              intro hdead'
              simpa [concretizeExpr_proof_irrel] using
                (UInt256_bne_zero_eq_bool_iff_ne hdead)
            have hdeadProp :
                ∀ hdead',
                  (¬concretizeExpr concrete
                      (sym.accountDeadExpr Expr.Address) hdead' =
                    (⟨0⟩ : UInt256)) =
                    (State.dead state.accountMap concrete.executionEnv.codeOwner = true) := by
              intro hdead'
              exact propext (hdeadIff hdead')
            rw [concretizeExpr.eq_def]
            simp [Ccall, Cgascap, Cextra, Caccess, Cxfer, Cnew,
              concretizeSym_substate_eq hbase, concretizeSubstate,
              concretizeSym_gasAvailable_eq hbase,
              concretizeSym_executionEnv_eq hbase,
              concretizeExpr_addrOfWord, concretizeExprList_proof_irrel,
              concretizeExpr_lit, concretizeExpr_proof_irrel, htarget, hgas, hdead, hdeadIff, hdeadProp,
              UInt256_bne_zero_eq_decide_ne]
  case System.CREATE2 =>
    cases hs2 : sym.stackAt 2 with
    | error e => simp [hs2] at hc
    | ok s2 =>
        simp [hs2] at hc
        cases hc
        have hslot := concretizeSym_stackAt_eq hbase hs2
        rw [concretizeExpr_addNat]
        rw [concretizeExpr_cwordCost]
        rw [concretizeExpr_cwordCost]
        simp [concretizeExpr_proof_irrel, hslot, R]
        ring_nf
  case System.STATICCALL =>
    cases hs0 : sym.stackAt 0 with
    | error e =>
        simp [symC'.callCost, hs0, Except.bind, bind] at hc
    | ok gas =>
        simp [symC'.callCost, hs0, Except.bind, bind] at hc
        cases hs1 : sym.stackAt 1 with
        | error e =>
            simp [hs1, Except.bind, bind] at hc
        | ok target =>
            simp [hs1] at hc
            cases hc
            have htarget := concretizeSym_stackAt_eq hbase hs1
            have hgas := concretizeSym_stackAt_eq hbase hs0
            have hrecipientDead :
                (sym.accountDeadExpr (Expr.AddrOfWord target.1)).consumeStack ≤
                  concrete.machineState.stack.length :=
              Nat.le_trans
                (accountDeadExpr_consumption sym (Expr.AddrOfWord target.1))
                (concretizeSym_ok_stack_bound hbase)
            have hdead :
                (concretizeExpr concrete
                    (sym.accountDeadExpr (Expr.AddrOfWord target.1)) hrecipientDead !=
                  (⟨0⟩ : UInt256)) =
                  State.dead state.accountMap
                    (AccountAddress.ofUInt256 (state.machineState.stack[1]?.getD default)) := by
              have h :=
                accountMapFindSound_deadExpr_ne_zero
                  (hbase := hbase)
                  (hsound := hsound)
                  (addr := Expr.AddrOfWord target.1)
                  (haddr := by
                    simpa [Expr.consumeStack] using
                      Nat.le_trans target.2 (concretizeSym_ok_stack_bound hbase))
                  (hdead := hrecipientDead)
              simpa [concretizeExpr_addrOfWord, concretizeExpr_proof_irrel,
                htarget] using h
            have hdeadIff :
                ∀ hdead',
                  (concretizeExpr concrete
                      (sym.accountDeadExpr (Expr.AddrOfWord target.1)) hdead' ≠
                    (⟨0⟩ : UInt256)) ↔
                    State.dead state.accountMap
                      (AccountAddress.ofUInt256 (state.machineState.stack[1]?.getD default)) = true := by
              intro hdead'
              simpa [concretizeExpr_proof_irrel] using
                (UInt256_bne_zero_eq_bool_iff_ne hdead)
            have hdeadProp :
                ∀ hdead',
                  (¬concretizeExpr concrete
                      (sym.accountDeadExpr (Expr.AddrOfWord target.1)) hdead' =
                    (⟨0⟩ : UInt256)) =
                    (State.dead state.accountMap
                      (AccountAddress.ofUInt256 (state.machineState.stack[1]?.getD default)) = true) := by
              intro hdead'
              exact propext (hdeadIff hdead')
            rw [concretizeExpr.eq_def]
            simp [Ccall, Cgascap, Cextra, Caccess, Cxfer, Cnew,
              concretizeSym_substate_eq hbase, concretizeSubstate,
              concretizeSym_gasAvailable_eq hbase,
              concretizeExpr_addrOfWord, concretizeExprList_proof_irrel,
              concretizeExpr_lit, concretizeExpr_proof_irrel, htarget, hgas, hdead, hdeadIff, hdeadProp,
              UInt256_bne_zero_eq_decide_ne]
  case System.SELFDESTRUCT =>
    cases hs0 : sym.stackAt 0 with
    | error e => simp [hs0] at hc
    | ok s0 =>
        simp [hs0] at hc
        cases hc
        have hrecipientDead :
            (sym.accountDeadExpr (Expr.AddrOfWord s0.1)).consumeStack ≤
              concrete.machineState.stack.length :=
          Nat.le_trans
            (accountDeadExpr_consumption sym (Expr.AddrOfWord s0.1))
            (concretizeSym_ok_stack_bound hbase)
        have hcurrentBalance :
            (sym.accountBalanceExpr Expr.Address).consumeStack ≤
              concrete.machineState.stack.length :=
          Nat.le_trans
            (accountBalanceExpr_consumption sym Expr.Address)
            (concretizeSym_ok_stack_bound hbase)
        have hdead :
            (concretizeExpr concrete
                (sym.accountDeadExpr (Expr.AddrOfWord s0.1)) hrecipientDead !=
              (⟨0⟩ : UInt256)) =
              State.dead state.accountMap
                (AccountAddress.ofUInt256 (state.machineState.stack[0]?.getD default)) := by
          have h :=
            accountMapFindSound_deadExpr_ne_zero
              (hbase := hbase)
              (hsound := hsound)
              (addr := Expr.AddrOfWord s0.1)
              (haddr := by
                simpa [Expr.consumeStack] using
                  Nat.le_trans s0.2 (concretizeSym_ok_stack_bound hbase))
              (hdead := hrecipientDead)
          simpa [concretizeExpr_addrOfWord, concretizeExpr_proof_irrel,
            concretizeSym_stackAt_eq hbase hs0] using h
        have hdeadIff :
            ∀ hdead',
              (concretizeExpr concrete
                  (sym.accountDeadExpr (Expr.AddrOfWord s0.1)) hdead' ≠
                (⟨0⟩ : UInt256)) ↔
                State.dead state.accountMap
                  (AccountAddress.ofUInt256 (state.machineState.stack[0]?.getD default)) = true := by
          intro hdead'
          simpa [concretizeExpr_proof_irrel] using
            (UInt256_bne_zero_eq_bool_iff_ne hdead)
        have hdeadProp :
            ∀ hdead',
              (¬concretizeExpr concrete
                  (sym.accountDeadExpr (Expr.AddrOfWord s0.1)) hdead' =
                (⟨0⟩ : UInt256)) =
                (State.dead state.accountMap
                  (AccountAddress.ofUInt256 (state.machineState.stack[0]?.getD default)) = true) := by
          intro hdead'
          exact propext (hdeadIff hdead')
        have hdeadExprAny :
            ∀ hdead',
              concretizeExpr concrete
                (sym.accountDeadExpr (Expr.AddrOfWord s0.1)) hdead' =
                concretizeExpr concrete
                  (sym.accountDeadExpr (Expr.AddrOfWord s0.1)) hrecipientDead := by
          intro hdead'
          exact concretizeExpr_proof_irrel
        have hdeadBoolAny :
            ∀ hdead',
              (concretizeExpr concrete
                  (sym.accountDeadExpr (Expr.AddrOfWord s0.1)) hdead' !=
                (⟨0⟩ : UInt256)) =
                State.dead state.accountMap
                  (AccountAddress.ofUInt256 (state.machineState.stack[0]?.getD default)) := by
          intro hdead'
          simpa [concretizeExpr_proof_irrel] using hdead
        have hbalance :
            concretizeExpr concrete (sym.accountBalanceExpr Expr.Address) hcurrentBalance =
              Option.option (⟨0⟩ : UInt256) (fun x => x.balance)
                (state.accountMap.find? concrete.executionEnv.codeOwner) := by
          have h :=
            accountMapFindSound_balanceExpr
              (hbase := hbase)
              (hsound := hsound)
              (addr := Expr.Address)
              (haddr := by simp [Expr.consumeStack])
              (hbalance := hcurrentBalance)
          simpa [concretizeExpr_address, concretizeExpr_proof_irrel] using h
        rw [concretizeExpr.eq_def]
        simp [Cselfdestruct, concretizeSym_substate_eq hbase,
          concretizeSym_executionEnv_eq hbase, concretizeSubstate,
          concretizeExpr_addrOfWord, concretizeExprList_proof_irrel,
          concretizeExpr_proof_irrel, concretizeSym_stackAt_eq hbase hs0,
          hdead, hdeadIff, hdeadProp, hdeadExprAny, hdeadBoolAny, hbalance]
        cases hstateDead :
          State.dead state.accountMap
            (AccountAddress.ofUInt256
              (state.machineState.stack[0]?.getD default))
        all_goals
          have hraw := hdead.trans hstateDead
          erw [hraw]
          try simp [hstateDead, concretizeExpr_proof_irrel,
            UInt256_bne_zero_eq_decide_ne]

theorem sumZ_Z_consistent {state : Ethereum.State} {zres : Except ExecutionException (Ethereum.State × Nat)}
  {concrete : Ethereum.State} {symstate symstate' : SymState} {o : Option (Bool × ByteArray)}
  {w : Operation} {cost₂ : Expr .num} :
  let bytecode := state.executionEnv.code
  let validJumps := D_J bytecode { val := 0 }
  Z validJumps w state = zres →

  concretizeSym concrete validJumps symstate = .ok (state, o) →
  AccountMapFindSound concrete symstate.evm.accountMap →
  CurrentAccountFound symstate.evm.accountMap →
  symZ w symstate = .ok (cost₂, symstate') →
  match zres with
  | .error e => concretizeSym concrete validJumps symstate' = .error e
  | .ok (state,_) => concretizeSym concrete validJumps symstate' = .ok (state,o)
  := by
    dsimp only
    intro hZ hconcrete haccountSound hcurrentAccount hsymZ
    by_cases hδ : δ w = none
    · simp [symZ, hδ, Except.bind, bind] at hsymZ
    · by_cases hUnder : List.length state.machineState.stack < (δ w).getD 0
      · have hknown :
            symstate.knownStack.length < (δ w).getD 0 :=
          knownStack_lt_of_state_stack_underflow hconcrete hUnder
        have hfirst :
            concretizeSym concrete (D_J state.executionEnv.code { val := 0 })
              (addCondition symstate
                (.stackGE (symstate.asp + ((δ w).getD 0 - symstate.knownStack.length)))
                (by simp)) =
              .error .StackUnderflow :=
          concretizeSym_stackGE_underflow_error hconcrete hknown hUnder
        have hzres : zres = .error .StackUnderflow := by
          simp [Z, hδ, hUnder] at hZ
          exact hZ.symm
        subst zres
        have hcore :
            symZCore w
              (addCondition symstate
                (.stackGE (symstate.asp + ((δ w).getD 0 - symstate.knownStack.length)))
                (by simp)) =
              .ok (cost₂, symstate') := by
          simpa [symZ, symZApplyStackUnderflowCondition, hδ, hknown, Except.bind, bind, pure]
            using hsymZ
        simpa [Z, hδ, hUnder] using symZCore_preserve_concretize_error hfirst hcore
      · let sym0 := symZApplyStackUnderflowCondition w symstate
        have hstackOk :
            concretizeSym concrete (D_J state.executionEnv.code { val := 0 }) sym0 =
              .ok (state, o) := by
          dsimp [sym0]
          exact concretizeSym_stackUnderflowCondition_no_underflow_ok hconcrete hUnder
        have hcore :
            symZCore w sym0 = .ok (cost₂, symstate') := by
          simpa [sym0, symZ, hδ, Except.bind, bind, pure] using hsymZ
        obtain ⟨cost₁?, hmemOk⟩ := symZCore_memoryExpansionCost_ok hcore
        by_cases hMemGas :
            state.machineState.gasAvailable.toNat < memoryExpansionCost state w
        · have hzres : zres = .error .OutOfGass := by
            simp [Z, hδ, hUnder, hMemGas] at hZ
            exact hZ.symm
          subst zres
          cases cost₁? with
          | none =>
              have hzero : memoryExpansionCost state w = 0 :=
                memoryExpansionCost_zero_of_symMemoryExpansionCost_none hmemOk
              rw [hzero] at hMemGas
              omega
          | some cost₁ =>
              have hcost :
                  concretizeExpr concrete cost₁.1
                    (Nat.le_trans cost₁.2 (concretizeSym_ok_stack_bound hstackOk)) =
                    memoryExpansionCost state w :=
                symMemoryExpansionCost_some_concretize hstackOk hmemOk
              have hmemErr :
                  concretizeSym concrete (D_J state.executionEnv.code { val := 0 })
                    (symZApplyMemoryExpansionAndCharge sym0 (some cost₁)) =
                    .error .OutOfGass :=
                symZApplyMemoryExpansionAndCharge_mem_oog hstackOk hcost hMemGas
              simpa [Z, hδ, hUnder, hMemGas] using
                symZCore_after_memory_preserve_error hmemOk hmemErr hcore
        · let state₁ : Ethereum.State :=
            { state with machineState := { state.machineState with
              gasAvailable := state.machineState.gasAvailable - UInt256.ofNat (memoryExpansionCost state w) } }
          have hmemCharge :
              concretizeSym concrete (D_J state.executionEnv.code { val := 0 })
                (symZApplyMemoryExpansionAndCharge sym0 cost₁?) =
                .ok (state₁, o) := by
            dsimp [state₁]
            exact symZApplyMemoryExpansionAndCharge_ok hstackOk hmemOk hMemGas
          have hcoreOrig := hcore
          unfold symZCore at hcore
          simp [hmemOk, Except.bind, bind] at hcore
          cases hc2 : symC' (symZApplyMemoryExpansionAndCharge sym0 cost₁?) w with
          | error e =>
              simp [hc2, Except.bind, bind] at hcore
          | ok cost₂' =>
              simp [hc2, Except.bind, bind] at hcore
              have haccountSoundCharge :
                  AccountMapFindSound concrete
                    (symZApplyMemoryExpansionAndCharge sym0 cost₁?).evm.accountMap := by
                have hsym0 :
                    sym0.evm.accountMap = symstate.evm.accountMap := by
                  simp [sym0, symZApplyStackUnderflowCondition, addCondition]
                  split <;> rfl
                cases cost₁? with
                | none =>
                    simpa [symZApplyMemoryExpansionAndCharge,
                      symZApplyMemoryExpansionCondition, update_gas, hsym0]
                      using haccountSound
                | some cost₁ =>
                    simpa [symZApplyMemoryExpansionAndCharge,
                      symZApplyMemoryExpansionCondition, update_gas,
                      addCondition, hsym0] using haccountSound
              have hcurrentCharge :
                  CurrentAccountFound
                    (symZApplyMemoryExpansionAndCharge sym0 cost₁?).evm.accountMap := by
                have hsym0 :
                    sym0.evm.accountMap = symstate.evm.accountMap := by
                  simp [sym0, symZApplyStackUnderflowCondition, addCondition]
                  split <;> rfl
                cases cost₁? with
                | none =>
                    simpa [symZApplyMemoryExpansionAndCharge,
                      symZApplyMemoryExpansionCondition, update_gas, hsym0]
                      using hcurrentAccount
                | some cost₁ =>
                    simpa [symZApplyMemoryExpansionAndCharge,
                      symZApplyMemoryExpansionCondition, update_gas,
                      addCondition, hsym0] using hcurrentAccount
              have hcostEq :
                  concretizeExpr concrete cost₂'.1
                    (Nat.le_trans cost₂'.2 (concretizeSym_ok_stack_bound hmemCharge)) =
                    C' state₁ w :=
                symC'_concretize hmemCharge haccountSoundCharge hcurrentCharge hc2
              by_cases hCostGas :
                  state₁.machineState.gasAvailable.toNat < C' state₁ w
              · have hcostErr :
                    concretizeSym concrete (D_J state.executionEnv.code { val := 0 })
                      (symZApplyCostCondition
                        (symZApplyMemoryExpansionAndCharge sym0 cost₁?) cost₂') =
                      .error .OutOfGass :=
                  symZApplyCostCondition_oog hmemCharge hcostEq hCostGas
                have hzres : zres = .error .OutOfGass := by
                  simp [Z, hδ, hUnder, hMemGas, state₁, hCostGas] at hZ
                  exact hZ.symm
                rw [hzres]
                exact symZCore_after_cost_preserve_error hmemOk hc2 hcostErr hcoreOrig
              · have hcostOk :
                    concretizeSym concrete (D_J state.executionEnv.code { val := 0 })
                      (symZApplyCostCondition
                        (symZApplyMemoryExpansionAndCharge sym0 cost₁?) cost₂') =
                      .ok (state₁, o) :=
                  symZApplyCostCondition_ok hmemCharge hcostEq hCostGas
                cases hjump :
                    symZApplyJumpCondition w
                      (symZApplyCostCondition
                        (symZApplyMemoryExpansionAndCharge sym0 cost₁?) cost₂') with
                | error e =>
                    simp [hjump, Except.bind, bind] at hcore
                | ok sym3 =>
                    simp [hjump, Except.bind, bind] at hcore
                    by_cases hBadJump :
                        w = .JUMP ∧
                          notIn state₁.machineState.stack[0]?
                            (D_J state.executionEnv.code { val := 0 }) = true
                    · rcases hBadJump with ⟨hwjump, hInvalid⟩
                      subst w
                      have hlen0 : 0 < state₁.machineState.stack.length := by
                        have hlenState : 1 ≤ state.machineState.stack.length := by
                          simpa [δ] using (Nat.le_of_not_lt hUnder)
                        dsimp [state₁]
                        omega
                      have hsome :
                          state₁.machineState.stack[0]? =
                            some state₁.machineState.stack[0]! := by
                        rw [List.getElem?_eq_getElem hlen0]
                        rw [getElem!_pos state₁.machineState.stack 0 hlen0]
                      have hbad :
                          notIn (.some state₁.machineState.stack[0]!)
                            (D_J state.executionEnv.code { val := 0 }) = true := by
                        rw [hsome] at hInvalid
                        exact hInvalid
                      have hJumpErr :
                          concretizeSym concrete (D_J state.executionEnv.code { val := 0 }) sym3 =
                            .error .BadJumpDestination :=
                        symZApplyJumpCondition_jump_error hcostOk hjump hbad
                      have hzres : zres = .error .BadJumpDestination := by
                        have hCostGasJump :
                            ¬ state₁.machineState.gasAvailable.toNat < GasConstants.Gmid := by
                          simpa [C', Ethereum.EVM.InstructionGasGroups.Wcopy,
                            Ethereum.EVM.InstructionGasGroups.Wextaccount,
                            Ethereum.EVM.InstructionGasGroups.Wzero,
                            Ethereum.EVM.InstructionGasGroups.Wbase,
                            Ethereum.EVM.InstructionGasGroups.Wverylow,
                            Ethereum.EVM.InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
                            Ethereum.EVM.InstructionGasGroups.Wverylow.dupInstrs,
                            Ethereum.EVM.InstructionGasGroups.Wverylow.swapInstrs,
                            Ethereum.EVM.InstructionGasGroups.Wlow,
                            Ethereum.EVM.InstructionGasGroups.Wmid,
                            Ethereum.EVM.InstructionGasGroups.Whigh] using hCostGas
                        have hCostGasZ :
                            ¬ (state.machineState.gasAvailable -
                                  UInt256.ofNat (memoryExpansionCost state .JUMP)).toNat <
                                GasConstants.Gmid := by
                          simpa [state₁] using hCostGasJump
                        have hInvalidZ :
                            Z.notIn state.machineState.stack[0]?
                              (D_J state.executionEnv.code { val := 0 }) = true := by
                          simpa [Z.notIn, Z.belongs, notIn, belongs, state₁] using hInvalid
                        simp [Z, hδ, hUnder, hMemGas, hCostGasZ, hInvalidZ] at hZ
                        exact hZ.symm
                      rw [hzres]
                      exact symZCore_after_jump_preserve_error hmemOk hc2 hjump hJumpErr hcoreOrig
                    · have hnotBadSome :
                          ¬ (w = .JUMP ∧
                            notIn (.some state₁.machineState.stack[0]!)
                              (D_J state.executionEnv.code { val := 0 }) = true) := by
                        intro hbadSome
                        rcases hbadSome with ⟨hwjump, hbadSome⟩
                        apply hBadJump
                        refine ⟨hwjump, ?_⟩
                        subst w
                        have hlen0 : 0 < state₁.machineState.stack.length := by
                          have hlenState : 1 ≤ state.machineState.stack.length := by
                            simpa [δ] using (Nat.le_of_not_lt hUnder)
                          dsimp [state₁]
                          omega
                        have hsome :
                            state₁.machineState.stack[0]? =
                              some state₁.machineState.stack[0]! := by
                          rw [List.getElem?_eq_getElem hlen0]
                          rw [getElem!_pos state₁.machineState.stack 0 hlen0]
                        rw [hsome]
                        exact hbadSome
                      have h3Ok :
                          concretizeSym concrete (D_J state.executionEnv.code { val := 0 }) sym3 =
                            .ok (state₁, o) :=
                        symZApplyJumpCondition_ok hcostOk hjump hnotBadSome
                      cases hjumpi : symZApplyJumpiCondition w sym3 with
                      | error e =>
                          simp [hjumpi, Except.bind, bind] at hcore
                      | ok sym4 =>
                          simp [hjumpi, Except.bind, bind] at hcore
                          by_cases hBadJumpi :
                              w = .JUMPI ∧
                                state₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
                                notIn state₁.machineState.stack[0]?
                                  (D_J state.executionEnv.code { val := 0 }) = true
                          · rcases hBadJumpi with ⟨hwjumpi, hJcNe, hInvalid⟩
                            subst w
                            have hlen2 : 2 ≤ state₁.machineState.stack.length := by
                              have hlenState : 2 ≤ state.machineState.stack.length := by
                                simpa [δ] using (Nat.le_of_not_lt hUnder)
                              dsimp [state₁]
                              omega
                            have hlen0 : 0 < state₁.machineState.stack.length := by
                              omega
                            have hlen1 : 1 < state₁.machineState.stack.length := by
                              omega
                            have hsome0 :
                                state₁.machineState.stack[0]? =
                                  some state₁.machineState.stack[0]! := by
                              rw [List.getElem?_eq_getElem hlen0]
                              rw [getElem!_pos state₁.machineState.stack 0 hlen0]
                            have hsome1 :
                                state₁.machineState.stack[1]? =
                                  some state₁.machineState.stack[1]! := by
                              rw [List.getElem?_eq_getElem hlen1]
                              rw [getElem!_pos state₁.machineState.stack 1 hlen1]
                            have hbad :
                                notIn (.some state₁.machineState.stack[0]!)
                                  (D_J state.executionEnv.code { val := 0 }) = true := by
                              rw [hsome0] at hInvalid
                              exact hInvalid
                            have hneWord :
                                state₁.machineState.stack[1]! ≠ (⟨0⟩ : UInt256) := by
                              intro hz
                              rw [hsome1, hz] at hJcNe
                              exact hJcNe rfl
                            have hjcnz :
                                (state₁.machineState.stack[1]! == (⟨0⟩ : UInt256)) = false :=
                              UInt256_beq_zero_false_of_ne state₁.machineState.stack[1]! hneWord
                            have hJumpiErr :
                                concretizeSym concrete (D_J state.executionEnv.code { val := 0 }) sym4 =
                                  .error .BadJumpDestination :=
                              symZApplyJumpiCondition_jumpi_error h3Ok hjumpi hjcnz hbad
                            have hzres : zres = .error .BadJumpDestination := by
                              have hCostGasJumpi :
                                  ¬ state₁.machineState.gasAvailable.toNat < GasConstants.Ghigh := by
                                simpa [C', Ethereum.EVM.InstructionGasGroups.Wcopy,
                                  Ethereum.EVM.InstructionGasGroups.Wextaccount,
                                  Ethereum.EVM.InstructionGasGroups.Wzero,
                                  Ethereum.EVM.InstructionGasGroups.Wbase,
                                  Ethereum.EVM.InstructionGasGroups.Wverylow,
                                  Ethereum.EVM.InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
                                  Ethereum.EVM.InstructionGasGroups.Wverylow.dupInstrs,
                                  Ethereum.EVM.InstructionGasGroups.Wverylow.swapInstrs,
                                  Ethereum.EVM.InstructionGasGroups.Wlow,
                                  Ethereum.EVM.InstructionGasGroups.Wmid,
                                  Ethereum.EVM.InstructionGasGroups.Whigh] using hCostGas
                              have hCostGasZ :
                                  ¬ (state.machineState.gasAvailable -
                                        UInt256.ofNat (memoryExpansionCost state .JUMPI)).toNat <
                                      GasConstants.Ghigh := by
                                simpa [state₁] using hCostGasJumpi
                              have hJcNeZ :
                                  state.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) := by
                                simpa [state₁] using hJcNe
                              have hInvalidZ :
                                  Z.notIn state.machineState.stack[0]?
                                    (D_J state.executionEnv.code { val := 0 }) = true := by
                                simpa [Z.notIn, Z.belongs, notIn, belongs, state₁] using hInvalid
                              simp [Z, hδ, hUnder, hMemGas, hCostGasZ, hJcNeZ,
                                hInvalidZ] at hZ
                              exact hZ.symm
                            rw [hzres]
                            exact symZCore_after_jumpi_preserve_error hmemOk hc2 hjump hjumpi
                              hJumpiErr hcoreOrig
                          · have hJumpiOkCond :
                                w = .JUMPI →
                                  ((state₁.machineState.stack[1]! == (⟨0⟩ : UInt256)) = true ∨
                                    notIn (.some state₁.machineState.stack[0]!)
                                      (D_J state.executionEnv.code { val := 0 }) = false) := by
                              intro hwjumpi
                              by_cases hjcz :
                                  (state₁.machineState.stack[1]! == (⟨0⟩ : UInt256)) = true
                              · exact Or.inl hjcz
                              · right
                                apply Bool.eq_false_of_not_eq_true
                                intro hdestBad
                                apply hBadJumpi
                                refine ⟨hwjumpi, ?_, ?_⟩
                                · have hlenState : 2 ≤ state.machineState.stack.length := by
                                    have hUnderJ :
                                        ¬ state.machineState.stack.length < (δ Operation.JUMPI).getD 0 := by
                                      simpa [hwjumpi] using hUnder
                                    simpa [δ] using (Nat.le_of_not_lt hUnderJ)
                                  have hlen1 : 1 < state₁.machineState.stack.length := by
                                    dsimp [state₁]
                                    omega
                                  have hsome1 :
                                      state₁.machineState.stack[1]? =
                                        some state₁.machineState.stack[1]! := by
                                    rw [List.getElem?_eq_getElem hlen1]
                                    rw [getElem!_pos state₁.machineState.stack 1 hlen1]
                                  have hjczFalse :
                                      (state₁.machineState.stack[1]! == (⟨0⟩ : UInt256)) = false :=
                                    Bool.eq_false_of_not_eq_true hjcz
                                  have hneWord :
                                      state₁.machineState.stack[1]! ≠ (⟨0⟩ : UInt256) :=
                                    UInt256_ne_zero_of_beq_false state₁.machineState.stack[1]! hjczFalse
                                  intro hopt
                                  rw [hsome1] at hopt
                                  exact hneWord (Option.some.inj hopt)
                                · have hlenState : 2 ≤ state.machineState.stack.length := by
                                    have hUnderJ :
                                        ¬ state.machineState.stack.length < (δ Operation.JUMPI).getD 0 := by
                                      simpa [hwjumpi] using hUnder
                                    simpa [δ] using (Nat.le_of_not_lt hUnderJ)
                                  have hlen0 : 0 < state₁.machineState.stack.length := by
                                    dsimp [state₁]
                                    omega
                                  have hsome0 :
                                      state₁.machineState.stack[0]? =
                                        some state₁.machineState.stack[0]! := by
                                    rw [List.getElem?_eq_getElem hlen0]
                                    rw [getElem!_pos state₁.machineState.stack 0 hlen0]
                                  rw [hsome0]
                                  exact hdestBad
                            have h4Ok :
                                concretizeSym concrete (D_J state.executionEnv.code { val := 0 }) sym4 =
                                  .ok (state₁, o) :=
                              symZApplyJumpiCondition_ok h3Ok hjumpi hJumpiOkCond
                            cases hret : symZApplyReturnDataCopyCondition w sym4 with
                            | error e =>
                                simp [hret, Except.bind, bind] at hcore
                            | ok sym5 =>
                                simp [hret, Except.bind, bind] at hcore
                                by_cases hBadReturnData :
                                    w = .RETURNDATACOPY ∧
                                      (state₁.machineState.stack.getD 1 ⟨0⟩).toNat +
                                          (state₁.machineState.stack.getD 2 ⟨0⟩).toNat >
                                        state₁.machineState.returnData.size
                                · rcases hBadReturnData with ⟨hwret, hInvalidAccess⟩
                                  subst w
                                  have hRetErr :
                                      concretizeSym concrete
                                        (D_J state.executionEnv.code { val := 0 }) sym5 =
                                        .error .InvalidMemoryAccess :=
                                    symZApplyReturnDataCopyCondition_error h4Ok hret (by omega)
                                  have hzres : zres = .error .InvalidMemoryAccess := by
                                    have hCostGasZ :
                                        ¬ (state.machineState.gasAvailable -
                                              UInt256.ofNat
                                                (memoryExpansionCost state .RETURNDATACOPY)).toNat <
                                            C' state₁ .RETURNDATACOPY := by
                                      simpa [state₁] using hCostGas
                                    have hInvalidAccessZ :
                                        (state.machineState.stack.getD 1 ⟨0⟩).toNat +
                                            (state.machineState.stack.getD 2 ⟨0⟩).toNat >
                                          state.machineState.returnData.size := by
                                      simpa [state₁] using hInvalidAccess
                                    have hInvalidAccessZ' :
                                        state.machineState.returnData.size <
                                          (state.machineState.stack[1]?.getD (⟨0⟩ : UInt256)).toNat +
                                            (state.machineState.stack[2]?.getD (⟨0⟩ : UInt256)).toNat := by
                                      simpa [List.getD_eq_getElem?_getD] using
                                        (show state.machineState.returnData.size <
                                          (state.machineState.stack.getD 1 ⟨0⟩).toNat +
                                            (state.machineState.stack.getD 2 ⟨0⟩).toNat from by
                                          omega)
                                    simp [Z, hδ, hUnder, hMemGas, hCostGasZ,
                                      hInvalidAccessZ', state₁] at hZ
                                    exact hZ.symm
                                  rw [hzres]
                                  exact symZCore_after_returnDataCopy_preserve_error
                                    hmemOk hc2 hjump hjumpi hret hRetErr hcoreOrig
                                · have hReturnDataOkCond :
                                      w = .RETURNDATACOPY →
                                        (state₁.machineState.stack.getD 1 ⟨0⟩).toNat +
                                            (state₁.machineState.stack.getD 2 ⟨0⟩).toNat ≤
                                          state₁.machineState.returnData.size := by
                                    intro hwret
                                    apply Nat.le_of_not_gt
                                    intro hgt
                                    exact hBadReturnData ⟨hwret, hgt⟩
                                  have h5Ok :
                                      concretizeSym concrete
                                        (D_J state.executionEnv.code { val := 0 }) sym5 =
                                        .ok (state₁, o) :=
                                    symZApplyReturnDataCopyCondition_ok h4Ok hret hReturnDataOkCond
                                  let sym6 := symZApplyStackOverflowCondition w sym5
                                  by_cases hBadOverflow :
                                      1024 <
                                        state₁.machineState.stack.length - (δ w).getD 0 +
                                          (α w).getD 0
                                  · have hδleState₁ :
                                        (δ w).getD 0 ≤ state₁.machineState.stack.length := by
                                      dsimp [state₁]
                                      exact Nat.le_of_not_lt hUnder
                                    have hStackErr :
                                        concretizeSym concrete
                                          (D_J state.executionEnv.code { val := 0 }) sym6 =
                                          .error .StackOverflow := by
                                      dsimp [sym6]
                                      exact symZApplyStackOverflowCondition_error
                                        h5Ok hδleState₁ hBadOverflow
                                    have hzres : zres = .error .StackOverflow := by
                                      have hCostGasZ :
                                          ¬ (state.machineState.gasAvailable -
                                                UInt256.ofNat (memoryExpansionCost state w)).toNat <
                                              C' state₁ w := by
                                        simpa [state₁] using hCostGas
                                      have hNoBadJumpZ :
                                          ¬ (w = .JUMP ∧
                                            Z.notIn state.machineState.stack[0]?
                                              (D_J state.executionEnv.code { val := 0 }) = true) := by
                                        intro hbad
                                        apply hBadJump
                                        simpa [Z.notIn, Z.belongs, notIn, belongs, state₁] using hbad
                                      have hNoBadJumpiZ :
                                          ¬ (w = .JUMPI ∧
                                            state.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
                                            Z.notIn state.machineState.stack[0]?
                                              (D_J state.executionEnv.code { val := 0 }) = true) := by
                                        intro hbad
                                        apply hBadJumpi
                                        simpa [Z.notIn, Z.belongs, notIn, belongs, state₁] using hbad
                                      have hNoBadReturnZ :
                                          ¬ (w = .RETURNDATACOPY ∧
                                            state.machineState.returnData.size <
                                              (state.machineState.stack[1]?.getD (⟨0⟩ : UInt256)).toNat +
                                                (state.machineState.stack[2]?.getD (⟨0⟩ : UInt256)).toNat) := by
                                        intro hbad
                                        rcases hbad with ⟨hwret, hretBad⟩
                                        apply hBadReturnData
                                        refine ⟨hwret, ?_⟩
                                        simpa [List.getD_eq_getElem?_getD, state₁] using hretBad
                                      have hOverflowZ :
                                          1024 <
                                            state.machineState.stack.length - (δ w).getD 0 +
                                              (α w).getD 0 := by
                                        simpa [state₁] using hBadOverflow
                                      simp [Z, hδ, hUnder, hMemGas, hCostGasZ,
                                        hNoBadJumpZ, hNoBadJumpiZ, hNoBadReturnZ,
                                        hOverflowZ, state₁] at hZ
                                      exact hZ.symm
                                    rw [hzres]
                                    exact symZCore_after_stackOverflow_preserve_error
                                      hmemOk hc2 hjump hjumpi hret hStackErr hcoreOrig
                                  · have hδleState₁ :
                                        (δ w).getD 0 ≤ state₁.machineState.stack.length := by
                                      dsimp [state₁]
                                      exact Nat.le_of_not_lt hUnder
                                    have h6Ok :
                                        concretizeSym concrete
                                          (D_J state.executionEnv.code { val := 0 }) sym6 =
                                          .ok (state₁, o) := by
                                      dsimp [sym6]
                                      exact symZApplyStackOverflowCondition_ok
                                        h5Ok hδleState₁ hBadOverflow
                                    cases hstatic : symZApplyStaticModeCondition w sym6 with
                                    | error e =>
                                        simp [sym6, hstatic, Except.bind, bind] at hcore
                                    | ok sym7 =>
                                        simp [sym6, hstatic, Except.bind, bind] at hcore
                                        by_cases hBadStatic :
                                            (¬ state₁.executionEnv.perm) ∧
                                              (w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT,
                                                  .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
                                                (w = .CALL ∧
                                                  state₁.machineState.stack[2]? ≠ some (⟨0⟩ : UInt256)))
                                        · rcases hBadStatic with ⟨hperm, hviolConcrete⟩
                                          have hviolSym :
                                              w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT,
                                                  .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
                                                (w = .CALL ∧
                                                  (state₁.machineState.stack[2]! == (⟨0⟩ : UInt256)) = false) := by
                                            rcases hviolConcrete with hstaticOp | hcallValue
                                            · exact Or.inl hstaticOp
                                            · rcases hcallValue with ⟨hwcall, hvalueOptNe⟩
                                              right
                                              refine ⟨hwcall, ?_⟩
                                              have hlenCall : 3 ≤ state₁.machineState.stack.length := by
                                                have hUnderCall :
                                                    ¬ state.machineState.stack.length <
                                                      (δ Operation.CALL).getD 0 := by
                                                  simpa [hwcall] using hUnder
                                                have hlen7 : 7 ≤ state.machineState.stack.length := by
                                                  simpa [δ] using Nat.le_of_not_lt hUnderCall
                                                dsimp [state₁]
                                                omega
                                              have hlen2 : 2 < state₁.machineState.stack.length := by
                                                omega
                                              have hsome2 :
                                                  state₁.machineState.stack[2]? =
                                                    some state₁.machineState.stack[2]! := by
                                                rw [List.getElem?_eq_getElem hlen2]
                                                rw [getElem!_pos state₁.machineState.stack 2 hlen2]
                                              have hneWord :
                                                  state₁.machineState.stack[2]! ≠ (⟨0⟩ : UInt256) := by
                                                intro hz
                                                rw [hsome2, hz] at hvalueOptNe
                                                exact hvalueOptNe rfl
                                              exact UInt256_beq_zero_false_of_ne
                                                state₁.machineState.stack[2]! hneWord
                                          have hStaticErr :
                                              concretizeSym concrete
                                                (D_J state.executionEnv.code { val := 0 }) sym7 =
                                                .error .StaticModeViolation :=
                                            symZApplyStaticModeCondition_error h6Ok hstatic hperm hviolSym
                                          have hzres : zres = .error .StaticModeViolation := by
                                            have hCostGasZ :
                                                ¬ (state.machineState.gasAvailable -
                                                      UInt256.ofNat (memoryExpansionCost state w)).toNat <
                                                    C' state₁ w := by
                                              simpa [state₁] using hCostGas
                                            have hNoBadJumpZ :
                                                ¬ (w = .JUMP ∧
                                                  Z.notIn state.machineState.stack[0]?
                                                    (D_J state.executionEnv.code { val := 0 }) = true) := by
                                              intro hbad
                                              apply hBadJump
                                              simpa [Z.notIn, Z.belongs, notIn, belongs, state₁] using hbad
                                            have hNoBadJumpiZ :
                                                ¬ (w = .JUMPI ∧
                                                  state.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
                                                  Z.notIn state.machineState.stack[0]?
                                                    (D_J state.executionEnv.code { val := 0 }) = true) := by
                                              intro hbad
                                              apply hBadJumpi
                                              simpa [Z.notIn, Z.belongs, notIn, belongs, state₁] using hbad
                                            have hNoBadReturnZ :
                                                ¬ (w = .RETURNDATACOPY ∧
                                                  state.machineState.returnData.size <
                                                    (state.machineState.stack[1]?.getD (⟨0⟩ : UInt256)).toNat +
                                                      (state.machineState.stack[2]?.getD (⟨0⟩ : UInt256)).toNat) := by
                                              intro hbad
                                              rcases hbad with ⟨hwret, hretBad⟩
                                              apply hBadReturnData
                                              refine ⟨hwret, ?_⟩
                                              simpa [List.getD_eq_getElem?_getD, state₁] using hretBad
                                            have hNoOverflowZ :
                                                ¬ 1024 <
                                                  state.machineState.stack.length - (δ w).getD 0 +
                                                    (α w).getD 0 := by
                                              simpa [state₁] using hBadOverflow
                                            have hStaticZ :
                                                (¬ state.executionEnv.perm) ∧
                                                  (w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT,
                                                      .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
                                                    (w = .CALL ∧
                                                      state.machineState.stack[2]? ≠ some (⟨0⟩ : UInt256))) := by
                                              constructor
                                              · simpa [state₁] using hperm
                                              · simpa [state₁] using hviolConcrete
                                            have hStaticPermZ : ¬ state.executionEnv.perm := hStaticZ.1
                                            have hStaticWZ :
                                                w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT,
                                                    .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
                                                  (w = .CALL ∧
                                                    state.machineState.stack[2]? ≠ some (⟨0⟩ : UInt256)) :=
                                              hStaticZ.2
                                            have hStaticWZ' :
                                                (w = .CREATE ∨ w = .CREATE2 ∨ w = .SSTORE ∨
                                                    w = .SELFDESTRUCT ∨ w = .LOG0 ∨ w = .LOG1 ∨
                                                    w = .LOG2 ∨ w = .LOG3 ∨ w = .LOG4 ∨
                                                    w = .TSTORE) ∨
                                                  w = .CALL ∧
                                                    ¬ state.machineState.stack[2]? = some (⟨0⟩ : UInt256) := by
                                              simpa using hStaticWZ
                                            simp [Z, hδ, hUnder, hMemGas, hCostGasZ,
                                              hNoBadJumpZ, hNoBadJumpiZ, hNoBadReturnZ,
                                              hNoOverflowZ, hStaticPermZ, hStaticWZ', state₁] at hZ
                                            exact hZ.symm
                                          rw [hzres]
                                          exact symZCore_after_staticMode_preserve_error
                                            hmemOk hc2 hjump hjumpi hret rfl hstatic
                                            hStaticErr hcoreOrig
                                        · have hStaticOkCond :
                                              state₁.executionEnv.perm ∨
                                                (w ∉ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT,
                                                    .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∧
                                                  (w = .CALL →
                                                    (state₁.machineState.stack[2]! == (⟨0⟩ : UInt256)) = true)) := by
                                            by_cases hperm : state₁.executionEnv.perm
                                            · exact Or.inl hperm
                                            · right
                                              constructor
                                              · intro hstaticOp
                                                apply hBadStatic
                                                exact ⟨hperm, Or.inl hstaticOp⟩
                                              · intro hwcall
                                                have hnotOptNe :
                                                    ¬ state₁.machineState.stack[2]? ≠ some (⟨0⟩ : UInt256) := by
                                                  intro hne
                                                  apply hBadStatic
                                                  exact ⟨hperm, Or.inr ⟨hwcall, hne⟩⟩
                                                have hoptEq :
                                                    state₁.machineState.stack[2]? = some (⟨0⟩ : UInt256) := by
                                                  by_contra hne
                                                  exact hnotOptNe hne
                                                have hlenCall : 3 ≤ state₁.machineState.stack.length := by
                                                  have hUnderCall :
                                                      ¬ state.machineState.stack.length <
                                                        (δ Operation.CALL).getD 0 := by
                                                    simpa [hwcall] using hUnder
                                                  have hlen7 : 7 ≤ state.machineState.stack.length := by
                                                    simpa [δ] using Nat.le_of_not_lt hUnderCall
                                                  dsimp [state₁]
                                                  omega
                                                have hlen2 : 2 < state₁.machineState.stack.length := by
                                                  omega
                                                have hsome2 :
                                                    state₁.machineState.stack[2]? =
                                                      some state₁.machineState.stack[2]! := by
                                                  rw [List.getElem?_eq_getElem hlen2]
                                                  rw [getElem!_pos state₁.machineState.stack 2 hlen2]
                                                rw [hsome2] at hoptEq
                                                have hvalueZero :
                                                    state₁.machineState.stack[2]! = (⟨0⟩ : UInt256) :=
                                                  Option.some.inj hoptEq
                                                rw [hvalueZero]
                                                rfl
                                          have h7Ok :
                                              concretizeSym concrete
                                                (D_J state.executionEnv.code { val := 0 }) sym7 =
                                                .ok (state₁, o) :=
                                            symZApplyStaticModeCondition_ok h6Ok hstatic hStaticOkCond
                                          let sym8 := symZApplySstoreStipendCondition w sym7
                                          by_cases hBadStipend :
                                              w = .SSTORE ∧
                                                state₁.machineState.gasAvailable.toNat ≤
                                                  GasConstants.Gcallstipend
                                          · rcases hBadStipend with ⟨hwsstore, hstipend⟩
                                            subst w
                                            have hStipendErr :
                                                concretizeSym concrete
                                                  (D_J state.executionEnv.code { val := 0 }) sym8 =
                                                  .error .OutOfGass := by
                                              dsimp [sym8]
                                              exact symZApplySstoreStipendCondition_error
                                                h7Ok rfl hstipend
                                            have hzres : zres = .error .OutOfGass := by
                                              have hCostGasZ :
                                                  ¬ (state.machineState.gasAvailable -
                                                        UInt256.ofNat (memoryExpansionCost state .SSTORE)).toNat <
                                                      C' state₁ .SSTORE := by
                                                simpa [state₁] using hCostGas
                                              have hNoBadJumpZ :
                                                  ¬ (Operation.SSTORE = .JUMP ∧
                                                    Z.notIn state.machineState.stack[0]?
                                                      (D_J state.executionEnv.code { val := 0 }) = true) := by
                                                simp
                                              have hNoBadJumpiZ :
                                                  ¬ (Operation.SSTORE = .JUMPI ∧
                                                    state.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
                                                    Z.notIn state.machineState.stack[0]?
                                                      (D_J state.executionEnv.code { val := 0 }) = true) := by
                                                simp
                                              have hNoBadReturnZ :
                                                  ¬ (Operation.SSTORE = .RETURNDATACOPY ∧
                                                    state.machineState.returnData.size <
                                                      (state.machineState.stack[1]?.getD (⟨0⟩ : UInt256)).toNat +
                                                        (state.machineState.stack[2]?.getD (⟨0⟩ : UInt256)).toNat) := by
                                                simp
                                              have hNoOverflowZ :
                                                  ¬ 1024 <
                                                    state.machineState.stack.length - (δ Operation.SSTORE).getD 0 +
                                                      (α Operation.SSTORE).getD 0 := by
                                                simpa [state₁] using hBadOverflow
                                              have hPermState₁ : state₁.executionEnv.perm = true := by
                                                cases hp : state₁.executionEnv.perm
                                                · exfalso
                                                  apply hBadStatic
                                                  constructor
                                                  · simp [hp]
                                                  · left
                                                    simp
                                                · rfl
                                              have hPermZ : state.executionEnv.perm = true := by
                                                simpa [state₁] using hPermState₁
                                              have hNoStaticZ :
                                                  ¬ ((¬ state.executionEnv.perm) ∧
                                                    ((Operation.SSTORE = .CREATE ∨ Operation.SSTORE = .CREATE2 ∨
                                                        Operation.SSTORE = .SSTORE ∨
                                                        Operation.SSTORE = .SELFDESTRUCT ∨
                                                        Operation.SSTORE = .LOG0 ∨ Operation.SSTORE = .LOG1 ∨
                                                        Operation.SSTORE = .LOG2 ∨ Operation.SSTORE = .LOG3 ∨
                                                        Operation.SSTORE = .LOG4 ∨ Operation.SSTORE = .TSTORE) ∨
                                                      Operation.SSTORE = .CALL ∧
                                                        ¬ state.machineState.stack[2]? = some (⟨0⟩ : UInt256))) := by
                                                intro hbad
                                                exact hbad.1 hPermZ
                                              have hStipendZ' :
                                                  (state.machineState.gasAvailable -
                                                      UInt256.ofNat (memoryExpansionCost state .SSTORE)).toNat ≤
                                                    GasConstants.Gcallstipend := by
                                                simpa [state₁] using hstipend
                                              have hStipendZ :
                                                  Operation.SSTORE = .SSTORE ∧
                                                    (state.machineState.gasAvailable -
                                                        UInt256.ofNat (memoryExpansionCost state .SSTORE)).toNat ≤
                                                      GasConstants.Gcallstipend := by
                                                exact ⟨rfl, hStipendZ'⟩
                                              simp [Z, hδ, hUnder, hMemGas, hCostGasZ,
                                                hNoBadJumpZ, hNoBadJumpiZ, hNoBadReturnZ,
                                                hNoOverflowZ, hPermZ, hNoStaticZ, hStipendZ,
                                                hStipendZ', state₁] at hZ
                                              exact hZ.symm
                                            rw [hzres]
                                            exact symZCore_after_sstoreStipend_preserve_error
                                              hmemOk hc2 hjump hjumpi hret rfl hstatic
                                              hStipendErr hcoreOrig
                                          · have hStipendOkCond :
                                                w = .SSTORE →
                                                  GasConstants.Gcallstipend <
                                                    state₁.machineState.gasAvailable.toNat := by
                                              intro hwsstore
                                              apply Nat.lt_of_not_ge
                                              intro hle
                                              exact hBadStipend ⟨hwsstore, hle⟩
                                            have h8Ok :
                                                concretizeSym concrete
                                                  (D_J state.executionEnv.code { val := 0 }) sym8 =
                                                  .ok (state₁, o) := by
                                              dsimp [sym8]
                                              exact symZApplySstoreStipendCondition_ok
                                                h7Ok hStipendOkCond
                                            by_cases hBadCreate :
                                                w.isCreate = true ∧
                                                  state₁.machineState.stack.getD 2 (⟨0⟩ : UInt256) >
                                                    (⟨49152⟩ : UInt256)
                                            · rcases hBadCreate with ⟨hisCreate, hsizeGt⟩
                                              have hcreate :
                                                  w = .CREATE ∨ w = .CREATE2 :=
                                                (operation_isCreate_eq_true_iff w).mp hisCreate
                                              have hlenCreate :
                                                  3 ≤ state₁.machineState.stack.length := by
                                                rcases hcreate with hwcreate | hwcreate2
                                                · have hlen :
                                                      3 ≤ state.machineState.stack.length := by
                                                    subst w
                                                    simpa [δ] using Nat.le_of_not_lt hUnder
                                                  dsimp [state₁]
                                                  omega
                                                · have hlen :
                                                      4 ≤ state.machineState.stack.length := by
                                                    subst w
                                                    simpa [δ] using Nat.le_of_not_lt hUnder
                                                  dsimp [state₁]
                                                  omega
                                              have hlen2 : 2 < state₁.machineState.stack.length := by
                                                omega
                                              have hsome2 :
                                                  state₁.machineState.stack[2]? =
                                                    some state₁.machineState.stack[2]! := by
                                                rw [List.getElem?_eq_getElem hlen2]
                                                rw [getElem!_pos state₁.machineState.stack 2 hlen2]
                                              have hgetD2 :
                                                  state₁.machineState.stack.getD 2 (⟨0⟩ : UInt256) =
                                                    state₁.machineState.stack[2]! := by
                                                rw [List.getD_eq_getElem?_getD]
                                                rw [hsome2]
                                                rfl
                                              have hslotGt :
                                                  state₁.machineState.stack[2]! >
                                                    (⟨49152⟩ : UInt256) := by
                                                simpa [hgetD2] using hsizeGt
                                              cases hcreateSym :
                                                  symZApplyCreateSizeCondition w sym8 with
                                              | error e =>
                                                  simp [sym8, hcreateSym, Except.bind, bind] at hcore
                                              | ok sym9 =>
                                                  simp [sym8, hcreateSym, Except.bind, bind] at hcore
                                                  cases hcore
                                                  have hCreateErr :
                                                      concretizeSym concrete
                                                        (D_J state.executionEnv.code { val := 0 }) symstate' =
                                                        .error .OutOfGass :=
                                                    symZApplyCreateSizeCondition_error
                                                      h8Ok hcreateSym hcreate hslotGt
                                                  have hzres : zres = .error .OutOfGass := by
                                                    have hCostGasZ :
                                                        ¬ (state.machineState.gasAvailable -
                                                              UInt256.ofNat (memoryExpansionCost state w)).toNat <
                                                            C' state₁ w := by
                                                      simpa [state₁] using hCostGas
                                                    have hNoBadJumpZ :
                                                        ¬ (w = .JUMP ∧
                                                          Z.notIn state.machineState.stack[0]?
                                                            (D_J state.executionEnv.code { val := 0 }) = true) := by
                                                      intro hbad
                                                      apply hBadJump
                                                      simpa [Z.notIn, Z.belongs, notIn, belongs, state₁] using hbad
                                                    have hNoBadJumpiZ :
                                                        ¬ (w = .JUMPI ∧
                                                          state.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
                                                          Z.notIn state.machineState.stack[0]?
                                                            (D_J state.executionEnv.code { val := 0 }) = true) := by
                                                      intro hbad
                                                      apply hBadJumpi
                                                      simpa [Z.notIn, Z.belongs, notIn, belongs, state₁] using hbad
                                                    have hNoBadReturnZ :
                                                        ¬ (w = .RETURNDATACOPY ∧
                                                          state.machineState.returnData.size <
                                                            (state.machineState.stack[1]?.getD (⟨0⟩ : UInt256)).toNat +
                                                              (state.machineState.stack[2]?.getD (⟨0⟩ : UInt256)).toNat) := by
                                                      intro hbad
                                                      rcases hbad with ⟨hwret, hretBad⟩
                                                      apply hBadReturnData
                                                      refine ⟨hwret, ?_⟩
                                                      simpa [List.getD_eq_getElem?_getD, state₁] using hretBad
                                                    have hNoOverflowZ :
                                                        ¬ 1024 <
                                                          state.machineState.stack.length - (δ w).getD 0 +
                                                            (α w).getD 0 := by
                                                      simpa [state₁] using hBadOverflow
                                                    have hNoStaticZ :
                                                        ¬ (state.executionEnv.perm = false ∧
                                                          ((w = .CREATE ∨ w = .CREATE2 ∨ w = .SSTORE ∨
                                                              w = .SELFDESTRUCT ∨ w = .LOG0 ∨ w = .LOG1 ∨
                                                              w = .LOG2 ∨ w = .LOG3 ∨ w = .LOG4 ∨
                                                              w = .TSTORE) ∨
                                                            w = .CALL ∧
                                                              ¬ state.machineState.stack[2]? =
                                                                some (⟨0⟩ : UInt256))) := by
                                                      intro hbad
                                                      apply hBadStatic
                                                      simpa [state₁] using hbad
                                                    have hNoStipendZ :
                                                        ¬ (w = .SSTORE ∧
                                                          (state.machineState.gasAvailable -
                                                              UInt256.ofNat (memoryExpansionCost state w)).toNat ≤
                                                            GasConstants.Gcallstipend) := by
                                                      intro hbad
                                                      apply hBadStipend
                                                      simpa [state₁] using hbad
                                                    have hBadCreateZ :
                                                        (⟨49152⟩ : UInt256) <
                                                          state.machineState.stack[2]?.getD (⟨0⟩ : UInt256) := by
                                                      simpa [List.getD_eq_getElem?_getD, state₁] using hsizeGt
                                                    simp [Z, hδ, hUnder, hMemGas, hCostGasZ,
                                                      hNoBadJumpZ, hNoBadJumpiZ, hNoBadReturnZ,
                                                      hNoOverflowZ, hNoStaticZ, hNoStipendZ,
                                                      hisCreate, hBadCreateZ, state₁] at hZ
                                                    exact hZ.symm
                                                  rw [hzres]
                                                  exact hCreateErr
                                            · cases hcreateSym :
                                                  symZApplyCreateSizeCondition w sym8 with
                                              | error e =>
                                                  simp [sym8, hcreateSym, Except.bind, bind] at hcore
                                              | ok sym9 =>
                                                  simp [sym8, hcreateSym, Except.bind, bind] at hcore
                                                  cases hcore
                                                  have hCreateOkCond :
                                                      w = .CREATE ∨ w = .CREATE2 →
                                                        state₁.machineState.stack[2]! ≤
                                                          (⟨49152⟩ : UInt256) := by
                                                    intro hcreate
                                                    have hisCreate :
                                                        w.isCreate = true :=
                                                      (operation_isCreate_eq_true_iff w).mpr hcreate
                                                    have hlenCreate :
                                                        3 ≤ state₁.machineState.stack.length := by
                                                      rcases hcreate with hwcreate | hwcreate2
                                                      · have hlen :
                                                            3 ≤ state.machineState.stack.length := by
                                                          subst w
                                                          simpa [δ] using Nat.le_of_not_lt hUnder
                                                        dsimp [state₁]
                                                        omega
                                                      · have hlen :
                                                            4 ≤ state.machineState.stack.length := by
                                                          subst w
                                                          simpa [δ] using Nat.le_of_not_lt hUnder
                                                        dsimp [state₁]
                                                        omega
                                                    have hlen2 : 2 < state₁.machineState.stack.length := by
                                                      omega
                                                    have hsome2 :
                                                        state₁.machineState.stack[2]? =
                                                          some state₁.machineState.stack[2]! := by
                                                      rw [List.getElem?_eq_getElem hlen2]
                                                      rw [getElem!_pos state₁.machineState.stack 2 hlen2]
                                                    have hgetD2 :
                                                        state₁.machineState.stack.getD 2 (⟨0⟩ : UInt256) =
                                                          state₁.machineState.stack[2]! := by
                                                      rw [List.getD_eq_getElem?_getD]
                                                      rw [hsome2]
                                                      rfl
                                                    have hnotGtSlot :
                                                        ¬ state₁.machineState.stack[2]! >
                                                          (⟨49152⟩ : UInt256) := by
                                                      intro hgt
                                                      apply hBadCreate
                                                      exact ⟨hisCreate, by simpa [hgetD2] using hgt⟩
                                                    change
                                                      state₁.machineState.stack[2]!.val ≤
                                                        (⟨49152⟩ : UInt256).val
                                                    by_contra hnotLe
                                                    have hgtNat :
                                                        (⟨49152⟩ : UInt256).val <
                                                          state₁.machineState.stack[2]!.val :=
                                                      Nat.lt_of_not_ge hnotLe
                                                    have hgtWord :
                                                        state₁.machineState.stack[2]! >
                                                          (⟨49152⟩ : UInt256) := hgtNat
                                                    exact hnotGtSlot hgtWord
                                                  have hCreateOk :
                                                      concretizeSym concrete
                                                        (D_J state.executionEnv.code { val := 0 }) symstate' =
                                                        .ok (state₁, o) :=
                                                    symZApplyCreateSizeCondition_ok
                                                      h8Ok hcreateSym hCreateOkCond
                                                  have hzres : zres = .ok (state₁, C' state₁ w) := by
                                                    have hCostGasZ :
                                                        ¬ (state.machineState.gasAvailable -
                                                              UInt256.ofNat (memoryExpansionCost state w)).toNat <
                                                            C' state₁ w := by
                                                      simpa [state₁] using hCostGas
                                                    have hNoBadJumpZ :
                                                        ¬ (w = .JUMP ∧
                                                          Z.notIn state.machineState.stack[0]?
                                                            (D_J state.executionEnv.code { val := 0 }) = true) := by
                                                      intro hbad
                                                      apply hBadJump
                                                      simpa [Z.notIn, Z.belongs, notIn, belongs, state₁] using hbad
                                                    have hNoBadJumpiZ :
                                                        ¬ (w = .JUMPI ∧
                                                          state.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
                                                          Z.notIn state.machineState.stack[0]?
                                                            (D_J state.executionEnv.code { val := 0 }) = true) := by
                                                      intro hbad
                                                      apply hBadJumpi
                                                      simpa [Z.notIn, Z.belongs, notIn, belongs, state₁] using hbad
                                                    have hNoBadReturnZ :
                                                        ¬ (w = .RETURNDATACOPY ∧
                                                          state.machineState.returnData.size <
                                                            (state.machineState.stack[1]?.getD (⟨0⟩ : UInt256)).toNat +
                                                              (state.machineState.stack[2]?.getD (⟨0⟩ : UInt256)).toNat) := by
                                                      intro hbad
                                                      rcases hbad with ⟨hwret, hretBad⟩
                                                      apply hBadReturnData
                                                      refine ⟨hwret, ?_⟩
                                                      simpa [List.getD_eq_getElem?_getD, state₁] using hretBad
                                                    have hNoOverflowZ :
                                                        ¬ 1024 <
                                                          state.machineState.stack.length - (δ w).getD 0 +
                                                            (α w).getD 0 := by
                                                      simpa [state₁] using hBadOverflow
                                                    have hNoStaticZ :
                                                        ¬ (state.executionEnv.perm = false ∧
                                                          ((w = .CREATE ∨ w = .CREATE2 ∨ w = .SSTORE ∨
                                                              w = .SELFDESTRUCT ∨ w = .LOG0 ∨ w = .LOG1 ∨
                                                              w = .LOG2 ∨ w = .LOG3 ∨ w = .LOG4 ∨
                                                              w = .TSTORE) ∨
                                                            w = .CALL ∧
                                                              ¬ state.machineState.stack[2]? =
                                                                some (⟨0⟩ : UInt256))) := by
                                                      intro hbad
                                                      apply hBadStatic
                                                      simpa [state₁] using hbad
                                                    have hNoStipendZ :
                                                        ¬ (w = .SSTORE ∧
                                                          (state.machineState.gasAvailable -
                                                              UInt256.ofNat (memoryExpansionCost state w)).toNat ≤
                                                            GasConstants.Gcallstipend) := by
                                                      intro hbad
                                                      apply hBadStipend
                                                      simpa [state₁] using hbad
                                                    have hNoCreateZ :
                                                        ¬ (w.isCreate = true ∧
                                                          (⟨49152⟩ : UInt256) <
                                                            state.machineState.stack[2]?.getD (⟨0⟩ : UInt256)) := by
                                                      intro hbad
                                                      apply hBadCreate
                                                      simpa [List.getD_eq_getElem?_getD, state₁] using hbad
                                                    simp [Z, hδ, hUnder, hMemGas, hCostGasZ,
                                                      hNoBadJumpZ, hNoBadJumpiZ, hNoBadReturnZ,
                                                      hNoOverflowZ, hNoStaticZ, hNoStipendZ,
                                                      hNoCreateZ, state₁] at hZ
                                                    exact hZ.symm
                                                  rw [hzres]
                                                  exact hCreateOk

end SymExecProofs

end Symbolic

end Ethereum
