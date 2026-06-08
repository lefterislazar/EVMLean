import Ethereum.Theory.OpcodeLemmas
import Ethereum.GasConstants

import Ethereum.Symbolic.Expr
import Ethereum.Symbolic.State
import Ethereum.Symbolic.Concrete

open Ethereum.EVM GasConstants

namespace Ethereum

namespace Symbolic

inductive SymbolicError where
  | InvalidInstruction
  | StackUnderflow

def belongs (o : Option UInt256) (l : Array UInt256) : Bool :=
  match o with
    | none => false
    | some n => l.contains n

def notIn (o : Option UInt256) (l : Array UInt256) : Bool := not (belongs o l)

def SymState.knownStack (sym : SymState) : List (Expr .word) :=
  match sym.evm.machineState.stack with
  | .Stack known _ => known

-- Abstract stack pointer
def SymState.asp (sym : SymState) : Nat :=
  match sym.evm.machineState.stack with
  | .Stack _ asp => asp

lemma stack_consumption : ∀ (sym : SymState), sym.evm.machineState.stack.consumeStack ≤ sym.n := by
  intro sym
  set sym.evm := sym.evm
  set sym.hevm := sym.hevm
  simp [State.consumeStack, MachineState.consumeStack, maxList] at sym.hevm
  grind

lemma maxListConsume_elem_consume {τ n} {es : List (Expr τ)} :  Expr.maxConsumesStackList es ≤ n → ∀ e, e ∈ es → e.consumeStack ≤ n := by
  intro hlt e hin
  induction es with
  | nil => simp at hin
  | cons head tail ih =>
    cases hin <;> simp [Expr.maxConsumesStackList] at hlt
    · exact hlt.1
    · rename_i h_in_tail
      apply ih (hlt.2) h_in_tail

lemma stackKnown_consumption : ∀ (sym : SymState) x, x ∈ sym.knownStack → x.consumeStack ≤ sym.n := by
  intro sym x hin
  set sym.evm := sym.evm
  set sym.hevm := sym.hevm
  simp [State.consumeStack, MachineState.consumeStack, maxList] at sym.hevm
  have hstack : sym.evm.machineState.stack.consumeStack ≤ sym.n := by
    grind
  simp [SymState.knownStack] at hin
  split at hin
  rename_i hstackConstr
  rw [hstackConstr] at hstack
  simp [Expr.consumeStack] at hstack
  set symstack := sym.evm.machineState.stack
  apply maxListConsume_elem_consume hstack
  · exact hin


def SymState.stackAt (sym : SymState) (idx : Nat) : Except SymbolicError { e : Expr .word // e.consumeStack ≤ sym.n } :=
  if h : sym.asp + (idx - sym.knownStack.length) < sym.n
  then 
    pure ⟨sym.knownStack[idx]?.getD (Expr.StackItem <| sym.asp + (idx - sym.knownStack.length))
      ,
      by
      cases hknown : (sym.knownStack[idx]?)
      · simp [Expr.consumeStack]
        -- apply Nat.le_of_lt
        apply Nat.add_one_le_of_lt h
      · simp
        simp [SymState.knownStack] at hknown
        split at hknown; rename_i heq
        apply List.mem_of_getElem? at hknown
        set sym.hevm := sym.hevm
        -- simp [State.consumeStack, maxList, MachineState.consumeStack] at sym.hevm
        have : sym.evm.machineState.stack.consumeStack ≤ sym.n := stack_consumption sym
        apply maxListConsume_elem_consume
        · rw [heq] at this
          simp [Expr.consumeStack] at this
          exact this
        · exact hknown
      ⟩
  else throw .StackUnderflow

def addCondition (sym : SymState) (c : Condition s b) (h : s ≤ sym.n) : SymState :=
  { 
    n := max b sym.n
    conditions :=
      (ConditionChain.cons sym.conditions h (by simp) c : ConditionChain (max b sym.n))
    evm := sym.evm
    hevm := by apply le_trans sym.hevm (by simp)
  }

lemma gasAvailable_consumption : ∀ (sym : SymState), sym.evm.machineState.gasAvailable.consumeStack ≤ sym.n := by
  intro sym
  set sym.evm := sym.evm
  set sym.hevm := sym.hevm
  simp [State.consumeStack, MachineState.consumeStack, maxList] at sym.hevm
  grind

def update_gas (sym : SymState) (e : Expr .word) (h : e.consumeStack ≤ sym.n) : SymState :=
  { n := sym.n
    conditions := sym.conditions
    evm := { sym.evm with
             machineState.gasAvailable := e }
    hevm := by
      simp [State.consumeStack, maxList]
      set sym.hevm := sym.hevm
      simp [State.consumeStack, maxList] at sym.hevm
      apply And.intro
      · exact sym.hevm.1
      · apply And.right at sym.hevm
        apply And.intro
        · exact sym.hevm.1
        · apply And.right at sym.hevm
          apply And.intro
          · apply And.left at sym.hevm
            simp [MachineState.consumeStack, maxList]
            simp [MachineState.consumeStack, maxList] at sym.hevm
            apply And.intro
            · exact sym.hevm.1
            · apply And.right at sym.hevm
              apply And.intro
              · exact sym.hevm.1
              · apply And.right at sym.hevm
                apply And.intro
                · exact h
                · apply And.right at sym.hevm
                  apply And.intro
                  · exact sym.hevm.1
                  · apply And.right at sym.hevm
                    apply And.intro
                    · exact sym.hevm.1
                    · apply And.right at sym.hevm
                      apply And.intro
                      · exact sym.hevm.1
                      · apply And.right at sym.hevm
                        exact sym.hevm
          · exact sym.hevm.2
    }

lemma activeWords_consumption : ∀ (sym : SymState), sym.evm.machineState.activeWords.consumeStack ≤ sym.n := by
  intro sym
  set sym.evm := sym.evm
  set sym.hevm := sym.hevm
  simp [State.consumeStack, MachineState.consumeStack, maxList] at sym.hevm
  grind

lemma accessedAccounts_consumption : ∀ (sym : SymState), Expr.maxConsumesStackList sym.evm.substate.accessedAccounts ≤ sym.n := by
  intro sym
  have hstate := sym.hevm
  simp [State.consumeStack, Substate.consumeStack, maxList] at hstate
  omega

lemma accessedStorageKeys_consumption : ∀ (sym : SymState), Expr.maxConsumesStackList sym.evm.substate.accessedStorageKeys ≤ sym.n := by
  intro sym
  have hstate := sym.hevm
  simp [State.consumeStack, Substate.consumeStack, maxList] at hstate
  omega

-- def symMemoryExpansionCostCond (sym : SymState) (instr : Operation) : Except SymbolicError SymState :=
def symMemoryExpansionCost (sym : SymState) (instr : Operation) :
    Except SymbolicError (Option { e : Expr .num // e.consumeStack ≤ sym.n }) :=
  let stack := sym.evm.machineState.stack
  match instr with
    | .KECCAK256 =>
      memExpandWith 0 1
    | .CALLDATACOPY | .CODECOPY =>
      memExpandWith 0 2
    | .MCOPY => do
      let s0 ← sym.stackAt 0
      let s1 ← sym.stackAt 1
      let s2 ← sym.stackAt 2
      let cost := Expr.SubNat (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords (Expr.Max s0 s1) s2)) (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords))
      pure $ pure $ ⟨cost, by simp [cost, Expr.consumeStack, activeWords_consumption]; exact ⟨s0.2, (⟨s1.2, s2.2⟩)⟩⟩
    | .EXTCODECOPY =>
      memExpandWith 1 3
    | .RETURNDATACOPY =>
      memExpandWith 0 2
    | .MLOAD | .MSTORE => do
      let s0 ← sym.stackAt 0
      let cost := Expr.SubNat (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords s0 (.Lit ⟨32⟩))) (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords))
      pure $ pure $ ⟨cost, by simp [cost, Expr.consumeStack, activeWords_consumption]; exact s0.2⟩
    | .MSTORE8 => do
      let s0 ← sym.stackAt 0
      let cost := Expr.SubNat (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords s0 (.Lit ⟨1⟩))) (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords))
      pure $ pure $ ⟨cost, by simp [cost, Expr.consumeStack, activeWords_consumption]; exact s0.2⟩
    | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 =>
      memExpandWith 0 1
    | .CREATE | .CREATE2 =>
      memExpandWith 1 2
    | .CALL | .CALLCODE =>
      memExpandWith 3 4
    | .DELEGATECALL | .STATICCALL =>
      memExpandWith 2 3
    | .RETURN | .REVERT =>
      memExpandWith 0 1
    | _ => pure .none
  where
    memExpandWith i j := do
      let si ← sym.stackAt i
      let sj ← sym.stackAt j
      let cost := Expr.SubNat (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords si sj)) (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords))
      pure $ pure $ ⟨cost, by simp [cost, Expr.consumeStack, activeWords_consumption]; apply And.intro si.2 sj.2 ⟩

def symCsstore (sym : SymState) : Except SymbolicError { e : Expr .num // e.consumeStack ≤ sym.n } := do
  let s0 ← sym.stackAt 0
  let v' ← sym.stackAt 1
  let v := 
    Expr.SLoad s0 (.AbstractStore .Address 0)
   --  : Expr .word → Expr .buf → Expr .word
  pure <| ⟨.Csstore v v' s0 sym.evm.substate.accessedStorageKeys,
    by simp [Expr.consumeStack]
       constructor
       · simpa [v, Expr.consumeStack] using s0.2
       · constructor
         · exact v'.2
         · constructor
           · exact s0.2
           · have hstate := sym.hevm
             simp [State.consumeStack, Substate.consumeStack, maxList] at hstate
             omega
  ⟩

def symC' (sym : SymState) (instr : Operation) :
    Except SymbolicError { e : Expr .num // e.consumeStack ≤ sym.n } :=
  match instr with
    | .SSTORE => symCsstore sym
    | .TSTORE => pure ⟨Expr.NatLit Gwarmaccess, by simp [Expr.consumeStack]⟩
    | .EXP => do
      let s1 ← sym.stackAt 1
      pure ⟨Expr.Cexp s1, by
        simpa using s1.2⟩
    | .EXTCODECOPY => do
      let s0 ← sym.stackAt 0
      let s3 ← sym.stackAt 3
      let cost := Expr.AddNat
        (Expr.Caccess (Expr.AddrOfWord s0) sym.evm.substate.accessedAccounts)
        (Expr.CwordCost 0 Gcopy s3)
      pure ⟨cost, by
        simp [cost]
        exact ⟨s0.2, accessedAccounts_consumption sym, s3.2⟩
      ⟩
    | .LOG0 => logCost 0
    | .LOG1 => logCost 1
    | .LOG2 => logCost 2
    | .LOG3 => logCost 3
    | .LOG4 => logCost 4
    | .SELFDESTRUCT => do
      let s0 ← sym.stackAt 0
      pure ⟨Expr.Cselfdestruct s0 sym.evm.substate.accessedAccounts, by
        simpa using (Nat.max_le.mpr ⟨s0.2, accessedAccounts_consumption sym⟩)
      ⟩
    | .CREATE => do
      let s2 ← sym.stackAt 2
      pure ⟨Expr.CwordCost Gcreate Ginitcodeword s2, by
        simpa using s2.2⟩
    | .CREATE2 => do
      let s2 ← sym.stackAt 2
      let cost := Expr.AddNat
        (Expr.CwordCost Gcreate Ginitcodeword s2)
        (Expr.CwordCost 0 Gkeccak256word s2)
      pure ⟨cost, by
        simp [cost]
        exact s2.2⟩
    | .KECCAK256 => do
      let s1 ← sym.stackAt 1
      pure ⟨Expr.CwordCost Gkeccak256 Gkeccak256word s1, by
        simpa using s1.2⟩
    | .JUMPDEST => pure ⟨Expr.NatLit Gjumpdest, by simp [Expr.consumeStack]⟩
    | .SLOAD => do
      let s0 ← sym.stackAt 0
      pure ⟨Expr.Csload s0 sym.evm.substate.accessedStorageKeys, by
        simpa using (Nat.max_le.mpr ⟨s0.2, accessedStorageKeys_consumption sym⟩)
      ⟩
    | .TLOAD => pure ⟨Expr.NatLit Ctload, by simp [Expr.consumeStack]⟩
    | .BLOCKHASH => pure ⟨Expr.NatLit Gblockhash, by simp [Expr.consumeStack]⟩
    /-
      By `μₛ[2]` the YP means the value that is to be transferred,
      not what happens to be on the stack at index 2. Therefore it is 0 for
      `DELEGATECALL` and `STATICCALL`.
    -/
    | .CALL => callCost (valueFromStack := true) (recipientIsTarget := true)
    | .CALLCODE => callCost (valueFromStack := true) (recipientIsTarget := false)
    | .DELEGATECALL => callCost (valueFromStack := false) (recipientIsTarget := false)
    | .STATICCALL => callCost (valueFromStack := false) (recipientIsTarget := true)
    | .BLOBHASH => pure ⟨Expr.NatLit HASH_OPCODE_GAS, by simp [Expr.consumeStack]⟩
    | w =>
      if w ∈ Ethereum.EVM.InstructionGasGroups.Wcopy then do
        let s2 ← sym.stackAt 2
        pure ⟨Expr.CwordCost Gverylow Gcopy s2, by
          simpa using s2.2⟩
      else if w ∈ Ethereum.EVM.InstructionGasGroups.Wextaccount then do
        let s0 ← sym.stackAt 0
        pure ⟨Expr.Caccess (Expr.AddrOfWord s0) sym.evm.substate.accessedAccounts, by
          simpa using (Nat.max_le.mpr ⟨s0.2, accessedAccounts_consumption sym⟩)
        ⟩
      else
        pure ⟨Expr.NatLit $
          if w ∈ Ethereum.EVM.InstructionGasGroups.Wzero then Gzero else
          if w ∈ Ethereum.EVM.InstructionGasGroups.Wbase then Gbase else
          if w ∈ Ethereum.EVM.InstructionGasGroups.Wverylow then Gverylow else
          if w ∈ Ethereum.EVM.InstructionGasGroups.Wlow then Glow else
          if w ∈ Ethereum.EVM.InstructionGasGroups.Wmid then Gmid else
          if w ∈ Ethereum.EVM.InstructionGasGroups.Whigh then Ghigh else
          0, by simp [Expr.consumeStack]⟩
where
  logCost (topics : Nat) := do
    let s1 ← sym.stackAt 1
    pure ⟨Expr.CwordCost (Glog + topics * Glogtopic) Glogdata s1, by
      simpa using s1.2⟩
  callCost (valueFromStack recipientIsTarget : Bool) := do
    let gas ← sym.stackAt 0
    let target ← sym.stackAt 1
    let value ←
      if valueFromStack then
        sym.stackAt 2
      else
        pure ⟨Expr.Lit ⟨0⟩, by simp [Expr.consumeStack]⟩
    let targetAddr := Expr.AddrOfWord target
    let recipient := if recipientIsTarget then targetAddr else Expr.Address
    let cost := Expr.Ccall
      targetAddr
      recipient
      value
      gas
      sym.evm.machineState.gasAvailable
      sym.evm.substate.accessedAccounts
    pure ⟨cost, by
      have htargetAddr : targetAddr.consumeStack ≤ sym.n := by
        simpa [targetAddr] using target.2
      have hrecipient : recipient.consumeStack ≤ sym.n := by
        cases recipientIsTarget
        · simp [recipient, Expr.consumeStack]
        · simpa [recipient, targetAddr] using target.2
      simpa [cost] using
        (Nat.max_le.mpr ⟨htargetAddr,
          Nat.max_le.mpr ⟨hrecipient,
            Nat.max_le.mpr ⟨value.2,
              Nat.max_le.mpr ⟨gas.2,
                Nat.max_le.mpr ⟨gasAvailable_consumption sym, accessedAccounts_consumption sym⟩⟩⟩⟩⟩)
    ⟩


def symZ (code : ByteArray) (validJumps : Array UInt256) (w : Operation) (sym : SymState)
  : Except SymbolicError (Expr .num × SymState) :=
  do 
  if δ w = none then
    .error .InvalidInstruction -- Should I give something else?
  let sym :=
    if hknown : sym.knownStack.length < (δ w).getD 0 then
      let diff := (δ w).getD 0 - sym.knownStack.length
      let c := (.stackGE diff)
      addCondition sym c (by simp)
    else sym
  let cost₁? ← symMemoryExpansionCost sym w
  let sym :=
    match cost₁? with
    | .none => sym
    | .some cost₁ =>
      let assertion := Assertion.PGEqnat (Expr.toNat sym.evm.machineState.gasAvailable) cost₁
      let c : Condition assertion.consumeStack 0 := .assert ⟨assertion, by rfl⟩ (.exception .OutOfGass)
      addCondition sym c
        (by simp [assertion, Assertion.consumeStack, Expr.consumeStack]
            exact ⟨gasAvailable_consumption sym, cost₁.2⟩)
  let sym : SymState := update_gas sym (Expr.Sub (sym.evm.machineState.gasAvailable)
        ((cost₁?).option (Expr.Lit ⟨0⟩) (λ (⟨c,_⟩ ) ↦ c.ofNat)))
        (by simp [Expr.consumeStack]
            apply And.intro (gasAvailable_consumption sym)
            cases cost₁? <;> simp [Option.option, Expr.consumeStack]
            rename_i x; exact x.2)
  let cost₂? ← symC' sym w





def symstep (code : ByteArray) (validJumps : Array UInt256) (sym : SymState) : Option SymState :=
  match sym.evm.machineState.pc with
  | .Lit n => do
    let instr <- decode code n
    match instr with
    | (.ADD, .none) =>
      .some
        { sym with
          conditions :=
            (Assertion.PLEqnat (Expr.NatLit 2) (Expr.StackSize (sym.evm.machineState.stack)), (Failure.exception .StackUnderflow)) ::
            (Assertion.PLEq (Expr.Lit ⟨3⟩) ((sym.evm.machineState.gasAvailable)), (Failure.exception .OutOfGass)) ::
            (Assertion.PLEqnat (Expr.StackSize (sym.evm.machineState.stack)) (Expr.NatLit 1025), (Failure.exception .StackOverflow)) :: sym.conditions
          evm.machineState.stack :=
            match sym.evm.machineState.stack with
            | .Stack (s0 :: s1 :: s') n => .Stack ((Expr.Add s0 s1) :: s') n
            | .Stack (s0 :: []) n => .Stack ((Expr.Add s0 (.StackItem n)) :: []) (n+1)
            | .Stack [] n => .Stack [Expr.Add (.StackItem n) (.StackItem (n+1))] (n+2)
          evm.machineState.gasAvailable :=
            (Expr.Sub sym.evm.machineState.gasAvailable (Expr.Lit ⟨3⟩))
          evm.machineState.pc := (Expr.Lit (n + ⟨1⟩))
          evm.machineState.execLength := sym.evm.machineState.execLength + 1
        }

    | (.SUB, .none) =>
      .some
        { sym with
          conditions :=
            (Assertion.PLEqnat (Expr.NatLit 2) (Expr.StackSize (sym.evm.machineState.stack)), (Failure.exception .StackUnderflow)) ::
            (Assertion.PLEq (Expr.Lit ⟨3⟩) ((sym.evm.machineState.gasAvailable)), (Failure.exception .OutOfGass)) ::
            (Assertion.PLEqnat (Expr.StackSize (sym.evm.machineState.stack)) (Expr.NatLit 1025), (Failure.exception .StackOverflow)) :: sym.conditions
          evm.machineState.stack :=
            match sym.evm.machineState.stack with
            | .Stack (s0 :: s1 :: s') n => .Stack ((Expr.Sub s0 s1) :: s') n
            | .Stack (s0 :: []) n => .Stack ((Expr.Sub s0 (.StackItem n)) :: []) (n+1)
            | .Stack [] n => .Stack [Expr.Sub (.StackItem n) (.StackItem (n+1))] (n+2)
          evm.machineState.gasAvailable :=
            (Expr.Sub sym.evm.machineState.gasAvailable (Expr.Lit ⟨3⟩))
          evm.machineState.pc := (Expr.Lit (n + ⟨1⟩))
          evm.machineState.execLength := sym.evm.machineState.execLength + 1
        }

    | (.PUSH0, .none) =>
      .some
        { sym with
          conditions :=
            (Assertion.PLEqnat (Expr.StackSize (sym.evm.machineState.stack)) (Expr.NatLit 1025), (Failure.exception .StackOverflow)) ::
            (Assertion.PLEq (Expr.Lit ⟨2⟩) ((sym.evm.machineState.gasAvailable)), (Failure.exception .OutOfGass)) :: sym.conditions
          evm.machineState.stack :=
            match sym.evm.machineState.stack with
            | .Stack known n => .Stack ((Expr.Lit ⟨0⟩) :: known) n
          evm.machineState.gasAvailable :=
            (Expr.Sub sym.evm.machineState.gasAvailable (Expr.Lit ⟨2⟩))
          evm.machineState.pc := (Expr.Lit (n + ⟨1⟩))
          evm.machineState.execLength := sym.evm.machineState.execLength + 1
        }
    | (.PUSH1, .some (arg,1)) =>
      .some
        { sym with
          conditions :=
            (Assertion.PLEqnat (Expr.StackSize (sym.evm.machineState.stack)) (Expr.NatLit 1025), (Failure.exception .StackOverflow)) ::
            (Assertion.PLEq (Expr.Lit ⟨2⟩) ((sym.evm.machineState.gasAvailable)), (Failure.exception .OutOfGass)) :: sym.conditions
          evm.machineState.stack :=
            match sym.evm.machineState.stack with
            | .Stack known n => .Stack (Expr.Lit arg :: known) n
          evm.machineState.gasAvailable :=
            (Expr.Sub sym.evm.machineState.gasAvailable (Expr.Lit ⟨2⟩))
          evm.machineState.pc := (Expr.Lit (n + ⟨1⟩))
          evm.machineState.execLength := sym.evm.machineState.execLength + 1
        }

    | _ => .none
  | _ => .none


lemma pc_lit_if_symstep_some {bytecode : ByteArray} {validJumps : Array UInt256} {symstate symstate' : SymState} :
  symstep bytecode validJumps symstate = .some symstate' →
  ∃ n, symstate.evm.machineState.pc = .Lit n := by
    intro hsymstep
    simp [symstep] at hsymstep
    split at hsymstep
    · rename_i n hn; exact ⟨n,hn⟩
    · contradiction

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

lemma list_len_ge_2_to_match :
    2 ≤ List.length l →
    ∃ a b t, l = a :: b :: t := by
      intro h
      match l with
      | [] => simp at h
      | _ :: [] => simp at h
      | a :: b :: t => simp

-- lemma UInt256_ofNat_n_eq_val_n : ∀ n (h : n < UInt256.size), { val := { val := n, isLt := h}} = UInt256.ofNat n := by
--   intro n h
--   simp [UInt256.ofNat, Id.run, cast]
--   rfl

lemma list_get_dropped : a :: t = List.drop n l → l[n]? = .some a := by
  intro h
  rw [List.drop_eq_getElem_cons] at h
  simp at h
  symm
  rw [h.left]
  rw [List.some_getElem_eq_getElem?_iff]
  · simp
  · apply List.length_lt_of_drop_ne_nil; simp [← h]

theorem sumStep_Xstep_consistent {state : Ethereum.State} {xres : Except ExecutionException (Ethereum.State × Option (Bool × ByteArray))}
  {concrete : Ethereum.State} {symstate symstate' : SymState} {o : Option (Bool × ByteArray)}
  {validJumps : Array UInt256} :
  let bytecode := state.executionEnv.code
  state.machineState.stack.length ≤ 1024 →
  Xstep (D_J bytecode { val := 0 }) state = xres →
  -- models symstate (.ok (state, o)) → 
  concretizeSym concrete symstate = .ok (state, o) →
  symstep bytecode validJumps symstate = .some symstate' →
  concretizeSym concrete symstate' = xres
  := by
    intro bytecode hstack_bound hxstep hmodel hsymstep

    have hmodel' : state = concretizeState concrete symstate.evm := by
      apply if_concretizeOk_then_state hmodel

    have hmodel_stack : state.machineState.stack = concretizeExpr concrete symstate.evm.machineState.stack := by
      rw [hmodel']; simp [concretizeState, concretizeMachineState]
    have hmodel_gas : state.machineState.gasAvailable = concretizeExpr concrete symstate.evm.machineState.gasAvailable := by
      rw [hmodel']; simp [concretizeState, concretizeMachineState]
    have hmodel_execLen : state.machineState.execLength = symstate.evm.machineState.execLength := by
      rw [hmodel']; simp [concretizeState, concretizeMachineState]
    have hmodel_activeWords : state.machineState.activeWords = concretizeExpr concrete symstate.evm.machineState.activeWords := by
      rw [hmodel']; simp [concretizeState, concretizeMachineState]
    have hmodel_memory : state.machineState.memory = concretizeExpr concrete symstate.evm.machineState.memory := by
      rw [hmodel']; simp [concretizeState, concretizeMachineState]
    have hmodel_retData : state.machineState.returnData = concretizeExpr concrete symstate.evm.machineState.returnData := by
      rw [hmodel']; simp [concretizeState, concretizeMachineState]
    have hmodel_Hreturn : state.machineState.H_return = concretizeExpr concrete symstate.evm.machineState.H_return := by
      rw [hmodel']; simp [concretizeState, concretizeMachineState]
    have hmodel_accMap : state.accountMap = concretizeAccountMap concrete symstate.evm.accountMap := by
      rw [hmodel']; simp [concretizeState]
    have hmodel_substate : state.substate = concretizeSubstate concrete symstate.evm.substate := by
      rw [hmodel']; simp [concretizeState]
    have hmodel_createdAccs : state.createdAccounts = addListToSet compare symstate.evm.createdAccounts concrete.createdAccounts
      (concretizeExpr concrete) := by rw [hmodel']; simp [concretizeState]
    have hmodel_accMap0 : state.σ₀ = concrete.σ₀ := by
      rw [hmodel']; simp [concretizeState]
    have hmodel_totalGas : state.totalGasUsedInBlock = concrete.totalGasUsedInBlock := by
      rw [hmodel']; simp [concretizeState]
    have hmodel_transRec : state.transactionReceipts = concrete.transactionReceipts := by
      rw [hmodel']; simp [concretizeState]
    have hmodel_execEnv : state.executionEnv = concrete.executionEnv := by
      rw [hmodel']; simp [concretizeState]
    have hmodel_blocks : state.blocks = concrete.blocks := by
      rw [hmodel']; simp [concretizeState]
    have hmodel_genHeader : state.genesisBlockHeader = concrete.genesisBlockHeader := by
      rw [hmodel']; simp [concretizeState]

    have hpc_lit : ∃ n, symstate.evm.machineState.pc = .Lit n := pc_lit_if_symstep_some hsymstep
    cases hpc_lit; rename_i n hpc_lit

    have hpc_lit_concrete : n = state.machineState.pc := by
      rw [hmodel']
      simp [concretizeState, concretizeMachineState, concretizeExpr, hpc_lit]

    #check step_add
    -- simp [Xstep] at hxstep
    simp [symstep] at hsymstep
    rw [hpc_lit] at hsymstep
    simp at hsymstep
    cases h: decode bytecode n with
    | some oparg => 
      simp [h] at hsymstep
      match hoparg : oparg with
      | (.ADD, none) =>
          simp at hsymstep
          rw [Ethereum.EVM.step_add] at hxstep
          · simp [concretizeSym]
            rw [← hsymstep]
            simp [concretizeAssertion, concretizeExpr]
            rw [← hmodel_stack]
              
            split <;> rename_i h_stackunder
            · -- 
              obtain ⟨s0, s1, st2, h_stack_2⟩ := list_len_ge_2_to_match h_stackunder
              rw [h_stack_2] at hxstep
              simp at hxstep
              
              split <;> rename_i h_gas
              · 
                rw [← hmodel_gas] at h_gas
                have h_gas_nat : ¬ state.machineState.gasAvailable.toNat < 3 := by
                  change ¬ state.machineState.gasAvailable.val < 3
                  change 3 ≤ state.machineState.gasAvailable.val at h_gas
                  omega
                rw [GasConstants.Gverylow] at hxstep
                simp [h_gas_nat] at hxstep

                split <;> rename_i h_stackover
                · -- all good
                  simp [h_stack_2] at h_stackover
                  have h_stackover' : ¬ 1024 < st2.length + 1 := by omega
                  simp [h_stackover'] at hxstep

                  have h_noexcept := if_concretizeOk_then_noexcept hmodel
                  rw [if_noexcept_then_concrete_state symstate.conditions h_noexcept]


                  simp [ concretizeState, ← hmodel_accMap, ← hmodel_accMap0, ← hmodel_totalGas
                  , ← hmodel_transRec, ← hmodel_execEnv, ← hmodel_blocks, ← hmodel_genHeader, ← hmodel_substate, ← hmodel_createdAccs
                  , ← hmodel_execLen, hmodel_activeWords, hmodel_memory, hmodel_retData, hmodel_Hreturn
                  , ← hxstep]
                  simp [concretizeMachineState]
                  apply And.intro
                  · simp [concretizeExpr]; subst n; rfl
                  · apply And.intro
                    · 
                      split
                      · rename_i hsymstack
                        simp [concretizeExpr]
                        apply And.intro <;>
                          (simp [hsymstack, concretizeExpr, h_stack_2] at hmodel_stack;
                           simp [hmodel_stack.left, hmodel_stack.right])
                      · rename_i hsymstack
                        simp [concretizeExpr]
                        apply And.intro
                        · simp [hsymstack, concretizeExpr, h_stack_2] at hmodel_stack
                          simp [hmodel_stack.left]
                          rename_i n
                          simp [list_get_dropped (hmodel_stack.right)]
                        · simp [hsymstack, concretizeExpr, h_stack_2] at hmodel_stack
                          obtain hstack_drop := hmodel_stack.right 
                          rw [List.drop_eq_getElem_cons] at hstack_drop
                          · simp at hstack_drop
                            rw [← hstack_drop.right]
                          · apply List.length_lt_of_drop_ne_nil
                            simp [← hstack_drop]
                      · rename_i hsymstack
                        simp [concretizeExpr]
                        apply And.intro
                        · simp [hsymstack, concretizeExpr, h_stack_2] at hmodel_stack
                          rw [List.drop_eq_getElem_cons] at hmodel_stack
                          · rw [List.drop_eq_getElem_cons] at hmodel_stack
                            · simp at hmodel_stack
                              obtain ⟨h0, h1, h2⟩ := hmodel_stack
                              rename_i n
                              simp [h0, h1]
                              grind
                            · apply List.length_lt_of_drop_ne_nil
                              simp at hmodel_stack
                              rw [← hmodel_stack.right]; simp
                          · apply List.length_lt_of_drop_ne_nil
                            simp [← hmodel_stack]

                        · simp [hsymstack, concretizeExpr, h_stack_2] at hmodel_stack
                          rw [List.drop_eq_getElem_cons] at hmodel_stack
                          · rw [List.drop_eq_getElem_cons] at hmodel_stack
                            · simp at hmodel_stack
                              obtain ⟨h0, h1, h2⟩ := hmodel_stack
                              rw [← h2]
                            · apply List.length_lt_of_drop_ne_nil
                              simp at hmodel_stack
                              rw [← hmodel_stack.right]; simp
                          · apply List.length_lt_of_drop_ne_nil
                            simp [← hmodel_stack]
                    · simp [concretizeExpr, hmodel_gas, UInt256.ofNat, Id.run]

                · -- Stack Overflow
                  simp [h_stack_2] at h_stackover
                  have h_stackover' : 1024 < st2.length + 1 := by omega
                  simp [h_stackover'] at hxstep
                  simp [← hxstep]; rfl

              · -- OutOfGas
                rw [← hmodel_gas] at h_gas

                have h_gas_nat : state.machineState.gasAvailable.toNat < 3 := by
                  change state.machineState.gasAvailable.val < 3
                  change ¬ 3 ≤ state.machineState.gasAvailable.val at h_gas
                  omega
                rw [GasConstants.Gverylow] at hxstep
                simp [h_gas_nat] at hxstep
                rw [← hxstep]
                rfl

            · -- Stack Underflow
              simp at h_stackunder
              rw [← hxstep]
              match hstack : state.machineState.stack with
              | [] => rfl
              | _ :: [] => rfl
              | s0 :: s1 :: s2 => simp [hstack] at h_stackunder; omega

          · subst bytecode; rw [← hpc_lit_concrete]; assumption 
      | _ => sorry
    | none => simp [h] at hsymstep; sorry
