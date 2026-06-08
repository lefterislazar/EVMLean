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
  apply maxListConsume_elem_consume hstack.left
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
          exact this.left
        · exact hknown
      ⟩
  else throw .StackUnderflow

def addCondition {s b : Nat} (sym : SymState) (c : Condition s b) (h : s ≤ sym.n) : SymState :=
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

lemma returnData_consumption : ∀ (sym : SymState), sym.evm.machineState.returnData.consumeStack ≤ sym.n := by
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

lemma accountConsumeStack_of_mem {n} {entries : List (Expr .addr × Account)}
    (hstack : maxConsumesStackAccountList entries ≤ n)
    {entry : Expr .addr × Account}
    (hmem : entry ∈ entries) :
    entry.2.consumeStack ≤ n := by
  induction entries with
  | nil => simp at hmem
  | cons head tail ih =>
      simp [maxConsumesStackAccountList] at hstack
      cases hmem with
      | head =>
          exact hstack.right.left
      | tail _ htail =>
          exact ih hstack.right.right htail

def RuntimeCode.isEmpty : RuntimeCode → Bool
  | .concrete code => code.isEmpty
  | .symbolic code => code.isEmpty

def Account.summary (account : Account) : AccountSummary :=
  .mk account.nonce account.balance account.code.isEmpty

def SymState.accountSummary (sym : SymState) (addr : Expr .addr) : AccountSummary :=
  match sym.evm.accountMap.find? addr with
  | none => .missing
  | some account => account.summary

def SymState.accountBalanceExpr (sym : SymState) (addr : Expr .addr) : Expr .word :=
  (sym.accountSummary addr).balanceExpr

def SymState.accountDeadExpr (sym : SymState) (addr : Expr .addr) : Expr .word :=
  (sym.accountSummary addr).deadExpr

def SymState.accountStorageExpr (sym : SymState) (addr : Expr .addr) : Expr .storage :=
  match sym.evm.accountMap.find? addr with
  | none => .ConcreteStore []
  | some account => account.storage

lemma accountSummary_consumption (sym : SymState) (addr : Expr .addr) :
    Expr.consumeStackAccountSummary (sym.accountSummary addr) ≤ sym.n := by
  unfold SymState.accountSummary
  cases hfind : sym.evm.accountMap.find? addr with
  | none =>
      simp [AccountSummary.missing, Expr.consumeStack]
  | some account =>
      obtain ⟨key, hmem, _⟩ := Batteries.RBMap.find?_some_mem_toList hfind
      have haccmap : sym.evm.accountMap.consumeStack ≤ sym.n := by
        have hstate := sym.hevm
        simp [State.consumeStack, maxList] at hstate
        omega
      have hacc : account.consumeStack ≤ sym.n :=
        accountConsumeStack_of_mem (by simpa [AccountMap.consumeStack] using haccmap) hmem
      have hnonce : account.nonce.consumeStack ≤ sym.n := by
        have h := hacc
        simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at h
        omega
      have hbalance : account.balance.consumeStack ≤ sym.n := by
        have h := hacc
        simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at h
        omega
      simpa [Account.summary, Expr.consumeStackAccountSummary] using
        Nat.max_le.mpr ⟨hnonce, hbalance⟩

lemma accountBalanceExpr_consumption (sym : SymState) (addr : Expr .addr) :
    (sym.accountBalanceExpr addr).consumeStack ≤ sym.n := by
  unfold SymState.accountBalanceExpr
  cases hsummary : sym.accountSummary addr with
  | mk nonce balance codeEmpty =>
      have h := accountSummary_consumption sym addr
      rw [hsummary] at h
      have hbalance : balance.consumeStack ≤ sym.n :=
        Nat.le_trans (Nat.le_max_right nonce.consumeStack balance.consumeStack)
          (by simpa [Expr.consumeStackAccountSummary] using h)
      simpa [AccountSummary.balanceExpr] using hbalance

lemma accountDeadExpr_consumption (sym : SymState) (addr : Expr .addr) :
    (sym.accountDeadExpr addr).consumeStack ≤ sym.n := by
  simpa [SymState.accountDeadExpr, AccountSummary.deadExpr] using
    accountSummary_consumption sym addr

lemma accountStorageExpr_consumption (sym : SymState) (addr : Expr .addr) :
    (sym.accountStorageExpr addr).consumeStack ≤ sym.n := by
  unfold SymState.accountStorageExpr
  cases hfind : sym.evm.accountMap.find? addr with
  | none =>
      simp [Expr.consumeStack]
  | some account =>
      obtain ⟨key, hmem, _⟩ := Batteries.RBMap.find?_some_mem_toList hfind
      have haccmap : sym.evm.accountMap.consumeStack ≤ sym.n := by
        have hstate := sym.hevm
        simp [State.consumeStack, maxList] at hstate
        omega
      have hacc : account.consumeStack ≤ sym.n :=
        accountConsumeStack_of_mem (by simpa [AccountMap.consumeStack] using haccmap) hmem
      have hstorage : account.storage.consumeStack ≤ sym.n := by
        have h := hacc
        simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at h
        omega
      exact hstorage

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
      memExpandCall 3 4 5 6
    | .DELEGATECALL | .STATICCALL =>
      memExpandCall 2 3 4 5
    | .RETURN | .REVERT =>
      memExpandWith 0 1
    | _ => pure .none
  where
    memExpandWith i j := do
      let si ← sym.stackAt i
      let sj ← sym.stackAt j
      let cost := Expr.SubNat (Expr.Cₘ (Expr.M sym.evm.machineState.activeWords si sj)) (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords))
      pure $ pure $ ⟨cost, by simp [cost, Expr.consumeStack, activeWords_consumption]; apply And.intro si.2 sj.2 ⟩
    memExpandCall i j k l := do
      let si ← sym.stackAt i
      let sj ← sym.stackAt j
      let sk ← sym.stackAt k
      let sl ← sym.stackAt l
      let cost :=
        Expr.SubNat
          (Expr.Cₘ (Expr.M (Expr.ofNat (Expr.M sym.evm.machineState.activeWords si sj)) sk sl))
          (Expr.Cₘ (Expr.toNat sym.evm.machineState.activeWords))
      pure $ pure $ ⟨cost, by
        simp [cost, Expr.consumeStack, activeWords_consumption]
        omega⟩

def symCsstore (sym : SymState) : Except SymbolicError { e : Expr .num // e.consumeStack ≤ sym.n } := do
  let s0 ← sym.stackAt 0
  let v' ← sym.stackAt 1
  let v := 
    Expr.SLoad s0 (sym.accountStorageExpr Expr.Address)
  pure <| ⟨.Csstore v v' s0 sym.evm.substate.accessedStorageKeys,
    by simp [Expr.consumeStack]
       constructor
       · simpa [v, Expr.consumeStack] using
           (Nat.max_le.mpr ⟨s0.2, accountStorageExpr_consumption sym Expr.Address⟩)
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
      let recipient := Expr.AddrOfWord s0
      let currentBalance := sym.accountBalanceExpr Expr.Address
      let recipientDead := sym.accountDeadExpr recipient
      pure ⟨Expr.Cselfdestruct recipient sym.evm.substate.accessedAccounts currentBalance recipientDead, by
        simp [recipient, currentBalance, recipientDead]
        exact ⟨s0.2, accessedAccounts_consumption sym,
          accountBalanceExpr_consumption sym Expr.Address, accountDeadExpr_consumption sym recipient⟩
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
    pure ⟨Expr.CbyteCost (Glog + topics * Glogtopic) Glogdata s1, by
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
    let recipientDead := sym.accountDeadExpr recipient
    let cost := Expr.Ccall
      targetAddr
      value
      gas
      sym.evm.machineState.gasAvailable
      sym.evm.substate.accessedAccounts
      recipientDead
    pure ⟨cost, by
      have htargetAddr : targetAddr.consumeStack ≤ sym.n := by
        simpa [targetAddr] using target.2
      simpa [cost] using
        (Nat.max_le.mpr ⟨htargetAddr,
          Nat.max_le.mpr ⟨value.2,
            Nat.max_le.mpr ⟨gas.2,
              Nat.max_le.mpr ⟨gasAvailable_consumption sym,
                Nat.max_le.mpr ⟨accessedAccounts_consumption sym,
                  accountDeadExpr_consumption sym recipient⟩⟩⟩⟩⟩)
    ⟩


def symZApplyMemoryExpansionCondition
    (sym : SymState)
    (cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }) :
    SymState :=
  let sym :=
    match cost₁? with
    | .none => sym
    | .some cost₁ =>
      let assertion := Assertion.PGEqnat (Expr.toNat sym.evm.machineState.gasAvailable) cost₁
      let c : Condition assertion.consumeStack 0 := .assert ⟨assertion, by rfl⟩ (.exception .OutOfGass)
      addCondition sym c
        (by simp [assertion, Assertion.consumeStack, Expr.consumeStack]
            exact ⟨gasAvailable_consumption sym, cost₁.2⟩)
  sym

def symZApplyMemoryExpansionAndCharge
    (sym : SymState)
    (cost₁? : Option { e : Expr .num // e.consumeStack ≤ sym.n }) :
    SymState :=
  let sym := symZApplyMemoryExpansionCondition sym cost₁?
  let sym : SymState := update_gas sym (Expr.Sub (sym.evm.machineState.gasAvailable)
        ((cost₁?).option (Expr.Lit ⟨0⟩) (λ (⟨c,_⟩ ) ↦ c.ofNat)))
        (by simp [Expr.consumeStack]
            apply And.intro (gasAvailable_consumption sym)
            cases cost₁? <;> simp [Option.option, Expr.consumeStack]
            rename_i x; exact x.2)
  sym

def symZApplyCostCondition
    (sym : SymState)
    (cost₂ : { e : Expr .num // e.consumeStack ≤ sym.n }) :
    SymState :=
  let assertion := Assertion.PGEqnat (Expr.toNat sym.evm.machineState.gasAvailable) cost₂.1
  let c : Condition assertion.consumeStack 0 := .assert ⟨assertion, by rfl⟩ (.exception .OutOfGass)
  addCondition sym c
    (by simp [assertion, Assertion.consumeStack, Expr.consumeStack]
        exact ⟨gasAvailable_consumption sym, cost₂.2⟩)

def symZApplyJumpCondition (w : Operation) (sym : SymState) :
    Except SymbolicError SymState := do
  if w = Operation.JUMP then
    let dest ← sym.stackAt 0
    let c : Condition dest.1.consumeStack 0 := .jumpValid dest.1
    pure <| addCondition sym c dest.2
  else pure sym

def symZApplyJumpiCondition (w : Operation) (sym : SymState) :
    Except SymbolicError SymState := do
  if w = Operation.JUMPI then
    let dest ← sym.stackAt 0
    let jcond ← sym.stackAt 1
    let c : Condition (max (dest.1.consumeStack) (jcond.1.consumeStack)) 0 := .jumpiValid dest.1 jcond.1
    pure <| addCondition sym c (max_le dest.2 jcond.2)
  else pure sym

def symZApplyReturnDataCopyCondition (w : Operation) (sym : SymState) :
    Except SymbolicError SymState := do
  if w = Operation.RETURNDATACOPY then
    let s1 ← sym.stackAt 1
    let s2 ← sym.stackAt 2
    let assertion := Assertion.PLEqnat
      (Expr.AddNat (Expr.toNat s1) (Expr.toNat s2))
      (Expr.BufLengthNat sym.evm.machineState.returnData)
    let c : Condition assertion.consumeStack 0 := .assert ⟨assertion, by rfl⟩ (.exception .InvalidMemoryAccess)
    pure <| addCondition sym c
      (by simp [assertion, Assertion.consumeStack, Expr.consumeStack]
          exact ⟨s1.2, s2.2, returnData_consumption sym⟩)
  else pure sym

def symZApplyStackOverflowCondition (w : Operation) (sym : SymState) :
    SymState :=
  -- TODO: track max stack size so that we can avoid this often
  let diff := sym.asp + (1025 + (δ w).getD 0 - (α w).getD 0 - sym.knownStack.length)
  let c : Condition 0 0 := .stackLT diff
  addCondition sym c (by simp)

def symZApplyStaticModeCondition (w : Operation) (sym : SymState) :
    Except SymbolicError SymState := do
  if w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] then
    let c : Condition 0 0 := .staticMode
    pure <| addCondition sym c (by simp)
  else if w = .CALL then
    let value ← sym.stackAt 2
    let c : Condition value.1.consumeStack 0 := .staticModeIfNonzero value.1
    pure <| addCondition sym c value.2
  else pure sym

def symZApplySstoreStipendCondition (w : Operation) (sym : SymState) :
    SymState :=
  if (w = .SSTORE) then
    let assertion := Assertion.PGTnat sym.evm.machineState.gasAvailable.toNat (Expr.NatLit GasConstants.Gcallstipend)
    let c : Condition assertion.consumeStack 0 := .assert ⟨assertion, by rfl⟩ (.exception .OutOfGass)
    addCondition sym c
      (by simp [assertion, Assertion.consumeStack, Expr.consumeStack]
          exact gasAvailable_consumption sym)
  else sym

def symZApplyCreateSizeCondition (w : Operation) (sym : SymState) :
    Except SymbolicError SymState := do
  if (w = .CREATE ∨ w = .CREATE2) then
    let s2 ← sym.stackAt 2
    let assertion := Assertion.PLEq s2 (Expr.Lit ⟨49152⟩)
    let c : Condition assertion.consumeStack 0 := .assert ⟨assertion, by rfl⟩ (.exception .OutOfGass)
    pure $ addCondition sym c
      (by simp [assertion, Assertion.consumeStack, Expr.consumeStack]
          exact s2.2)
  else pure sym

def symZCore (w : Operation) (sym : SymState)
  : Except SymbolicError (Expr .num × SymState) :=
  do
  let cost₁? ← symMemoryExpansionCost sym w
  let sym := symZApplyMemoryExpansionAndCharge sym cost₁?
  let cost₂ ← symC' sym w
  let sym := symZApplyCostCondition sym cost₂
  let sym ← symZApplyJumpCondition w sym
  let sym ← symZApplyJumpiCondition w sym
  let sym ← symZApplyReturnDataCopyCondition w sym
  let sym := symZApplyStackOverflowCondition w sym
  let sym ← symZApplyStaticModeCondition w sym
  let sym := symZApplySstoreStipendCondition w sym
  let sym ← symZApplyCreateSizeCondition w sym
  pure (cost₂, sym)

def symZApplyStackUnderflowCondition (w : Operation) (sym : SymState) :
    SymState :=
  if hknown : sym.knownStack.length < (δ w).getD 0 then
    let diff := sym.asp + ((δ w).getD 0 - sym.knownStack.length)
    let c : Condition 0 diff := .stackGE diff
    addCondition sym c (by simp)
  else sym

def symZ (w : Operation) (sym : SymState)
  : Except SymbolicError (Expr .num × SymState) :=
  do
  if δ w = none then
    .error .InvalidInstruction -- Should I give something else?
  let sym := symZApplyStackUnderflowCondition w sym
  symZCore w sym

/-
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
    -/
