import Ethereum.State

import Ethereum.Symbolic.Expr
import Ethereum.Symbolic.State

open Ethereum.EVM

namespace Ethereum

namespace Symbolic

private theorem consumeStack_le_max_of_mem
    {τ : EType} {expr : Expr τ} {exprs : List (Expr τ)} {bound : Nat}
    (hstack : Expr.maxConsumesStackList exprs ≤ bound)
    (hmem : expr ∈ exprs) :
    expr.consumeStack ≤ bound := by
  induction exprs with
  | nil => simp at hmem
  | cons head tail ih =>
      simp [Expr.maxConsumesStackList] at hstack
      cases hmem with
      | head =>
          exact hstack.left
      | tail _ htail =>
          exact ih hstack.right htail

def concretizeType (τ : EType) : Type :=
    match τ with
    | .buf => ByteArray
    -- | .contract => ByteArray
    | .byte => UInt256
    | .addr => AccountAddress
    | .word => UInt256
    | .log => LogEntry
    | .stack => Stack UInt256
    | .storage => Storage
    | .num => Nat

def defaultConcretizeType : (τ : EType) → concretizeType τ
  | .buf => ByteArray.empty
  | .storage => Batteries.mkRBMap UInt256 UInt256 compare
  | .stack => []
  | .log => { address := default, topics := #[], data := ByteArray.empty }
  | .word => ⟨0⟩
  | .addr => Fin.ofNat AccountAddress.size 0
  | .byte => ⟨0⟩
  | .num => Nat.zero --0

mutual 
def concretizeExpr {τ : EType} 
  (concrete : Ethereum.State)
  (expr : Expr τ)
  (hstack : expr.consumeStack ≤ concrete.machineState.stack.length)
  : concretizeType τ := 
  match expr with
  | .Lit lit => lit
  | .NatLit n => n
  | .LitByte byte => { val := Fin.castLE (by simp [UInt256.size] : 2^8 ≤ UInt256.size) byte.toBitVec.toFin }
  | .IndexWord idx val => Ethereum.UInt256.byteAt
                            (concretizeExpr concrete idx (by simp [Expr.consumeStack] at hstack; exact hstack.left))
                            (concretizeExpr concrete val (by simp [Expr.consumeStack] at hstack; exact hstack.right))
  | .EqByte a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right)
      if a' == b' then ⟨1⟩ else ⟨0⟩
  -- | .JoinBytes
  --   b0  b1  b2  b3  b4  b5  b6  b7
  --   b8  b9  b10 b11 b12 b13 b14 b15
  --   b16 b17 b18 b19 b20 b21 b22 b23
  --   b24 b25 b26 b27 b28 b29 b30 b31 =>
  | .Add a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right)
      a' + b' | .Sub a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right)
      a' - b'
  | .Mul a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right)
      a' * b'
  | .Div a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right)
      UInt256.div a' b'
  | .SDiv a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right)
      UInt256.sdiv a' b'
  | .Mod a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right)
      UInt256.mod a' b'
  | .SMod a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right)
      UInt256.smod a' b'
  | .AddMod a b c =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right.left)
      let c' : UInt256 := concretizeExpr concrete c (by simp [Expr.consumeStack] at hstack; exact hstack.right.right)
      UInt256.addMod a' b' c'
  | .MulMod a b c =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right.left)
      let c' : UInt256 := concretizeExpr concrete c (by simp [Expr.consumeStack] at hstack; exact hstack.right.right)
      UInt256.mulMod a' b' c'
  | .BufLength b =>
      let b' : ByteArray := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack)
      { val := Fin.ofNat UInt256.size (b'.size) }
  | .Stack known n =>
      let known' : List (UInt256) := concretizeExprList concrete known
        (by simp [Expr.consumeStack] at hstack; exact hstack)
          -- simp [Expr.consumeStack.maxConsumesStackList] at hstack)

      known' ++ (List.drop n $ concrete.machineState.stack)
  | .StackItem n =>
      concrete.machineState.stack[n]'(by simp [Expr.consumeStack] at hstack; exact Nat.lt_of_add_one_le hstack)
  -- | .StackSize stack =>
  --     let stack' : List (UInt256) := concretizeExpr concrete stack
  --     List.length stack'
  | .LT a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Expr.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Expr.consumeStack] at hstack; exact hstack.right)
      UInt256.lt a' b'
  | _ => defaultConcretizeType τ

def concretizeExprList {τ : EType}
  (concrete : Ethereum.State)
  (exprs : List (Expr τ))
  (hstack : Expr.maxConsumesStackList exprs ≤ concrete.machineState.stack.length) :
  List (concretizeType τ) :=
    exprs.attach.map (λ ⟨expr,h_exprKnown⟩ ↦
      concretizeExpr concrete expr (consumeStack_le_max_of_mem hstack h_exprKnown))
end

-- UNUSED
private theorem consumeStack_lt_of_mem
    {τ : EType} {expr : Expr τ} {exprs : List (Expr τ)} {bound : Nat}
    (hstack : Expr.maxConsumesStackList exprs ≤ bound)
    (hmem : expr ∈ exprs) :
    expr.consumeStack ≤ bound := by
  induction exprs with
  | nil => simp at hmem
  | cons head tail ih =>
      simp [Expr.maxConsumesStackList] at hstack
      cases hmem with
      | head =>
          exact hstack.left
      | tail _ htail =>
          exact ih hstack.right htail

private theorem accountConsumeStack_lt_of_mem
    {entry : Expr .addr × Account} {entries : List (Expr .addr × Account)} {bound : Nat}
    (hstack : maxConsumesStackAccountList entries ≤ bound)
    (hmem : entry ∈ entries) :
    entry.2.consumeStack ≤ bound := by
  induction entries with
  | nil => simp at hmem
  | cons head tail ih =>
      simp [maxConsumesStackAccountList] at hstack
      cases hmem with
      | head =>
          exact hstack.right.left
      | tail _ htail =>
          exact ih hstack.right.right htail

private theorem accountKeyConsumeStack_le_of_mem
    {entry : Expr .addr × Account} {entries : List (Expr .addr × Account)} {bound : Nat}
    (hstack : maxConsumesStackAccountList entries ≤ bound)
    (hmem : entry ∈ entries) :
    entry.1.consumeStack ≤ bound := by
  induction entries with
  | nil => simp at hmem
  | cons head tail ih =>
      simp [maxConsumesStackAccountList] at hstack
      cases hmem with
      | head =>
          exact hstack.left
      | tail _ htail =>
          exact ih hstack.right.right htail

private theorem storageKeyFstConsumeStack_lt_of_mem
    {key : Expr .word} {keys : List (Expr .word)} {bound : Nat}
    (hstack : Expr.maxConsumesStackList keys ≤ bound)
    (hmem : key ∈ keys) :
    key.consumeStack ≤ bound := by
  induction keys with
  | nil => simp at hmem
  | cons head tail ih =>
      simp [Expr.maxConsumesStackList] at hstack
      cases hmem with
      | head =>
          exact hstack.left
      | tail _ htail =>
          exact ih hstack.right htail

/-
private theorem storageKeySndConsumeStack_lt_of_mem
    {key : Expr .addr × Expr .word} {keys : List (Expr .addr × Expr .word)} {bound : Nat}
    (hstack : maxConsumesStackAccessedStorageKeys keys ≤ bound)
    (hmem : key ∈ keys) :
    key.2.consumeStack ≤ bound := by
  induction keys with
  | nil => simp at hmem
  | cons head tail ih =>
      simp [maxConsumesStackAccessedStorageKeys] at hstack
      cases hmem with
      | head =>
          exact hstack.right.left
      | tail _ htail =>
          exact ih hstack.right.right htail
          -/

def RBMap.mapValues
    {κ α β : Type} {cmp : κ → κ → Ordering}
    (f : κ → α → β)
    (m : Batteries.RBMap κ α cmp) :
    Batteries.RBMap κ β cmp :=
  m.foldl
    (fun acc k v => acc.insert k (f k v))
    (Batteries.mkRBMap κ β cmp)

-- TODO: check this more
def concretizeRuntimeCode (concrete : Ethereum.State) (c : RuntimeCode) : ByteArray :=
  -- match c with
  -- | .concrete b => b
  -- | .symbolic _ =>
    let addr := concrete.executionEnv.codeOwner
    match concrete.accountMap.find? addr with
    | .none => ByteArray.empty
    | .some acc => acc.code

def concretizeAccount
    (concrete : Ethereum.State)
    (acc : Account)
    (hstack : acc.consumeStack ≤ concrete.machineState.stack.length) :
    Ethereum.Account :=
  { nonce := concretizeExpr concrete acc.nonce
      (by simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at hstack; omega)
    balance := concretizeExpr concrete acc.balance
      (by simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at hstack; omega)
    storage := concretizeExpr concrete acc.storage
      (by simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at hstack; omega)
    tstorage := concretizeExpr concrete acc.tstorage
      (by simp [Account.consumeStack, PersistentAccountState.consumeStack, maxList] at hstack; omega)
    code := concretizeRuntimeCode concrete acc.code
  }


lemma maxAccMapConsume_elem_consume {n} {es : AccountMap} :
    AccountMap.consumeStack es ≤ n →
    ∀ e, e ∈ Batteries.RBMap.toList es → e.1.consumeStack ≤ n := by
  intro hlt e hin
  exact accountKeyConsumeStack_le_of_mem (by simpa [AccountMap.consumeStack] using hlt) hin

def concretizeAccountMap
    (concrete : Ethereum.State)
    (σ : AccountMap)
    (hstack : σ.consumeStack ≤ concrete.machineState.stack.length) :
    Ethereum.AccountMap :=
  σ.toList.attach.foldl
    (fun acc entry =>
      let addr : AccountAddress :=
        concretizeExpr concrete (entry.1.1 : Expr .addr)
          (accountKeyConsumeStack_le_of_mem
            (by simpa [AccountMap.consumeStack] using hstack)
            entry.2)
      acc.insert addr
        (concretizeAccount concrete entry.1.2
          (accountConsumeStack_lt_of_mem
            (by simpa [AccountMap.consumeStack] using hstack)
            entry.2)))
    (Batteries.mkRBMap AccountAddress Ethereum.Account compare)

def addListToSet {α β : Type} (cmp) (l : List α) (s : Batteries.RBSet β cmp) (f : α → β) :=
  l.foldl (λ s' x ↦ let x' := f x; s'.insert x') s

/-
def concretizeStorageKeys
    (concrete : Ethereum.State)
    (keys : List (Expr .word))
    (hstack : Expr.maxConsumesStackList keys ≤ concrete.machineState.stack.length) :
    List (AccountAddress × UInt256) :=
  keys.attach.map fun key =>
    ( concretizeExpr concrete (key.2 : Expr .addr)
        (storageKeyFstConsumeStack_lt_of_mem hstack key.2)
    , concretizeExpr concrete (key.1.2 : Expr .word)
        (storageKeySndConsumeStack_lt_of_mem hstack key.2)
    )
    -/

def concretizeSubstate
    (concrete : Ethereum.State)
    (σ : Substate)
    (hstack : σ.consumeStack ≤ concrete.machineState.stack.length) :
    Ethereum.Substate :=
  { selfDestructSet := addListToSet compare
      (concretizeExprList concrete σ.selfDestructSet
        (by simp [Substate.consumeStack, maxList] at hstack; omega))
      concrete.substate.selfDestructSet id
    touchedAccounts := addListToSet compare
      (concretizeExprList concrete σ.touchedAccounts
        (by simp [Substate.consumeStack, maxList] at hstack; omega))
      concrete.substate.touchedAccounts id
    refundBalance := concretizeExpr concrete σ.refundBalance
      (by simp [Substate.consumeStack, maxList] at hstack; omega)
    accessedAccounts := addListToSet compare
      (concretizeExprList concrete σ.accessedAccounts
        (by simp [Substate.consumeStack, maxList] at hstack; omega))
      concrete.substate.accessedAccounts id
    accessedStorageKeys := addListToSet (Substate.storageKeysCmp)
      ((concretizeExprList concrete σ.accessedStorageKeys
        (by simp [Substate.consumeStack, maxList] at hstack; omega)).map (λ x ↦ (concrete.executionEnv.codeOwner,x)))
      concrete.substate.accessedStorageKeys id
    logSeries := (concretizeExprList concrete σ.logSeries
      (by simp [Substate.consumeStack, maxList] at hstack; omega)).toArray
  }

/-
def concretizeUninterp
  (concrete : Ethereum.State)
  (prevInterps : 
      List (Batteries.RBSet AccountAddress compare × Ethereum.AccountMap × UInt256 × Ethereum.Substate × UInt256 × ByteArray))
  (symCall : Uninterp)
  (hstack : symCall.consumeStack ≤ concrete.machineState.stack.length)
  : 
    List (Batteries.RBSet AccountAddress compare × Ethereum.AccountMap × UInt256 × Ethereum.Substate × UInt256 × ByteArray)
   :=
  match symCall with
  | .ThetaCall cA σ A Iₐ Iₒ Iᵣ Ic g p v v' i Iw =>
    let createdAccounts' : Batteries.RBSet AccountAddress compare :=
      addListToSet compare
        (concretizeExprList concrete cA
          (by simp [Uninterp.consumeStack, maxList] at hstack; omega))
        concrete.createdAccounts id
    let σ' : Ethereum.AccountMap := concretizeAccountMap concrete σ
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let A' : Ethereum.Substate := concretizeSubstate concrete A
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let Iₐ' : AccountAddress := concretizeExpr concrete Iₐ
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let Iₒ' : AccountAddress := concretizeExpr concrete Iₒ
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let Iᵣ' : AccountAddress := concretizeExpr concrete Iᵣ
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let Ic' : AccountAddress := concretizeExpr concrete Ic
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let g' : UInt256 := concretizeExpr concrete g
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let p' : UInt256 := concretizeExpr concrete p
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let v_' : UInt256 := concretizeExpr concrete v
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let v_'' : UInt256 := concretizeExpr concrete v'
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let i' : ByteArray := concretizeExpr concrete i
      (by simp [Uninterp.consumeStack, maxList] at hstack; omega)
    let (cA_ret, σ_ret, g_ret, A_ret, z_ret, o_ret) := 
      if v_' ≤ (σ'.find? Iₐ' |>.option ⟨0⟩ (·.balance)) ∧ concrete.executionEnv.depth < 1024 then
    Ethereum.EVM.Θ concrete.executionEnv.blobVersionedHashes createdAccounts' concrete.genesisBlockHeader concrete.blocks σ' concrete.σ₀ A' Iₐ' Iₒ' Iᵣ' (toExecute σ' Ic') g' p' v_' v_'' i' (concrete.executionEnv.depth + 1) concrete.executionEnv.header Iw
      else
      (createdAccounts', σ', g', A', false, .empty)
    (cA_ret, σ_ret, g_ret, A_ret, z_ret.toUInt256, o_ret) :: prevInterps 
  -- | .LambdaCall cA σ σ₀ A Iₐ Iₒ g p v v' i Iw => () :; prevInterps
  -/

def concretizeMachineState
    (concrete : Ethereum.State)
    (sym : MachineState)
    (hstack : sym.consumeStack ≤ concrete.machineState.stack.length) :
    Ethereum.MachineState :=
  {
    pc := concretizeExpr concrete sym.pc
      (by simp [MachineState.consumeStack, maxList] at hstack; omega)
    stack := concretizeExpr concrete sym.stack
      (by simp [MachineState.consumeStack, maxList] at hstack; omega)
    execLength := sym.execLength
    gasAvailable := concretizeExpr concrete sym.gasAvailable
      (by simp [MachineState.consumeStack, maxList] at hstack; omega)
    activeWords := concretizeExpr concrete sym.activeWords
      (by simp [MachineState.consumeStack, maxList] at hstack; omega)
    memory := concretizeExpr concrete sym.memory
      (by simp [MachineState.consumeStack, maxList] at hstack; omega)
    returnData  := concretizeExpr concrete sym.returnData
      (by simp [MachineState.consumeStack, maxList] at hstack; omega)
    H_return := concretizeExpr concrete sym.H_return
      (by simp [MachineState.consumeStack, maxList] at hstack; omega)
  }

def concretizeState
    (concrete : Ethereum.State)
    (sym : State)
    (hstack : sym.consumeStack ≤ concrete.machineState.stack.length) :
    Ethereum.State :=
  { concrete with
    accountMap := concretizeAccountMap concrete sym.accountMap
      (by simp [State.consumeStack, maxList] at hstack; omega)
    substate := concretizeSubstate concrete sym.substate
      (by simp [State.consumeStack, maxList] at hstack; omega)
    machineState := concretizeMachineState concrete sym.machineState
      (by simp [State.consumeStack, maxList] at hstack; omega)
    createdAccounts := addListToSet compare
      (concretizeExprList concrete sym.createdAccounts
        (by simp [State.consumeStack, maxList] at hstack; omega))
      concrete.createdAccounts id
  }

instance instBEqConcretizeType (τ : EType) : BEq (concretizeType τ) := by
  cases τ <;> simp [concretizeType] <;> infer_instance

def concretizeAssertion
    (concrete : Ethereum.State)
    (assert : Assertion)
    (hstack : assert.consumeStack ≤ concrete.machineState.stack.length) :
    Bool :=
  match assert with
  | .PEq a b =>
      let a' := concretizeExpr concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' := concretizeExpr concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' == b'
  | .PBool b => b
  | .PImpl a b =>
      let a' := concretizeAssertion concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' := concretizeAssertion concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      (not a') && b'
  | .PAnd a b =>
      let a' := concretizeAssertion concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' := concretizeAssertion concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' && b'
  | .POr a b =>
      let a' := concretizeAssertion concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' := concretizeAssertion concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' || b'
  | .PNeg n =>
      let n' := concretizeAssertion concrete n (by simp [Assertion.consumeStack] at hstack; exact hstack)
      not n'
  | .PLEq a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' ≤ b'
  | .PGEq a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' ≥ b'
  | .PLT a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' < b'
  | .PGT a b =>
      let a' : UInt256 := concretizeExpr concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' : UInt256 := concretizeExpr concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' > b'

  | .PLEqnat a b =>
      let a' : Nat := concretizeExpr concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' : Nat := concretizeExpr concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' ≤ b'
  | .PGEqnat a b =>
      let a' : Nat := concretizeExpr concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' : Nat := concretizeExpr concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' ≥ b'
  | .PLTnat a b =>
      let a' : Nat := concretizeExpr concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' : Nat := concretizeExpr concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' < b'
  | .PGTnat a b =>
      let a' : Nat := concretizeExpr concrete a (by simp [Assertion.consumeStack] at hstack; exact hstack.left)
      let b' : Nat := concretizeExpr concrete b (by simp [Assertion.consumeStack] at hstack; exact hstack.right)
      a' > b'


def checkCondition
    {consumes binds : Nat}
    (concrete : Ethereum.State)
    (cond : Condition consumes binds)
    (hstack : consumes ≤ concrete.machineState.stack.length) :
    Except ExecutionException (PLift <| binds ≤ concrete.machineState.stack.length) :=
  match cond with
  | .assert assertion (.exception e) =>
      if h : concretizeAssertion concrete assertion.1
        (by
          simp [ConsumingAssertion] at assertion
          suffices assertion.1.consumeStack = consumes by
            rw [this]; assumption
          obtain ⟨a',ha⟩ := assertion
          simp; symm;
          assumption
        )
      then .ok ⟨by simp⟩
      else throw e
  | .stackGE n =>
      if h : concrete.machineState.stack.length < n then throw .StackUnderflow
      else .ok ⟨Nat.le_of_not_lt h⟩
  | .stackLT n =>
      if concrete.machineState.stack.length ≥ n then throw .StackOverflow
      else .ok ⟨hstack⟩

def checkConditions
    {n : Nat}
    (concrete : Ethereum.State)
    (conds : ConditionChain n) :
    Except ExecutionException (PLift <| n ≤ concrete.machineState.stack.length) :=
  match conds with
  | .nil cond => checkCondition concrete cond (by simp)
  | .cons tail sufficientBindings hmax cond => do
      let ⟨condsProofs⟩ ← checkConditions concrete tail 
      let ⟨condProof⟩ ← checkCondition concrete cond (by
        exact (Nat.le_trans sufficientBindings condsProofs))
      .ok ⟨by rw [hmax, Nat.max_def]
              split 
              · exact condsProofs
              · exact condProof⟩

def concretizeSym (concrete : Ethereum.State) (sym : SymState) : Except ExecutionException (Ethereum.State × Option (Bool × ByteArray)):= do
  -- let uninterps := sym.calls.foldl (concretizeUninterp concrete) []
  let ⟨conds_bindings_proofs⟩ ← checkConditions concrete sym.conditions
  let bindings_sufficient : sym.evm.consumeStack ≤ sym.n := by
    apply le_trans sym.hevm (by rfl)
  Except.ok <| (concretizeState concrete sym.evm (le_trans bindings_sufficient conds_bindings_proofs), .none)
    -- TODO: do something about returnvalues as well


def models (syms : SymState) (s : Except ExecutionException (Ethereum.State × Option (Bool × ByteArray))) : Prop :=
  ∃ concrete, concretizeSym concrete syms = s

lemma if_concretizeOk_then_state {concrete : Ethereum.State} {symstate : SymState} {state : Ethereum.State} {o : Option (Bool × ByteArray)} :
  concretizeSym concrete symstate = .ok (state, o) 
  → ∃ hs, concretizeState concrete symstate.evm hs = state := by
    intro h
    simp [concretizeSym, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i _ hproofLifted h_checkConds_ok
      simp at h
      exact ⟨le_trans symstate.hevm hproofLifted.1, h.1⟩

lemma if_checkCondsOk_then_checkCondOk {n} {conds : ConditionChain n} {consumes binds} {concrete : Ethereum.State}
  {hs : PLift (n ≤ List.length concrete.machineState.stack)} :
  (checkConditions concrete conds).isOk = true →
  ∀ (c : Condition consumes binds) hs, InChain c conds → (checkCondition concrete c hs).isOk = true := by
    intro h -- c hs hin
    induction conds with
    | nil =>
      simp [checkConditions] at h
      intros _ _ hin
      cases hin
    | cons c_tail h_bindings h_max c_head ih =>
       intro c hs hin  
       simp [checkConditions, bind, Except.bind] at h
       split at h
       · simp [Except.isOk, Except.toBool] at h
       · cases hin' : hin
         · split at h
           · simp [Except.isOk,Except.toBool] at h
           · rename_i heq; simp [heq,Except.isOk,Except.toBool]
         · apply ih
           · assumption
           · rename_i heq _ _ _ ; simp [heq,Except.isOk,Except.toBool]
           · assumption

lemma if_concretizeOk_then_noexcept {consumes binds} {concrete : Ethereum.State} {symstate : SymState} {state : Ethereum.State} {o : Option (Bool × ByteArray)} :
  concretizeSym concrete symstate = .ok (state, o) 
  → ∀ (c : Condition consumes binds) hs, InChain c symstate.conditions → (checkCondition concrete c hs).isOk = true := by
    intro h
    simp [concretizeSym, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i hcondsOk
      have hcondsIsOk : ((checkConditions concrete symstate.conditions).isOk = true) := by
        simp [Except.isOk, Except.toBool, hcondsOk]
      apply if_checkCondsOk_then_checkCondOk hcondsIsOk
      assumption
      

lemma if_noexcept_then_concrete_state {A} {sinit : A} {concrete : Ethereum.State} {symstate : SymState} {consumes state binds o h} :  ∀ (l : List (Assertion × Failure)),
  (∀ (c : Condition consumes binds) hs, InChain c symstate.conditions → (checkCondition concrete c hs).isOk = true) →
  concretizeState concrete symstate.evm h = state →
  concretizeSym concrete symstate = .ok ⟨state, o⟩
  := by
    sorry
