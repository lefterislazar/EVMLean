import Ethereum.UInt256
import Ethereum.Wheels

namespace Ethereum
namespace Symbolic

/--
Type tags for the symbolic EVM expression language.

This mirrors hevm's phantom `EType` index: it keeps words, bytes, buffers,
storage, logs, addresses, contracts, and terminal execution results separated
while still letting them share one expression syntax.
-/
inductive EType where
  | buf
  | storage
  | stack
  | log
  | word
  | addr
  -- | contract
  | byte
  | num
  -- | end_
  deriving Repr, DecidableEq, Ord

-- /-- Variables introduced for globally shared symbolic arrays. -/
-- inductive GVar : EType → Type where
--   | bufVar : Nat → GVar .buf
--   | storeVar : Nat → GVar .storage
--   deriving Repr

mutual

  /-- Runtime bytecode, allowing symbolic bytes for code with symbolic pushdata. -/
  inductive RuntimeCode where
    | concrete : ByteArray → RuntimeCode
    | symbolic : Array (Expr .byte) → RuntimeCode

  /-- Contract code as used by creation/runtime EVM semantics. -/
  inductive ContractCode where
    | unknown : Expr .addr → ContractCode
    | init : ByteArray → Expr .buf → ContractCode
    | runtime : RuntimeCode → ContractCode

  /--
  An abstract representation of EVM terms, analogous to hevm's `Expr`.

  Memory, calldata, returndata, and bytecode slices are represented as `.buf`.
  Storage is represented as an expression tree over concrete or abstract base
  stores plus `SStore` updates. Writes retain their previous state locally, so an
  expression carries the context needed to interpret it.
  -/
  inductive Expr : EType → Type where
  -- identifiers
  | Lit : UInt256 → Expr .word
  | NatLit : Nat → Expr .num
  -- | Var : String → Expr .word
  -- | GVar {α : EType} : GVar α → Expr α

  -- bytes
  | LitByte : UInt8 → Expr .byte
              -- idx → val → ..
  | IndexWord : Expr .word → Expr .word → Expr .byte
  | EqByte : Expr .byte → Expr .byte → Expr .word
  -- | JoinBytes :
  --     Expr .byte → Expr .byte → Expr .byte → Expr .byte →
  --     Expr .byte → Expr .byte → Expr .byte → Expr .byte →
  --     Expr .byte → Expr .byte → Expr .byte → Expr .byte →
  --     Expr .byte → Expr .byte → Expr .byte → Expr .byte →
  --     Expr .byte → Expr .byte → Expr .byte → Expr .byte →
  --     Expr .byte → Expr .byte → Expr .byte → Expr .byte →
  --     Expr .byte → Expr .byte → Expr .byte → Expr .byte →
  --     Expr .byte → Expr .byte → Expr .byte → Expr .byte →
  --     Expr .word

  -- integers
  | Add : Expr .word → Expr .word → Expr .word
  | Sub : Expr .word → Expr .word → Expr .word
  | Mul : Expr .word → Expr .word → Expr .word
  | Div : Expr .word → Expr .word → Expr .word
  | SDiv : Expr .word → Expr .word → Expr .word
  | Mod : Expr .word → Expr .word → Expr .word
  | SMod : Expr .word → Expr .word → Expr .word
  | AddMod : Expr .word → Expr .word → Expr .word → Expr .word
  | MulMod : Expr .word → Expr .word → Expr .word → Expr .word
  | Exp : Expr .word → Expr .word → Expr .word
  | SEx : Expr .word → Expr .word → Expr .word
  | Min : Expr .word → Expr .word → Expr .word
  | Max : Expr .word → Expr .word → Expr .word

  -- word-valued predicates and path merging
  | LT : Expr .word → Expr .word → Expr .word
  | GT : Expr .word → Expr .word → Expr .word
  | LEq : Expr .word → Expr .word → Expr .word
  | GEq : Expr .word → Expr .word → Expr .word
  | SLT : Expr .word → Expr .word → Expr .word
  | SGT : Expr .word → Expr .word → Expr .word
  | Eq : Expr .word → Expr .word → Expr .word
  | IsZero : Expr .word → Expr .word
  | ITE : Expr .word → Expr .word → Expr .word → Expr .word

  -- bits
  | And : Expr .word → Expr .word → Expr .word
  | Or : Expr .word → Expr .word → Expr .word
  | Xor : Expr .word → Expr .word → Expr .word
  | Not : Expr .word → Expr .word
  | SHL : Expr .word → Expr .word → Expr .word
  | SHR : Expr .word → Expr .word → Expr .word
  | SAR : Expr .word → Expr .word → Expr .word
  | CLZ : Expr .word → Expr .word

  -- hashes
  | Keccak : Expr .buf → Expr .word

  -- block context
  | Origin : Expr .word
  | BlockHash : Expr .word → Expr .word
  | Coinbase : Expr .word
  | Timestamp : Expr .word
  | BlockNumber : Expr .word
  | PrevRandao : Expr .word
  | GasLimit : Expr .word
  | ChainId : Expr .word
  | BaseFee : Expr .word
  | BlobHash : Expr .word → Expr .word
  | BlobBaseFee : Expr .word

  -- transaction and frame context
  | Address : Expr .addr
  | Caller : Expr .addr
  | TxValue : Expr .word
  | GasPrice : Expr .word
  | Balance : Expr .addr → Expr .word
  | SelfBalance : Expr .word
  | Gas : String → Nat → Expr .word

  -- code
  | CodeSize : Expr .addr → Expr .word
  | CodeHash : Expr .addr → Expr .word

  -- logs
  | LogEntry : Expr .word → Expr .buf → List (Expr .word) → Expr .log

  -- contract summary
  -- | C :
  --     ContractCode →
  --     Expr .storage →
  --     Expr .storage →
  --     Expr .word →
  --     Option UInt256 →
  --     Expr .contract

  -- addresses
  | SymAddr : String → Expr .addr
  | LitAddr : AccountAddress → Expr .addr
  | AddrOfWord : Expr .word → Expr .addr
  | WAddr : Expr .addr → Expr .word

  -- storage
  | ConcreteStore : List (UInt256 × UInt256) → Expr .storage
  | AbstractStore :
      Expr .addr → ℕ → 
      Expr .storage
  | SLoad : Expr .word → Expr .storage → Expr .word
  | SStore : Expr .word → Expr .word → Expr .storage → Expr .storage

  -- stack
  -- Stack: List of known word expressions
  --              + depth of starting point of remaining abstract stack
  --                compared to original
  -- For example, pop increases Int of Abstract Stack
  --            if known list is empty
  | Stack : List (Expr .word) → ℕ → Expr .stack
  | StackItem : ℕ → Expr .word
  -- | StackSize : Expr .stack → Expr .num

  -- buffers
  | ConcreteBuf : ByteArray → Expr .buf
  --| AbstractBuf : String → Expr .buf
  | ReadWord : Expr .word → Expr .buf → Expr .word
  | ReadByte : Expr .word → Expr .buf → Expr .byte
  | WriteWord : Expr .word → Expr .word → Expr .buf → Expr .buf
  | WriteByte : Expr .word → Expr .byte → Expr .buf → Expr .buf
  | CopySlice :
      Expr .word →
      Expr .word →
      Expr .word →
      Expr .buf →
      Expr .buf →
      Expr .buf
  | BufLength : Expr .buf → Expr .word

  -- Uninterpreted call/create returns
  | RetBuf : Int → Expr .buf -- return buf of numbered call
  | CallSuccess : Expr .word -- return boolean of numbered call

  -- calldata buffer
  | CalldataBuf : Expr .buf

  -- control flow
  -- | Partial : List Assertion → String → Expr .end_
  -- | Failure : List Assertion → String → Expr .end_
  -- | Success : List Assertion → Expr .buf → List (Expr .addr × Expr .contract) → List (Expr .log) → Expr .end_

  -- GAS
  | toNat : Expr .word → Expr .num
  | ofNat : Expr .num → Expr .word
  | SubNat : Expr .num → Expr .num → Expr .num
  | M : Expr .word → Expr .word → Expr .word → Expr .num
  | Cₘ : Expr .num → Expr .num
  | Csstore : Expr .word -- new value
            → Expr .word -- existing value
            → Expr .word -- storage address
            → List (Expr .word) -- accessedKeys
            → Expr .num
  | Cexp : Expr .word → Expr .num
  | CwordCost : Nat → Nat → Expr .word → Expr .num
  | Caccess : Expr .addr → List (Expr .addr) → Expr .num
  | Cselfdestruct : Expr .word → List (Expr .addr) → Expr .num
  | Csload : Expr .word → List (Expr .word) → Expr .num
  | Ccall :
      Expr .addr →
      Expr .addr →
      Expr .word →
      Expr .word →
      Expr .word →
      List (Expr .addr) →
      Expr .num
  | AddNat : Expr .num → Expr .num → Expr .num

  /-- The language of boolean facts asserted about symbolic expressions. -/
  inductive Assertion where
    | PEq {α : EType} : Expr α → Expr α → Assertion
    | PLT : Expr .word → Expr .word → Assertion
    | PGT : Expr .word → Expr .word → Assertion
    | PGEq : Expr .word → Expr .word → Assertion
    | PLEq : Expr .word → Expr .word → Assertion

    -- TODO: make a class?
    | PLTnat : Expr .num → Expr .num → Assertion
    | PGTnat : Expr .num → Expr .num → Assertion
    | PGEqnat : Expr .num → Expr .num → Assertion
    | PLEqnat : Expr .num → Expr .num → Assertion

    | PNeg : Assertion → Assertion
    | PAnd : Assertion → Assertion → Assertion
    | POr : Assertion → Assertion → Assertion
    | PImpl : Assertion → Assertion → Assertion
    | PBool : Bool → Assertion

end

deriving instance BEq for RuntimeCode
deriving instance BEq for ContractCode
deriving instance BEq for Expr
deriving instance BEq for Assertion

namespace Expr

abbrev Word := Expr .word
abbrev Byte := Expr .byte
abbrev Buf := Expr .buf
abbrev Storage := Expr .storage
abbrev Addr := Expr .addr
-- abbrev Contract := Expr .contract
abbrev Log := Expr .log

def maxLit : UInt256 :=
  UInt256.ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def maxLitSigned : UInt256 :=
  UInt256.ofNat 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def minLitSigned : UInt256 :=
  UInt256.ofNat 0x8000000000000000000000000000000000000000000000000000000000000000

private def op1
    (symbolic : Word → Word)
    (concrete : UInt256 → UInt256)
    : Word → Word
  | .Lit x => .Lit (concrete x)
  | x => symbolic x

private def op2
    (symbolic : Word → Word → Word)
    (concrete : UInt256 → UInt256 → UInt256)
    : Word → Word → Word
  | .Lit x, .Lit y => .Lit (concrete x y)
  | x, y => symbolic x y

private def op3
    (symbolic : Word → Word → Word → Word)
    (concrete : UInt256 → UInt256 → UInt256 → UInt256)
    : Word → Word → Word → Word
  | .Lit x, .Lit y, .Lit z => .Lit (concrete x y z)
  | x, y, z => symbolic x y z

def add : Word → Word → Word := op2 .Add (· + ·)
def sub : Word → Word → Word := op2 .Sub (· - ·)
def mul : Word → Word → Word := op2 .Mul (· * ·)
def div : Word → Word → Word := op2 .Div (· / ·)
def sdiv : Word → Word → Word := op2 .SDiv UInt256.sdiv
def mod : Word → Word → Word := op2 .Mod (· % ·)
def smod : Word → Word → Word := op2 .SMod UInt256.smod

def addmod : Word → Word → Word → Word :=
  op3 .AddMod fun x y n =>
    if n == UInt256.ofNat 0 then UInt256.ofNat 0 else UInt256.ofNat ((x.toNat + y.toNat) % n.toNat)

def mulmod : Word → Word → Word → Word :=
  op3 .MulMod fun x y n =>
    if n == UInt256.ofNat 0 then UInt256.ofNat 0 else UInt256.ofNat ((x.toNat * y.toNat) % n.toNat)

def exp : Word → Word → Word := op2 .Exp (· ^ ·)
def byte : Word → Word → Byte
  | .Lit idx, .Lit value => .LitByte (UInt8.ofNat (UInt256.byteAt idx value).toNat)
  | idx, value => .IndexWord idx value
def lt : Word → Word → Word := op2 .LT fun x y => Bool.toUInt256 (x < y)
def gt : Word → Word → Word := op2 .GT fun x y => Bool.toUInt256 (x > y)
def leq : Word → Word → Word := op2 .LEq fun x y => Bool.toUInt256 (x ≤ y)
def geq : Word → Word → Word := op2 .GEq fun x y => Bool.toUInt256 (x ≥ y)
def slt : Word → Word → Word := op2 .SLT UInt256.slt
def sgt : Word → Word → Word := op2 .SGT UInt256.sgt
def eq : Word → Word → Word := op2 .Eq fun x y => Bool.toUInt256 (x == y)
def iszero : Word → Word := op1 .IsZero fun x => Bool.toUInt256 (x == UInt256.ofNat 0)
def and : Word → Word → Word := op2 .And (· &&& ·)
def or : Word → Word → Word := op2 .Or (· ||| ·)
def xor : Word → Word → Word := op2 .Xor (· ^^^ ·)
def not : Word → Word := op1 .Not Complement.complement
def shl : Word → Word → Word := op2 .SHL fun shift value => value <<< shift
def shr : Word → Word → Word := op2 .SHR fun shift value => value >>> shift
def sar : Word → Word → Word := op2 .SAR UInt256.sar

def bool : Bool → Word
  | true => .Lit (UInt256.ofNat 1)
  | false => .Lit (UInt256.ofNat 0)

def peq {α : EType} (x y : Expr α) : Assertion :=
  .PEq x y

def pand : List Assertion → Assertion :=
  List.foldl .PAnd (.PBool true)

def por : List Assertion → Assertion :=
  List.foldl .POr (.PBool false)

infixr:35 " .&& " => Assertion.PAnd
infixr:30 " .|| " => Assertion.POr
infix:50 " .== " => peq
infix:50 " ./= " => fun x y => Assertion.PNeg (peq x y)
infix:50 " .< " => Assertion.PLT
infix:50 " .<= " => Assertion.PLEq
infix:50 " .> " => Assertion.PGT
infix:50 " .>= " => Assertion.PGEq

mutual
def consumeStack {τ} : Expr τ → Nat
  | .Lit _ => 0
  | .NatLit _ => 0
  | .LitByte _ => 0
  | .IndexWord w i => max (consumeStack w) (consumeStack i)
  | .EqByte a b => max (consumeStack a) (consumeStack b)
  | .Add a b => max (consumeStack a) (consumeStack b)
  | .Sub a b => max (consumeStack a) (consumeStack b)
  | .Mul a b => max (consumeStack a) (consumeStack b)
  | .Div a b => max (consumeStack a) (consumeStack b)
  | .SDiv a b => max (consumeStack a) (consumeStack b)
  | .Mod a b => max (consumeStack a) (consumeStack b)
  | .SMod a b => max (consumeStack a) (consumeStack b)
  | .AddMod a b c => max (consumeStack a) (max (consumeStack b) (consumeStack c))
  | .MulMod a b c => max (consumeStack a) (max (consumeStack b) (consumeStack c))
  | .Exp a b => max (consumeStack a) (consumeStack b)
  | .SEx a b => max (consumeStack a) (consumeStack b)
  | .Min a b => max (consumeStack a) (consumeStack b)
  | .Max a b => max (consumeStack a) (consumeStack b)
  | .LT a b => max (consumeStack a) (consumeStack b)
  | .GT a b => max (consumeStack a) (consumeStack b)
  | .LEq a b => max (consumeStack a) (consumeStack b)
  | .GEq a b => max (consumeStack a) (consumeStack b)
  | .SLT a b => max (consumeStack a) (consumeStack b)
  | .SGT a b => max (consumeStack a) (consumeStack b)
  | .Eq a b => max (consumeStack a) (consumeStack b)
  | .IsZero a => consumeStack a
  | .ITE c a b => max (consumeStack c) (max (consumeStack a) (consumeStack b))
  | .And a b => max (consumeStack a) (consumeStack b)
  | .Or a b => max (consumeStack a) (consumeStack b)
  | .Xor a b => max (consumeStack a) (consumeStack b)
  | .Not a => consumeStack a
  | .SHL a b => max (consumeStack a) (consumeStack b)
  | .SHR a b => max (consumeStack a) (consumeStack b)
  | .SAR a b => max (consumeStack a) (consumeStack b)
  | .CLZ a => consumeStack a
  | .Keccak b => consumeStack b
  | .Origin => 0
  | .BlockHash a => consumeStack a
  | .Coinbase => 0
  | .Timestamp => 0
  | .BlockNumber => 0
  | .PrevRandao => 0
  | .GasLimit => 0
  | .ChainId => 0
  | .BaseFee => 0
  | .BlobHash a => consumeStack a
  | .BlobBaseFee => 0
  | .Address => 0
  | .Caller => 0
  | .TxValue => 0
  | .GasPrice => 0
  | .Balance a => consumeStack a
  | .SelfBalance => 0
  | .Gas _ _ => 0
  | .CodeSize a => consumeStack a
  | .CodeHash a => consumeStack a
  | .LogEntry a b topics => max (consumeStack a) (max (consumeStack b) (maxConsumesStackList topics))
  | .SymAddr _ => 0
  | .LitAddr _ => 0
  | .AddrOfWord a => consumeStack a
  | .WAddr a => consumeStack a
  | .ConcreteStore _ => 0
  | .AbstractStore a _ => consumeStack a
  | .SLoad a s => max (consumeStack a) (consumeStack s)
  | .SStore a b s => max (consumeStack a) (max (consumeStack b) (consumeStack s))
  | .Stack known _ => maxConsumesStackList known
  | .StackItem n => n + 1
  | .ConcreteBuf _ => 0
  | .ReadWord a b => max (consumeStack a) (consumeStack b)
  | .ReadByte a b => max (consumeStack a) (consumeStack b)
  | .WriteWord a b c => max (consumeStack a) (max (consumeStack b) (consumeStack c))
  | .WriteByte a b c => max (consumeStack a) (max (consumeStack b) (consumeStack c))
  | .CopySlice a b c src dst =>
      max (consumeStack a)
        (max (consumeStack b)
          (max (consumeStack c) (max (consumeStack src) (consumeStack dst))))
  | .BufLength b => consumeStack b
  | .RetBuf _ => 0
  | .CallSuccess => 0
  | .CalldataBuf => 0
  | .toNat a => consumeStack a
  | .ofNat a => consumeStack a
  | .SubNat a b => max (consumeStack a) (consumeStack b)
  | .M a b c => max (consumeStack a) (max (consumeStack b) (consumeStack c))
  | .Cₘ a => consumeStack a
  | .Csstore a b c d => max (consumeStack a) (max (consumeStack b) (max (consumeStack c) (maxConsumesStackList d)))
  | .Cexp a => consumeStack a
  | .CwordCost _ _ a => consumeStack a
  | .Caccess a accessedAccounts => max (consumeStack a) (maxConsumesStackList accessedAccounts)
  | .Cselfdestruct a accessedAccounts => max (consumeStack a) (maxConsumesStackList accessedAccounts)
  | .Csload a accessedStorageKeys => max (consumeStack a) (maxConsumesStackList accessedStorageKeys)
  | .Ccall target recipient value gas gasAvailable accessedAccounts =>
      max (consumeStack target)
        (max (consumeStack recipient)
          (max (consumeStack value)
            (max (consumeStack gas)
              (max (consumeStack gasAvailable) (maxConsumesStackList accessedAccounts)))))
  | .AddNat a b => max (consumeStack a) (consumeStack b)

def maxConsumesStackList {τ}: List (Expr τ) → Nat
    | [] => 0
    | x :: xs => max (consumeStack x) (maxConsumesStackList xs)
end

@[simp] theorem consumeStack_addrOfWord (a : Expr .word) :
    consumeStack (AddrOfWord a) = consumeStack a := by
  rw [consumeStack.eq_60]

@[simp] theorem consumeStack_cexp (a : Expr .word) :
    consumeStack (Cexp a) = consumeStack a := by
  rw [consumeStack.eq_84]

@[simp] theorem consumeStack_cwordCost (base wordCost : Nat) (a : Expr .word) :
    consumeStack (CwordCost base wordCost a) = consumeStack a := by
  rw [consumeStack.eq_85]

@[simp] theorem consumeStack_caccess (a : Expr .addr) (accessedAccounts : List (Expr .addr)) :
    consumeStack (Caccess a accessedAccounts) =
      max (consumeStack a) (maxConsumesStackList accessedAccounts) := by
  rw [consumeStack.eq_86]

@[simp] theorem consumeStack_cselfdestruct (a : Expr .word) (accessedAccounts : List (Expr .addr)) :
    consumeStack (Cselfdestruct a accessedAccounts) =
      max (consumeStack a) (maxConsumesStackList accessedAccounts) := by
  rw [consumeStack.eq_87]

@[simp] theorem consumeStack_csload (a : Expr .word) (accessedStorageKeys : List (Expr .word)) :
    consumeStack (Csload a accessedStorageKeys) =
      max (consumeStack a) (maxConsumesStackList accessedStorageKeys) := by
  rw [consumeStack.eq_88]

@[simp] theorem consumeStack_ccall
    (target recipient : Expr .addr)
    (value gas gasAvailable : Expr .word)
    (accessedAccounts : List (Expr .addr)) :
    consumeStack (Ccall target recipient value gas gasAvailable accessedAccounts) =
      max (consumeStack target)
        (max (consumeStack recipient)
          (max (consumeStack value)
            (max (consumeStack gas)
              (max (consumeStack gasAvailable) (maxConsumesStackList accessedAccounts))))) := by
  rw [consumeStack.eq_89]

@[simp] theorem consumeStack_addNat (a b : Expr .num) :
    consumeStack (AddNat a b) = max (consumeStack a) (consumeStack b) := by
  rw [consumeStack.eq_90]

end Expr

def Assertion.consumeStack : Assertion → Nat
  | .PEq a b => max (Expr.consumeStack a) (Expr.consumeStack b)
  | .PLT a b => max (Expr.consumeStack a) (Expr.consumeStack b)
  | .PGT a b => max (Expr.consumeStack a) (Expr.consumeStack b)
  | .PGEq a b => max (Expr.consumeStack a) (Expr.consumeStack b)
  | .PLEq a b => max (Expr.consumeStack a) (Expr.consumeStack b)
  | .PLTnat a b => max (Expr.consumeStack a) (Expr.consumeStack b)
  | .PGTnat a b => max (Expr.consumeStack a) (Expr.consumeStack b)
  | .PGEqnat a b => max (Expr.consumeStack a) (Expr.consumeStack b)
  | .PLEqnat a b => max (Expr.consumeStack a) (Expr.consumeStack b)
  | .PNeg a => a.consumeStack
  | .PAnd a b => max a.consumeStack b.consumeStack
  | .POr a b => max a.consumeStack b.consumeStack
  | .PImpl a b => max a.consumeStack b.consumeStack
  | .PBool _ => 0

end Symbolic
end Ethereum
