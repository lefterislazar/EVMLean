/-!
# Finite fields

Prime fields `𝔽ₚ` and their quadratic extensions `𝔽ₚ[i]/(i² + 1)`, used by the
elliptic-curve primitives (secp256k1, secp256r1, alt_bn128 and BLS12-381).

Elements are natural numbers kept reduced modulo `p`; arithmetic on them is
GMP arithmetic on `Nat` in compiled code. The modulus is a type parameter, so
each curve has its own field type.
-/

namespace Ethereum.Crypto

/-- `b ^ e mod m`, by square-and-multiply. -/
def powMod (b e m : Nat) : Nat := Id.run do
  let mut result := 1 % m
  let mut base := b % m
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then result := result * base % m
    base := base * base % m
    e := e / 2
  return result

/-- The inverse of `a` modulo `m`, by the extended Euclidean algorithm, or `0`
    when `a` is not invertible. -/
def invMod (a m : Nat) : Nat := Id.run do
  let mut r₀ : Int := m
  let mut r₁ : Int := a % m
  let mut t₀ : Int := 0
  let mut t₁ : Int := 1
  while r₁ != 0 do
    let q := r₀ / r₁
    (r₀, r₁) := (r₁, r₀ - q * r₁)
    (t₀, t₁) := (t₁, t₀ - q * t₁)
  if r₀ != 1 then return 0
  return (t₀ % m).toNat

/-- The operations of a field, for the curve arithmetic that is generic in
    the field of coordinates. -/
class FieldOps (F : Type) extends Add F, Sub F, Mul F, Neg F, BEq F, Inhabited F where
  zero : F
  one : F
  /-- The multiplicative inverse; `0` for `0`. -/
  inv : F → F
  ofNat : Nat → F

namespace FieldOps

variable {F : Type} [FieldOps F]

def isZero (x : F) : Bool := x == zero

def sq (x : F) : F := x * x

def pow (x : F) (e : Nat) : F := Id.run do
  let mut result := one
  let mut base := x
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then result := result * base
    base := base * base
    e := e / 2
  return result

def div (x y : F) : F := x * inv y

end FieldOps

/-- The prime field `𝔽ₚ`. The value is kept below `p`. -/
structure Fp (p : Nat) where
  val : Nat
deriving Inhabited, Repr

namespace Fp

variable {p : Nat}

def ofNat (n : Nat) : Fp p := ⟨n % p⟩

instance : FieldOps (Fp p) where
  add a b := ⟨(a.val + b.val) % p⟩
  sub a b := ⟨(a.val + p - b.val) % p⟩
  mul a b := ⟨a.val * b.val % p⟩
  neg a := ⟨(p - a.val) % p⟩
  beq a b := a.val == b.val
  default := ⟨0⟩
  zero := ⟨0⟩
  one := ⟨1 % p⟩
  inv a := ⟨invMod a.val p⟩
  ofNat := ofNat

/-- The `sgn0` of RFC 9380: the parity of the canonical representative. -/
def sgn0 (a : Fp p) : Bool := a.val % 2 == 1

/-- Whether `a` is a square, by Euler's criterion (`p` an odd prime). -/
def isSquare (a : Fp p) : Bool :=
  a.val == 0 || powMod a.val ((p - 1) / 2) p == 1

/-- A square root of `a`, for `p ≡ 3 (mod 4)`, or `none` when `a` is not a
    square. -/
def sqrt? (a : Fp p) : Option (Fp p) :=
  let r : Fp p := ⟨powMod a.val ((p + 1) / 4) p⟩
  if r * r == a then some r else none

end Fp

/-- The quadratic extension `𝔽ₚ[i]/(i² + 1)`, for `p ≡ 3 (mod 4)`; `re + im·i`. -/
structure Fp2 (p : Nat) where
  re : Fp p
  im : Fp p
deriving Inhabited, Repr

namespace Fp2

variable {p : Nat}

def ofNats (re im : Nat) : Fp2 p := ⟨Fp.ofNat re, Fp.ofNat im⟩

def ofFp (a : Fp p) : Fp2 p := ⟨a, FieldOps.zero⟩

def conj (a : Fp2 p) : Fp2 p := ⟨a.re, -a.im⟩

/-- Multiplication by an element of the base field. -/
def scale (a : Fp2 p) (c : Fp p) : Fp2 p := ⟨a.re * c, a.im * c⟩

instance : FieldOps (Fp2 p) where
  add a b := ⟨a.re + b.re, a.im + b.im⟩
  sub a b := ⟨a.re - b.re, a.im - b.im⟩
  mul a b :=
    let t₀ := a.re * b.re
    let t₁ := a.im * b.im
    ⟨t₀ - t₁, (a.re + a.im) * (b.re + b.im) - t₀ - t₁⟩
  neg a := ⟨-a.re, -a.im⟩
  beq a b := a.re == b.re && a.im == b.im
  default := ⟨FieldOps.zero, FieldOps.zero⟩
  zero := ⟨FieldOps.zero, FieldOps.zero⟩
  one := ⟨FieldOps.one, FieldOps.zero⟩
  inv a :=
    let n := FieldOps.inv (a.re * a.re + a.im * a.im)
    ⟨a.re * n, -(a.im * n)⟩
  ofNat n := ⟨Fp.ofNat n, FieldOps.zero⟩

/-- The `sgn0` of RFC 9380 for `m = 2`. -/
def sgn0 (a : Fp2 p) : Bool :=
  a.re.sgn0 || (a.re.val == 0 && a.im.sgn0)

/--
A square root of `a`, or `none` when `a` is not a square: Algorithm 9 of
Adj and Rodríguez-Henríquez, "Square root computation over even extension
fields", for `p ≡ 3 (mod 4)`.
-/
def sqrt? (a : Fp2 p) : Option (Fp2 p) :=
  let a₁ := FieldOps.pow a ((p - 3) / 4)
  let α := a₁ * (a₁ * a)
  let x₀ := a₁ * a
  let minusOne : Fp2 p := -FieldOps.one
  let x :=
    if α == minusOne then (⟨FieldOps.zero, FieldOps.one⟩ : Fp2 p) * x₀
    else FieldOps.pow (FieldOps.one + α) ((p - 1) / 2) * x₀
  if x * x == a then some x else none

end Fp2

end Ethereum.Crypto
