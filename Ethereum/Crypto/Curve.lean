import Ethereum.Crypto.Field

/-!
# Short Weierstrass curves

Points of `y² = x³ + a·x + b` over a field `F`, in Jacobian coordinates:
`(X, Y, Z)` stands for the affine point `(X/Z², Y/Z³)`, and `Z = 0` for the
point at infinity.
-/

namespace Ethereum.Crypto

open FieldOps

/-- The curve `y² = x³ + a·x + b`. -/
structure Curve (F : Type) where
  a : F
  b : F

/-- A point in Jacobian coordinates. -/
structure Jac (F : Type) where
  x : F
  y : F
  z : F
deriving Inhabited

namespace Jac

variable {F : Type} [FieldOps F]

def infinity : Jac F := ⟨one, one, zero⟩

def ofAffine (x y : F) : Jac F := ⟨x, y, one⟩

def isInfinity (P : Jac F) : Bool := isZero P.z

/-- The affine coordinates of `P`, or `none` for the point at infinity. -/
def toAffine (P : Jac F) : Option (F × F) :=
  if isZero P.z then none
  else
    let zi := inv P.z
    let zi2 := zi * zi
    some (P.x * zi2, P.y * zi2 * zi)

def neg (P : Jac F) : Jac F := ⟨P.x, -P.y, P.z⟩

/-- Whether two points are equal. -/
def eq (P Q : Jac F) : Bool :=
  match toAffine P, toAffine Q with
  | none, none => true
  | some (x₁, y₁), some (x₂, y₂) => x₁ == x₂ && y₁ == y₂
  | _, _ => false

end Jac

namespace Curve

variable {F : Type} [FieldOps F] (c : Curve F)

def onCurve (x y : F) : Bool := y * y == x * x * x + c.a * x + c.b

def double (P : Jac F) : Jac F :=
  if isZero P.z || isZero P.y then Jac.infinity
  else
    let xx := P.x * P.x
    let yy := P.y * P.y
    let zz := P.z * P.z
    let s := ofNat 4 * P.x * yy
    let m := ofNat 3 * xx + c.a * zz * zz
    let x₃ := m * m - s - s
    let y₃ := m * (s - x₃) - ofNat 8 * yy * yy
    ⟨x₃, y₃, ofNat 2 * P.y * P.z⟩

def add (P Q : Jac F) : Jac F :=
  if isZero P.z then Q
  else if isZero Q.z then P
  else
    let z₁z₁ := P.z * P.z
    let z₂z₂ := Q.z * Q.z
    let u₁ := P.x * z₂z₂
    let u₂ := Q.x * z₁z₁
    let s₁ := P.y * z₂z₂ * Q.z
    let s₂ := Q.y * z₁z₁ * P.z
    if u₁ == u₂ then
      if s₁ == s₂ then c.double P else Jac.infinity
    else
      let h := u₂ - u₁
      let r := s₂ - s₁
      let hh := h * h
      let hhh := hh * h
      let v := u₁ * hh
      let x₃ := r * r - hhh - v - v
      let y₃ := r * (v - x₃) - s₁ * hhh
      ⟨x₃, y₃, P.z * Q.z * h⟩

/-- `n·P`, by double-and-add from the most significant bit. -/
def mul (P : Jac F) (n : Nat) : Jac F := Id.run do
  let mut R := Jac.infinity
  for i in (List.range n.log2.succ).reverse do
    R := c.double R
    if n.testBit i then R := c.add R P
  return R

end Curve

end Ethereum.Crypto
