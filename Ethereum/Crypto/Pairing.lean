import Ethereum.Crypto.Curve

/-!
# Pairing machinery for the BN and BLS12 curves

Both alt_bn128 and BLS12-381 have embedding degree 12 and a sextic twist. We
represent `𝔽ₚ¹²` as `𝔽ₚ²[w]/(w⁶ - ξ)`, a vector of six `𝔽ₚ²` coefficients,
where `ξ` is a quadratic and cubic non-residue of `𝔽ₚ²`.

The second pairing argument lives on the twist `E'(𝔽ₚ²)`. It is mapped into
`E(𝔽ₚ¹²)` by `(x, y) ↦ (x·w², y·w³)` for a D-type twist (alt_bn128) and by
`(x, y) ↦ (x/w², y/w³)` for an M-type twist (BLS12-381). The Miller loop
keeps its running point on the twist, in affine coordinates, and evaluates the
lines at the first argument directly as elements of `𝔽ₚ¹²`. Lines are only
computed up to factors in proper subfields of `𝔽ₚ¹²`, which the final
exponentiation sends to `1`.
-/

namespace Ethereum.Crypto

open FieldOps

/-- The non-residue `ξ` of a sextic tower over `𝔽ₚ²`, with the Frobenius
    coefficients `ξ^(i(p-1)/6)` for `i < 6`. -/
class SexticTower (p : Nat) where
  ξ : Fp2 p
  frobeniusCoeffs : Array (Fp2 p)

/-- The Frobenius coefficients `ξ^(i(p-1)/6)` for `i < 6`. -/
def SexticTower.coeffs {p : Nat} (ξ : Fp2 p) : Array (Fp2 p) :=
  let γ := pow ξ ((p - 1) / 6)
  (Array.range 6).map (pow γ ·)

/-- `𝔽ₚ¹² = 𝔽ₚ²[w]/(w⁶ - ξ)`: the coefficients of `1, w, …, w⁵`. -/
structure Fp12 (p : Nat) where
  c : Array (Fp2 p)
deriving Inhabited

namespace Fp12

variable {p : Nat} [SexticTower p]

def zero : Fp12 p := ⟨Array.replicate 6 FieldOps.zero⟩

def one : Fp12 p := ⟨#[FieldOps.one] ++ Array.replicate 5 FieldOps.zero⟩

/-- The element with the given nonzero coefficients. -/
def sparse (cs : List (Nat × Fp2 p)) : Fp12 p :=
  ⟨cs.foldl (fun acc (i, x) => acc.set! i x) zero.c⟩

instance : BEq (Fp12 p) where
  beq a b := (List.range 6).all fun i => a.c[i]! == b.c[i]!

def mul (a b : Fp12 p) : Fp12 p := Id.run do
  let mut prod : Array (Fp2 p) := Array.replicate 11 FieldOps.zero
  for i in [0:6] do
    let aᵢ := a.c[i]!
    if !isZero aᵢ then
      for j in [0:6] do
        prod := prod.modify (i + j) (· + aᵢ * b.c[j]!)
  let ξ := SexticTower.ξ (p := p)
  return ⟨Array.ofFn (n := 6) fun k => prod[k]! + ξ * prod.getD (k.val + 6) FieldOps.zero⟩

instance : Mul (Fp12 p) := ⟨mul⟩

def pow (a : Fp12 p) (e : Nat) : Fp12 p := Id.run do
  let mut result := one
  for i in (List.range e.log2.succ).reverse do
    result := result * result
    if e.testBit i then result := result * a
  return result

/-- The conjugate over `𝔽ₚ⁶`, which is the `p⁶`-power Frobenius map: `w ↦ -w`. -/
def conj (a : Fp12 p) : Fp12 p :=
  ⟨a.c.mapIdx fun i x => if i % 2 == 1 then -x else x⟩

/-- The `p`-power Frobenius map: `∑ cᵢ wⁱ ↦ ∑ cᵢ^p · ξ^(i(p-1)/6) · wⁱ`. -/
def frobenius (a : Fp12 p) : Fp12 p :=
  ⟨a.c.mapIdx fun i x => x.conj * (SexticTower.frobeniusCoeffs (p := p))[i]!⟩

/-! `𝔽ₚ⁶ = 𝔽ₚ²[v]/(v³ - ξ)`, with `v = w²`, for the inverse in `𝔽ₚ¹²`. -/

private def mul6 (a b : Array (Fp2 p)) : Array (Fp2 p) :=
  let ξ := SexticTower.ξ (p := p)
  #[a[0]! * b[0]! + ξ * (a[1]! * b[2]! + a[2]! * b[1]!),
    a[0]! * b[1]! + a[1]! * b[0]! + ξ * (a[2]! * b[2]!),
    a[0]! * b[2]! + a[1]! * b[1]! + a[2]! * b[0]!]

private def inv6 (a : Array (Fp2 p)) : Array (Fp2 p) :=
  let ξ := SexticTower.ξ (p := p)
  let c₀ := a[0]! * a[0]! - ξ * (a[1]! * a[2]!)
  let c₁ := ξ * (a[2]! * a[2]!) - a[0]! * a[1]!
  let c₂ := a[1]! * a[1]! - a[0]! * a[2]!
  let t := FieldOps.inv (a[0]! * c₀ + ξ * (a[2]! * c₁ + a[1]! * c₂))
  #[c₀ * t, c₁ * t, c₂ * t]

/-- The inverse: writing `a = A + w·B` with `A, B ∈ 𝔽ₚ⁶`,
    `a⁻¹ = (A - w·B) / (A² - v·B²)`. -/
def inv (a : Fp12 p) : Fp12 p :=
  let A := #[a.c[0]!, a.c[2]!, a.c[4]!]
  let B := #[a.c[1]!, a.c[3]!, a.c[5]!]
  let ξ := SexticTower.ξ (p := p)
  let AA := mul6 A A
  let BB := mul6 B B
  -- v·(b₀ + b₁v + b₂v²) = ξb₂ + b₀v + b₁v²
  let D := #[AA[0]! - ξ * BB[2]!, AA[1]! - BB[0]!, AA[2]! - BB[1]!]
  let Dinv := inv6 D
  let A' := mul6 A Dinv
  let B' := mul6 B Dinv
  ⟨#[A'[0]!, -B'[0]!, A'[1]!, -B'[1]!, A'[2]!, -B'[2]!]⟩

/--
The final exponentiation `f^((p¹² - 1)/r)`, given the hard part
`(p⁴ - p² + 1)/r` of the exponent: the easy part `(p⁶ - 1)(p² + 1)` uses the
conjugate and the Frobenius map.
-/
def finalExponentiation (hardExponent : Nat) (f : Fp12 p) : Fp12 p :=
  let f₁ := f.conj * f.inv
  let f₂ := f₁.frobenius.frobenius * f₁
  f₂.pow hardExponent

end Fp12

/-- The two kinds of sextic twist. -/
inductive TwistType
  /-- `E' : y² = x³ + b/ξ`, untwisted by `(x, y) ↦ (x·w², y·w³)`. -/
  | D
  /-- `E' : y² = x³ + b·ξ`, untwisted by `(x, y) ↦ (x/w², y/w³)`. -/
  | M

namespace Miller

variable {p : Nat} [SexticTower p]

/-- A point of the twist in affine coordinates, or `none` at infinity. -/
abbrev TwistPoint (p : Nat) := Option (Fp2 p × Fp2 p)

/--
The line with slope `λ` (on the twist) through the twist point `(x, y)`,
evaluated at `(xP, yP)` and scaled by a subfield factor.
-/
def line (tw : TwistType) (m x y : Fp2 p) (xP yP : Fp p) : Fp12 p :=
  let c := m * x - y
  match tw with
  | .D => Fp12.sparse [(0, Fp2.ofFp yP), (1, -(m.scale xP)), (3, c)]
  | .M => Fp12.sparse [(0, c), (2, -(m.scale xP)), (3, Fp2.ofFp yP)]

/-- The vertical line through the twist point with abscissa `x`, evaluated at
    `xP` and scaled by a subfield factor. -/
def vertical (tw : TwistType) (x : Fp2 p) (xP : Fp p) : Fp12 p :=
  match tw with
  | .D => Fp12.sparse [(0, Fp2.ofFp xP), (2, -x)]
  | .M => Fp12.sparse [(0, -x), (2, Fp2.ofFp xP)]

/-- Double `T`, returning the tangent line at `T` evaluated at `P`. -/
def double (tw : TwistType) (T : TwistPoint p) (xP yP : Fp p) : Fp12 p × TwistPoint p :=
  match T with
  | none => (Fp12.one, none)
  | some (x, y) =>
    if isZero y then (vertical tw x xP, none)
    else
      let m := ofNat 3 * x * x * FieldOps.inv (ofNat 2 * y)
      let x₃ := m * m - x - x
      let y₃ := m * (x - x₃) - y
      (line tw m x y xP yP, some (x₃, y₃))

/-- Add `Q` to `T`, returning the line through `T` and `Q` evaluated at `P`. -/
def add (tw : TwistType) (T Q : TwistPoint p) (xP yP : Fp p) : Fp12 p × TwistPoint p :=
  match T, Q with
  | none, _ => (Fp12.one, Q)
  | _, none => (Fp12.one, T)
  | some (x₁, y₁), some (x₂, y₂) =>
    if x₁ == x₂ then
      if y₁ == y₂ then double tw T xP yP else (vertical tw x₁ xP, none)
    else
      let m := (y₂ - y₁) * FieldOps.inv (x₂ - x₁)
      let x₃ := m * m - x₁ - x₂
      let y₃ := m * (x₁ - x₃) - y₁
      (line tw m x₁ y₁ xP yP, some (x₃, y₃))

/-- The Miller loop `f_{n,Q}(P)` over the bits of `n`, with the final running
    point `n·Q`. -/
def loop (tw : TwistType) (n : Nat) (Q : Fp2 p × Fp2 p) (xP yP : Fp p) :
    Fp12 p × TwistPoint p := Id.run do
  let mut f := Fp12.one
  let mut T : TwistPoint p := some Q
  for i in (List.range n.log2).reverse do
    let (l, T') := double tw T xP yP
    f := f * f * l
    T := T'
    if n.testBit i then
      let (l, T') := add tw T (some Q) xP yP
      f := f * l
      T := T'
  return (f, T)

end Miller

end Ethereum.Crypto
