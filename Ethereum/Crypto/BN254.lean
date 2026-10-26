import Ethereum.Crypto.Bytes
import Ethereum.Crypto.Pairing

/-!
# alt_bn128

The curve operations of the `BN_ADD`, `BN_MUL` and `SNARKV` precompiles
(EIP-196, EIP-197).

- `E  : y² = x³ + 3` over `𝔽ₚ`, with the group `G₁` of order `r`;
- `E' : y² = x³ + 3/(9 + i)` over `𝔽ₚ²`, a D-type sextic twist, with `G₂`;
- `𝔽ₚ¹² = 𝔽ₚ²[w]/(w⁶ - (9 + i))`.

The pairing is the optimal ate pairing.
-/

namespace Ethereum.Crypto.BN254

open FieldOps

def p : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- The order of `G₁` and `G₂`. -/
def r : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617

abbrev F := Fp p
abbrev F2 := Fp2 p

def ξ : F2 := Fp2.ofNats 9 1

instance : SexticTower p where
  ξ := ξ
  frobeniusCoeffs := SexticTower.coeffs ξ

def g1Curve : Curve F := ⟨zero, Fp.ofNat 3⟩

def g2Curve : Curve F2 := ⟨zero, Fp2.ofNats 3 0 * FieldOps.inv ξ⟩

/-! ## The pairing -/

/-- The loop count `6x + 2` of the optimal ate pairing. -/
def ateLoopCount : Nat := 29793968203157093288

def hardExponent : Nat := (p ^ 4 - p ^ 2 + 1) / r

/-- The `p`-power Frobenius endomorphism on the twist:
    `(x, y) ↦ (x̄ · ξ^((p-1)/3), ȳ · ξ^((p-1)/2))`. -/
def frobenius (Q : F2 × F2) : F2 × F2 :=
  (Q.1.conj * pow ξ ((p - 1) / 3), Q.2.conj * pow ξ ((p - 1) / 2))

/-- The Miller loop of the optimal ate pairing, `f_{6x+2,Q}(P)` times the
    lines through `π(Q)` and `-π²(Q)`. -/
def millerLoop (Q : F2 × F2) (xP yP : F) : Fp12 p :=
  let (f, T) := Miller.loop .D ateLoopCount Q xP yP
  let Q₁ := frobenius Q
  let (x₂, y₂) := frobenius Q₁
  let (l₁, T) := Miller.add .D T (some Q₁) xP yP
  let (l₂, _) := Miller.add .D T (some (x₂, -y₂)) xP yP
  f * l₁ * l₂

/-- Whether `∏ e(Pᵢ, Qᵢ) = 1`. Pairs with a point at infinity contribute `1`. -/
def pairingCheck (pairs : List (Jac F × Jac F2)) : Bool :=
  let f := pairs.foldl (init := Fp12.one) fun f (P, Q) =>
    match Jac.toAffine P, Jac.toAffine Q with
    | some (xP, yP), some Q => f * millerLoop Q xP yP
    | _, _ => f
  Fp12.finalExponentiation hardExponent f == Fp12.one

/-! ## The precompiles -/

/-- A coordinate: a 32-byte big-endian number below `p`. -/
def decodeFp (d : ByteArray) : Option F := do
  let x := ofBytesBE d
  guard (x < p)
  return Fp.ofNat x

/-- A point of `E` from its coordinates; `(0, 0)` is the point at infinity. -/
def decodeG1 (x y : ByteArray) : Option (Jac F) := do
  let x ← decodeFp x
  let y ← decodeFp y
  if isZero x && isZero y then return Jac.infinity
  guard (g1Curve.onCurve x y)
  return Jac.ofAffine x y

def encodeG1 (P : Jac F) : ByteArray :=
  match Jac.toAffine P with
  | none => ByteArray.mk (Array.replicate 64 0)
  | some (x, y) => toBytesBE x.val 32 ++ toBytesBE y.val 32

theorem encodeG1_size (P : Jac F) : (encodeG1 P).size = 64 := by
  unfold encodeG1
  split
  · exact Array.size_replicate ..
  · simp only [ByteArray.size_append, toBytesBE_size]

/-- `BN_ADD` on the coordinates of its two points. -/
def add (x₀ y₀ x₁ y₁ : ByteArray) : Option ByteArray :=
  encodeG1 <$> do return g1Curve.add (← decodeG1 x₀ y₀) (← decodeG1 x₁ y₁)

theorem add_size {x₀ y₀ x₁ y₁ o : ByteArray} (h : add x₀ y₀ x₁ y₁ = some o) : o.size = 64 :=
  map_eq_some_size encodeG1_size h

/-- `BN_MUL` on the coordinates of its point and its scalar. -/
def mul (x₀ y₀ n : ByteArray) : Option ByteArray :=
  encodeG1 <$> do return g1Curve.mul (← decodeG1 x₀ y₀) (ofBytesBE n)

theorem mul_size {x₀ y₀ n o : ByteArray} (h : mul x₀ y₀ n = some o) : o.size = 64 :=
  map_eq_some_size encodeG1_size h

/--
A point of `G₂`, encoded as `x.im ‖ x.re ‖ y.im ‖ y.re`; zero is the point at
infinity.
-/
def decodeG2 (d : ByteArray) : Option (Jac F2) := do
  let x : F2 := ⟨← decodeFp (d.extract 32 64), ← decodeFp (d.extract 0 32)⟩
  let y : F2 := ⟨← decodeFp (d.extract 96 128), ← decodeFp (d.extract 64 96)⟩
  if isZero x && isZero y then return Jac.infinity
  guard (g2Curve.onCurve x y)
  let Q := Jac.ofAffine x y
  guard (Jac.isInfinity (g2Curve.mul Q r))
  return Q

/-- `SNARKV`: the pairing check on a sequence of 192-byte pairs, as the
    32-byte word `1` or `0`. -/
def snarkv (data : ByteArray) : Option ByteArray :=
  (fun ok => toBytesBE (if ok then 1 else 0) 32) <$> do
    guard (data.size % 192 == 0)
    let pairs ← (List.range (data.size / 192)).mapM fun i => do
      let c := data.extract (192 * i) (192 * (i + 1))
      let P ← decodeG1 (c.extract 0 32) (c.extract 32 64)
      guard (Jac.isInfinity (g1Curve.mul P r))
      return (P, ← decodeG2 (c.extract 64 192))
    return pairingCheck pairs

theorem snarkv_size {data o : ByteArray} (h : snarkv data = some o) : o.size = 32 :=
  map_eq_some_size (fun _ => toBytesBE_size _ _) h

end Ethereum.Crypto.BN254
