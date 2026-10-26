import Ethereum.Crypto.Bytes
import Ethereum.Crypto.Curve

/-!
# secp256k1 public-key recovery

ECDSA public-key recovery on secp256k1, with the conventions of
libsecp256k1's `ecdsa_recover`: the recovery id `v ∈ {0, 1, 2, 3}` selects the
parity of `R.y` (bit 0) and whether `R.x = r + n` (bit 1); `r` and `s` must lie
in `[1, n)`; the message hash is reduced modulo `n`.
-/

namespace Ethereum.Crypto.Secp256k1

def p : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- The order of the group. -/
def n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

abbrev F := Fp p

def curve : Curve F := ⟨Fp.ofNat 0, Fp.ofNat 7⟩

def G : Jac F :=
  Jac.ofAffine
    (Fp.ofNat 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)
    (Fp.ofNat 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)

/--
The public key `(x, y)` that signed the hash `e` with signature `(r, s)` and
recovery id `v`, or `none` when there is none.
-/
def recover (e r s v : Nat) : Option (Nat × Nat) := do
  guard (v < 4 && 0 < r && r < n && 0 < s && s < n)
  let x := if v ≥ 2 then r + n else r
  guard (x < p)
  let xF : F := Fp.ofNat x
  let y ← (xF * xF * xF + curve.b).sqrt?
  let y := if y.val % 2 == v % 2 then y else -y
  let R := Jac.ofAffine xF y
  let rInv := invMod r n
  let u₁ := (n - e % n) * rInv % n
  let u₂ := s * rInv % n
  let Q := curve.add (curve.mul G u₁) (curve.mul R u₂)
  let (qx, qy) ← Jac.toAffine Q
  return (qx.val, qy.val)

/--
`ECDSARECOVER` of the Yellow Paper: the 64-byte public key `x ‖ y` recovered
from the 32-byte hash `e`, the recovery id `v` and the signature `(r, s)`.
-/
def ecdsaRecover (e v r s : ByteArray) : Except String ByteArray :=
  match recover (ofBytesBE e) (ofBytesBE r) (ofBytesBE s) (ofBytesBE v) with
  | some (x, y) => .ok (toBytesBE x 32 ++ toBytesBE y 32)
  | none => .error "ECDSARECOVER failed"

end Ethereum.Crypto.Secp256k1
