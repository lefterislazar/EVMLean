import Ethereum.Crypto.Bytes
import Ethereum.Crypto.Curve

/-!
# secp256r1 signature verification (EIP-7951)
-/

namespace Ethereum.Crypto.P256

def p : Nat := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- The order of the group. -/
def n : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

abbrev F := Fp p

def curve : Curve F :=
  ⟨-Fp.ofNat 3, Fp.ofNat 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b⟩

def G : Jac F :=
  Jac.ofAffine
    (Fp.ofNat 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296)
    (Fp.ofNat 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5)

/--
Whether `(r, s)` is a valid signature of the hash `h` under the public key
`(qx, qy)`. The key must be a curve point with canonical coordinates; the point
at infinity has no affine encoding and is never on the curve.
-/
def verify (h r s qx qy : Nat) : Bool := Id.run do
  if !(0 < r && r < n && 0 < s && s < n && qx < p && qy < p) then return false
  let qxF : F := Fp.ofNat qx
  let qyF : F := Fp.ofNat qy
  if !curve.onCurve qxF qyF then return false
  let w := invMod s n
  let u₁ := h % n * w % n
  let u₂ := r * w % n
  let R := curve.add (curve.mul G u₁) (curve.mul (Jac.ofAffine qxF qyF) u₂)
  match Jac.toAffine R with
  | none => return false
  | some (x, _) => return x.val % n == r

/-- `P256VERIFY`: the 160-byte input `h ‖ r ‖ s ‖ qx ‖ qy`. -/
def verifyInput (data : ByteArray) : Bool :=
  data.size == 160 &&
    verify (ofBytesBE (data.extract 0 32)) (ofBytesBE (data.extract 32 64))
      (ofBytesBE (data.extract 64 96)) (ofBytesBE (data.extract 96 128))
      (ofBytesBE (data.extract 128 160))

end Ethereum.Crypto.P256
