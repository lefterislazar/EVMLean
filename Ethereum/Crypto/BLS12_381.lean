import Ethereum.Crypto.Bytes
import Ethereum.Crypto.Pairing
import Ethereum.Crypto.SHA256

/-!
# BLS12-381

The curve operations of the EIP-2537 precompiles (Prague) and the KZG
point-evaluation precompile of EIP-4844.

- `E  : y² = x³ + 4` over `𝔽ₚ`, with the group `G₁` of order `r`;
- `E' : y² = x³ + 4(1 + i)` over `𝔽ₚ²`, an M-type sextic twist, with `G₂`;
- `𝔽ₚ¹² = 𝔽ₚ²[w]/(w⁶ - (1 + i))`.

The hash-to-curve maps follow RFC 9380: the simplified SWU map to a curve
isogenous to `E` (resp. `E'`), the 11-isogeny (resp. 3-isogeny) to `E`
(resp. `E'`), and cofactor clearing by multiplication with `h_eff`. The
isogeny coefficients are those of RFC 9380, Appendices E.2 and E.3.
-/

namespace Ethereum.Crypto.BLS12_381

open FieldOps

def p : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- The order of `G₁` and `G₂`. -/
def r : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

abbrev F := Fp p
abbrev F2 := Fp2 p

instance : SexticTower p where
  ξ := Fp2.ofNats 1 1
  frobeniusCoeffs := SexticTower.coeffs (Fp2.ofNats 1 1)

def g1Curve : Curve F := ⟨zero, Fp.ofNat 4⟩

def g2Curve : Curve F2 := ⟨zero, Fp2.ofNats 4 4⟩

def G1 : Jac F :=
  Jac.ofAffine
    (Fp.ofNat 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
    (Fp.ofNat 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)

def G2 : Jac F2 :=
  Jac.ofAffine
    (Fp2.ofNats
      0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8
      0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
    (Fp2.ofNats
      0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801
      0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)

/-! ## The pairing -/

/-- `|x|` for the curve parameter `x = -0xd201000000010000`. -/
def xAbs : Nat := 0xd201000000010000

def hardExponent : Nat := (p ^ 4 - p ^ 2 + 1) / r

/--
Whether `∏ e(Pᵢ, Qᵢ) = 1`. The Miller loop runs over `|x|` without the
final conjugation for the sign of `x`, which inverts every pairing value and
so does not change the check. Pairs with a point at infinity contribute `1`.
-/
def pairingCheck (pairs : List (Jac F × Jac F2)) : Bool :=
  let f := pairs.foldl (init := Fp12.one) fun f (P, Q) =>
    match Jac.toAffine P, Jac.toAffine Q with
    | some (xP, yP), some Q => f * (Miller.loop .M xAbs Q xP yP).1
    | _, _ => f
  Fp12.finalExponentiation hardExponent f == Fp12.one

/-! ## Encodings (EIP-2537) -/

/-- A field element: 64 big-endian bytes, the top 16 zero, below `p`. -/
def decodeFp (d : ByteArray) : Option F := do
  guard (d.size == 64 && (d.extract 0 16).data.all (· == 0))
  let x := ofBytesBE d
  guard (x < p)
  return Fp.ofNat x

/-- A point of `G₁` (or `E` if `subgroup` is false); `(0, 0)` is the point at
    infinity. -/
def decodeG1 (d : ByteArray) (subgroup : Bool) : Option (Jac F) := do
  guard (d.size == 128)
  let x ← decodeFp (d.extract 0 64)
  let y ← decodeFp (d.extract 64 128)
  if isZero x && isZero y then return Jac.infinity
  guard (g1Curve.onCurve x y)
  let P := Jac.ofAffine x y
  guard (!subgroup || Jac.isInfinity (g1Curve.mul P r))
  return P

/-- A point of `G₂` (or `E'` if `subgroup` is false), encoded as
    `x.re ‖ x.im ‖ y.re ‖ y.im`; `(0, 0)` is the point at infinity. -/
def decodeG2 (d : ByteArray) (subgroup : Bool) : Option (Jac F2) := do
  guard (d.size == 256)
  let x : F2 := ⟨← decodeFp (d.extract 0 64), ← decodeFp (d.extract 64 128)⟩
  let y : F2 := ⟨← decodeFp (d.extract 128 192), ← decodeFp (d.extract 192 256)⟩
  if isZero x && isZero y then return Jac.infinity
  guard (g2Curve.onCurve x y)
  let Q := Jac.ofAffine x y
  guard (!subgroup || Jac.isInfinity (g2Curve.mul Q r))
  return Q

def encodeFp (x : F) : ByteArray := toBytesBE x.val 64

def encodeG1 (P : Jac F) : ByteArray :=
  match Jac.toAffine P with
  | none => ByteArray.mk (Array.replicate 128 0)
  | some (x, y) => encodeFp x ++ encodeFp y

def encodeG2 (Q : Jac F2) : ByteArray :=
  match Jac.toAffine Q with
  | none => ByteArray.mk (Array.replicate 256 0)
  | some (x, y) => encodeFp x.re ++ encodeFp x.im ++ encodeFp y.re ++ encodeFp y.im

theorem encodeG1_size (P : Jac F) : (encodeG1 P).size = 128 := by
  unfold encodeG1
  split
  · exact Array.size_replicate ..
  · simp only [encodeFp, ByteArray.size_append, toBytesBE_size]

theorem encodeG2_size (Q : Jac F2) : (encodeG2 Q).size = 256 := by
  unfold encodeG2
  split
  · exact Array.size_replicate ..
  · simp only [encodeFp, ByteArray.size_append, toBytesBE_size]

/-! ## Hashing to the curve (RFC 9380) -/

private def iso11XNum : Array F := #[
  Fp.ofNat 0x11a05f2b1e833340b809101dd99815856b303e88a2d7005ff2627b56cdb4e2c85610c2d5f2e62d6eaeac1662734649b7,
  Fp.ofNat 0x17294ed3e943ab2f0588bab22147a81c7c17e75b2f6a8417f565e33c70d1e86b4838f2a6f318c356e834eef1b3cb83bb,
  Fp.ofNat 0xd54005db97678ec1d1048c5d10a9a1bce032473295983e56878e501ec68e25c958c3e3d2a09729fe0179f9dac9edcb0,
  Fp.ofNat 0x1778e7166fcc6db74e0609d307e55412d7f5e4656a8dbf25f1b33289f1b330835336e25ce3107193c5b388641d9b6861,
  Fp.ofNat 0xe99726a3199f4436642b4b3e4118e5499db995a1257fb3f086eeb65982fac18985a286f301e77c451154ce9ac8895d9,
  Fp.ofNat 0x1630c3250d7313ff01d1201bf7a74ab5db3cb17dd952799b9ed3ab9097e68f90a0870d2dcae73d19cd13c1c66f652983,
  Fp.ofNat 0xd6ed6553fe44d296a3726c38ae652bfb11586264f0f8ce19008e218f9c86b2a8da25128c1052ecaddd7f225a139ed84,
  Fp.ofNat 0x17b81e7701abdbe2e8743884d1117e53356de5ab275b4db1a682c62ef0f2753339b7c8f8c8f475af9ccb5618e3f0c88e,
  Fp.ofNat 0x80d3cf1f9a78fc47b90b33563be990dc43b756ce79f5574a2c596c928c5d1de4fa295f296b74e956d71986a8497e317,
  Fp.ofNat 0x169b1f8e1bcfa7c42e0c37515d138f22dd2ecb803a0c5c99676314baf4bb1b7fa3190b2edc0327797f241067be390c9e,
  Fp.ofNat 0x10321da079ce07e272d8ec09d2565b0dfa7dccdde6787f96d50af36003b14866f69b771f8c285decca67df3f1605fb7b,
  Fp.ofNat 0x6e08c248e260e70bd1e962381edee3d31d79d7e22c837bc23c0bf1bc24c6b68c24b1b80b64d391fa9c8ba2e8ba2d229]

private def iso11XDen : Array F := #[
  Fp.ofNat 0x8ca8d548cff19ae18b2e62f4bd3fa6f01d5ef4ba35b48ba9c9588617fc8ac62b558d681be343df8993cf9fa40d21b1c,
  Fp.ofNat 0x12561a5deb559c4348b4711298e536367041e8ca0cf0800c0126c2588c48bf5713daa8846cb026e9e5c8276ec82b3bff,
  Fp.ofNat 0xb2962fe57a3225e8137e629bff2991f6f89416f5a718cd1fca64e00b11aceacd6a3d0967c94fedcfcc239ba5cb83e19,
  Fp.ofNat 0x3425581a58ae2fec83aafef7c40eb545b08243f16b1655154cca8abc28d6fd04976d5243eecf5c4130de8938dc62cd8,
  Fp.ofNat 0x13a8e162022914a80a6f1d5f43e7a07dffdfc759a12062bb8d6b44e833b306da9bd29ba81f35781d539d395b3532a21e,
  Fp.ofNat 0xe7355f8e4e667b955390f7f0506c6e9395735e9ce9cad4d0a43bcef24b8982f7400d24bc4228f11c02df9a29f6304a5,
  Fp.ofNat 0x772caacf16936190f3e0c63e0596721570f5799af53a1894e2e073062aede9cea73b3538f0de06cec2574496ee84a3a,
  Fp.ofNat 0x14a7ac2a9d64a8b230b3f5b074cf01996e7f63c21bca68a81996e1cdf9822c580fa5b9489d11e2d311f7d99bbdcc5a5e,
  Fp.ofNat 0xa10ecf6ada54f825e920b3dafc7a3cce07f8d1d7161366b74100da67f39883503826692abba43704776ec3a79a1d641,
  Fp.ofNat 0x95fc13ab9e92ad4476d6e3eb3a56680f682b4ee96f7d03776df533978f31c1593174e4b4b7865002d6384d168ecdd0a,
  Fp.ofNat 0x1]

private def iso11YNum : Array F := #[
  Fp.ofNat 0x90d97c81ba24ee0259d1f094980dcfa11ad138e48a869522b52af6c956543d3cd0c7aee9b3ba3c2be9845719707bb33,
  Fp.ofNat 0x134996a104ee5811d51036d776fb46831223e96c254f383d0f906343eb67ad34d6c56711962fa8bfe097e75a2e41c696,
  Fp.ofNat 0xcc786baa966e66f4a384c86a3b49942552e2d658a31ce2c344be4b91400da7d26d521628b00523b8dfe240c72de1f6,
  Fp.ofNat 0x1f86376e8981c217898751ad8746757d42aa7b90eeb791c09e4a3ec03251cf9de405aba9ec61deca6355c77b0e5f4cb,
  Fp.ofNat 0x8cc03fdefe0ff135caf4fe2a21529c4195536fbe3ce50b879833fd221351adc2ee7f8dc099040a841b6daecf2e8fedb,
  Fp.ofNat 0x16603fca40634b6a2211e11db8f0a6a074a7d0d4afadb7bd76505c3d3ad5544e203f6326c95a807299b23ab13633a5f0,
  Fp.ofNat 0x4ab0b9bcfac1bbcb2c977d027796b3ce75bb8ca2be184cb5231413c4d634f3747a87ac2460f415ec961f8855fe9d6f2,
  Fp.ofNat 0x987c8d5333ab86fde9926bd2ca6c674170a05bfe3bdd81ffd038da6c26c842642f64550fedfe935a15e4ca31870fb29,
  Fp.ofNat 0x9fc4018bd96684be88c9e221e4da1bb8f3abd16679dc26c1e8b6e6a1f20cabe69d65201c78607a360370e577bdba587,
  Fp.ofNat 0xe1bba7a1186bdb5223abde7ada14a23c42a0ca7915af6fe06985e7ed1e4d43b9b3f7055dd4eba6f2bafaaebca731c30,
  Fp.ofNat 0x19713e47937cd1be0dfd0b8f1d43fb93cd2fcbcb6caf493fd1183e416389e61031bf3a5cce3fbafce813711ad011c132,
  Fp.ofNat 0x18b46a908f36f6deb918c143fed2edcc523559b8aaf0c2462e6bfe7f911f643249d9cdf41b44d606ce07c8a4d0074d8e,
  Fp.ofNat 0xb182cac101b9399d155096004f53f447aa7b12a3426b08ec02710e807b4633f06c851c1919211f20d4c04f00b971ef8,
  Fp.ofNat 0x245a394ad1eca9b72fc00ae7be315dc757b3b080d4c158013e6632d3c40659cc6cf90ad1c232a6442d9d3f5db980133,
  Fp.ofNat 0x5c129645e44cf1102a159f748c4a3fc5e673d81d7e86568d9ab0f5d396a7ce46ba1049b6579afb7866b1e715475224b,
  Fp.ofNat 0x15e6be4e990f03ce4ea50b3b42df2eb5cb181d8f84965a3957add4fa95af01b2b665027efec01c7704b456be69c8b604]

private def iso11YDen : Array F := #[
  Fp.ofNat 0x16112c4c3a9c98b252181140fad0eae9601a6de578980be6eec3232b5be72e7a07f3688ef60c206d01479253b03663c1,
  Fp.ofNat 0x1962d75c2381201e1a0cbd6c43c348b885c84ff731c4d59ca4a10356f453e01f78a4260763529e3532f6102c2e49a03d,
  Fp.ofNat 0x58df3306640da276faaae7d6e8eb15778c4855551ae7f310c35a5dd279cd2eca6757cd636f96f891e2538b53dbf67f2,
  Fp.ofNat 0x16b7d288798e5395f20d23bf89edb4d1d115c5dbddbcd30e123da489e726af41727364f2c28297ada8d26d98445f5416,
  Fp.ofNat 0xbe0e079545f43e4b00cc912f8228ddcc6d19c9f0f69bbb0542eda0fc9dec916a20b15dc0fd2ededda39142311a5001d,
  Fp.ofNat 0x8d9e5297186db2d9fb266eaac783182b70152c65550d881c5ecd87b6f0f5a6449f38db9dfa9cce202c6477faaf9b7ac,
  Fp.ofNat 0x166007c08a99db2fc3ba8734ace9824b5eecfdfa8d0cf8ef5dd365bc400a0051d5fa9c01a58b1fb93d1a1399126a775c,
  Fp.ofNat 0x16a3ef08be3ea7ea03bcddfabba6ff6ee5a4375efa1f4fd7feb34fd206357132b920f5b00801dee460ee415a15812ed9,
  Fp.ofNat 0x1866c8ed336c61231a1be54fd1d74cc4f9fb0ce4c6af5920abc5750c4bf39b4852cfe2f7bb9248836b233d9d55535d4a,
  Fp.ofNat 0x167a55cda70a6e1cea820597d94a84903216f763e13d87bb5308592e7ea7d4fbc7385ea3d529b35e346ef48bb8913f55,
  Fp.ofNat 0x4d2f259eea405bd48f010a01ad2911d9c6dd039bb61a6290e591b36e636a5c871a5c29f4f83060400f8b49cba8f6aa8,
  Fp.ofNat 0xaccbb67481d033ff5852c1e48c50c477f94ff8aefce42d28c0f9a88cea7913516f968986f7ebbea9684b529e2561092,
  Fp.ofNat 0xad6b9514c767fe3c3613144b45f1496543346d98adf02267d5ceef9a00d9b8693000763e3b90ac11e99b138573345cc,
  Fp.ofNat 0x2660400eb2e4f3b628bdd0d53cd76f2bf565b94e72927c1cb748df27942480e420517bd8714cc80d1fadc1326ed06f7,
  Fp.ofNat 0xe0fa1d816ddc03e6b24255e0d7819c171c40f65e273b853324efcd6356caa205ca2f570f13497804415473a1d634b8f,
  Fp.ofNat 0x1]

private def iso3XNum : Array F2 := #[
  Fp2.ofNats 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6,
  Fp2.ofNats 0x0 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a,
  Fp2.ofNats 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e 0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d,
  Fp2.ofNats 0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1 0x0]

private def iso3XDen : Array F2 := #[
  Fp2.ofNats 0x0 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63,
  Fp2.ofNats 0xc 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f,
  Fp2.ofNats 0x1 0x0,
  Fp2.ofNats 0x0 0x0]

private def iso3YNum : Array F2 := #[
  Fp2.ofNats 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706,
  Fp2.ofNats 0x0 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be,
  Fp2.ofNats 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c 0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f,
  Fp2.ofNats 0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10 0x0]

private def iso3YDen : Array F2 := #[
  Fp2.ofNats 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb,
  Fp2.ofNats 0x0 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3,
  Fp2.ofNats 0x12 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99,
  Fp2.ofNats 0x1 0x0]


/-- The simplified SWU map (RFC 9380, Section 6.6.2) to `y² = x³ + A·x + B`. -/
def sswu {K : Type} [FieldOps K] (A B Z : K) (sqrt? : K → Option K) (sgn0 : K → Bool)
    (u : K) : K × K :=
  let u2 := u * u
  let tv := FieldOps.inv (Z * Z * u2 * u2 + Z * u2)
  let x₁ := if isZero tv then B * FieldOps.inv (Z * A) else -B * FieldOps.inv A * (one + tv)
  let g x := x * x * x + A * x + B
  let (x, y) :=
    match sqrt? (g x₁) with
    | some y => (x₁, y)
    | none =>
      let x₂ := Z * u2 * x₁
      (x₂, (sqrt? (g x₂)).getD zero)
  (x, if sgn0 u == sgn0 y then y else -y)

/-- The polynomial with coefficients `cs` (constant first) at `x`. -/
private def horner {K : Type} [FieldOps K] (cs : Array K) (x : K) : K :=
  cs.foldr (fun c acc => acc * x + c) zero

/-- A rational isogeny map, given the coefficients of its four polynomials. -/
private def isoMap {K : Type} [FieldOps K] (xNum xDen yNum yDen : Array K) (x y : K) : Jac K :=
  let xd := horner xDen x
  let yd := horner yDen x
  if isZero xd || isZero yd then Jac.infinity
  else Jac.ofAffine (horner xNum x * FieldOps.inv xd) (y * horner yNum x * FieldOps.inv yd)

def hEffG1 : Nat := 0xd201000000010001

def hEffG2 : Nat :=
  0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551

/-- `MAP_FP_TO_G1`. -/
def mapToG1 (u : F) : Jac F :=
  let A := Fp.ofNat 0x144698a3b8e9433d693a02c96d4982b0ea985383ee66a8d8e8981aefd881ac98936f8da0e0f97f5cf428082d584c1d
  let B := Fp.ofNat 0x12e2908d11688030018b12e8753eee3b2016c1f0f24f4070a0b9c14fcef35ef55a23215a316ceaa5d1cc48e98e172be0
  let (x, y) := sswu A B (Fp.ofNat 11) Fp.sqrt? Fp.sgn0 u
  g1Curve.mul (isoMap iso11XNum iso11XDen iso11YNum iso11YDen x y) hEffG1

/-- `MAP_FP2_TO_G2`. -/
def mapToG2 (u : F2) : Jac F2 :=
  let (x, y) := sswu (Fp2.ofNats 0 240) (Fp2.ofNats 1012 1012) (-Fp2.ofNats 2 1) Fp2.sqrt?
    Fp2.sgn0 u
  g2Curve.mul (isoMap iso3XNum iso3XDen iso3YNum iso3YDen x y) hEffG2

/-! ## The EIP-2537 precompiles -/

private def chunks (d : ByteArray) (size : Nat) : List ByteArray :=
  (List.range (d.size / size)).map fun i => d.extract (i * size) ((i + 1) * size)

/--
The EIP-2537 precompile at address `operation` (`0x0b`–`0x11`) on `data`, or
`none` when the call fails.
-/
def precompile (operation : Nat) (data : ByteArray) : Option ByteArray :=
  match operation with
  | 11 => encodeG1 <$> do
    guard (data.size == 256)
    let P ← decodeG1 (data.extract 0 128) false
    let Q ← decodeG1 (data.extract 128 256) false
    return g1Curve.add P Q
  | 12 => encodeG1 <$> do
    guard (data.size != 0 && data.size % 160 == 0)
    let terms ← (chunks data 160).mapM fun c => do
      let P ← decodeG1 (c.extract 0 128) true
      return g1Curve.mul P (ofBytesBE (c.extract 128 160))
    return terms.foldl g1Curve.add Jac.infinity
  | 13 => encodeG2 <$> do
    guard (data.size == 512)
    let P ← decodeG2 (data.extract 0 256) false
    let Q ← decodeG2 (data.extract 256 512) false
    return g2Curve.add P Q
  | 14 => encodeG2 <$> do
    guard (data.size != 0 && data.size % 288 == 0)
    let terms ← (chunks data 288).mapM fun c => do
      let Q ← decodeG2 (c.extract 0 256) true
      return g2Curve.mul Q (ofBytesBE (c.extract 256 288))
    return terms.foldl g2Curve.add Jac.infinity
  | 15 => (fun ok => toBytesBE (if ok then 1 else 0) 32) <$> do
    guard (data.size != 0 && data.size % 384 == 0)
    let pairs ← (chunks data 384).mapM fun c => do
      return (← decodeG1 (c.extract 0 128) true, ← decodeG2 (c.extract 128 384) true)
    return pairingCheck pairs
  | 16 => encodeG1 <$> do
    guard (data.size == 64)
    return mapToG1 (← decodeFp data)
  | 17 => encodeG2 <$> do
    guard (data.size == 128)
    return mapToG2 ⟨← decodeFp (data.extract 0 64), ← decodeFp (data.extract 64 128)⟩
  | _ => none

/-- The output size of the precompile at address `operation`. -/
def outputSize (operation : Nat) : Nat :=
  match operation with
  | 11 | 12 | 16 => 128
  | 13 | 14 | 17 => 256
  | 15 => 32
  | _ => 0

theorem precompile_size {operation : Nat} {data o : ByteArray}
    (h : precompile operation data = some o) : o.size = outputSize operation := by
  unfold precompile at h
  split at h
  · exact map_eq_some_size encodeG1_size h
  · exact map_eq_some_size encodeG1_size h
  · exact map_eq_some_size encodeG2_size h
  · exact map_eq_some_size encodeG2_size h
  · exact map_eq_some_size (fun _ => toBytesBE_size _ _) h
  · exact map_eq_some_size encodeG1_size h
  · exact map_eq_some_size encodeG2_size h
  · nomatch h

/-! ## KZG point evaluation (EIP-4844) -/

/-- `[τ]₂` of the KZG trusted setup (`KZG_SETUP_G2_MONOMIAL[1]`). -/
def tauG2 : Jac F2 :=
  Jac.ofAffine
    (Fp2.ofNats 0x185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2 0x15bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72)
    (Fp2.ofNats 0x14353bdb96b626dd7d5ee8599d1fca2131569490e28de18e82451a496a9c9794ce26d105941f383ee689bfbbb832a99 0x1666c54b0a32529503432fcae0181b4bef79de09fc63671fda5ed1ba9bfa07899495346f3d7ac9cd23048ef30d0a154f)

/--
A KZG commitment or proof: a compressed point of `G₁` in the ZCash encoding,
validated as `KeyValidate` does, except that the canonical encoding of the
point at infinity is allowed.
-/
def decompressG1 (d : ByteArray) : Option (Jac F) := do
  guard (d.size == 48)
  let z := ofBytesBE d
  let cFlag := z.testBit 383
  let bFlag := z.testBit 382
  let aFlag := z.testBit 381
  let x := z % 2 ^ 381
  guard cFlag
  if bFlag then
    guard (!aFlag && x == 0)
    return Jac.infinity
  guard (x != 0 && x < p)
  let xF : F := Fp.ofNat x
  let y ← (xF * xF * xF + g1Curve.b).sqrt?
  let y := if (y.val * 2 ≥ p) == aFlag then y else -y
  let P := Jac.ofAffine xF y
  guard (Jac.isInfinity (g1Curve.mul P r))
  return P

/-- `FIELD_ELEMENTS_PER_BLOB ‖ BLS_MODULUS`, the output of a successful point
    evaluation. -/
def pointEvaluationOutput : ByteArray := toBytesBE 4096 32 ++ toBytesBE r 32

/-- Whether a point-evaluation input is valid: see `pointEvaluation`. -/
def verifyPointEvaluation (data : ByteArray) : Option Unit := do
  guard (data.size == 192)
  let versionedHash := data.extract 0 32
  let commitment := data.extract 96 144
  guard (versionedHash == ByteArray.mk #[0x01] ++ (SHA256.hash commitment).extract 1 32)
  let z := ofBytesBE (data.extract 32 64)
  let y := ofBytesBE (data.extract 64 96)
  guard (z < r && y < r)
  let C ← decompressG1 commitment
  let π ← decompressG1 (data.extract 144 192)
  let P := g1Curve.add C (g1Curve.mul G1 ((r - y) % r))
  let Q := g2Curve.add tauG2 (g2Curve.mul G2 ((r - z) % r))
  guard (pairingCheck [(P, Jac.neg G2), (π, Q)])

/--
The point-evaluation precompile on the 192-byte input
`versioned_hash ‖ z ‖ y ‖ commitment ‖ proof`: checks that the commitment
matches the versioned hash and that the proof shows `p(z) = y`, by
`e(C - [y]₁, -[1]₂) · e(π, [τ]₂ - [z]₂) = 1`.
-/
def pointEvaluation (data : ByteArray) : Option ByteArray :=
  (fun () => pointEvaluationOutput) <$> verifyPointEvaluation data

theorem pointEvaluation_size {data o : ByteArray} (h : pointEvaluation data = some o) :
    o.size = 64 :=
  map_eq_some_size (fun _ => by simp [pointEvaluationOutput, toBytesBE_size]) h

end Ethereum.Crypto.BLS12_381
