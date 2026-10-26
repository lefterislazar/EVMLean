import CryptoTests.Vectors
import Ethereum.Crypto.BLAKE2F
import Ethereum.Crypto.BLS12_381
import Ethereum.Crypto.BN254
import Ethereum.Crypto.P256
import Ethereum.Crypto.RIPEMD160
import Ethereum.Crypto.Secp256k1
import Ethereum.Crypto.SHA256
import Ethereum.State.TrieRoot

/-!
# Tests of the cryptographic primitives

Runs the pure Lean primitives of `Ethereum/Crypto` and the trie root on the
vectors of `CryptoTests/Vectors.lean`, which come from independent reference
implementations, and checks a few algebraic properties of the curves.
-/

namespace CryptoTests

open Ethereum Ethereum.Crypto

def hexDigit (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else none

def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    out := out.push ((hexDigit cs[2 * i]!).get! * 16 + (hexDigit cs[2 * i + 1]!).get!)
  return out

def hex (b : ByteArray) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList <| b.data.toList.flatMap fun byte =>
    [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!]

/-- The key/value pairs of an RLP list of two-element lists. -/
def triePairs (d : ByteArray) : Option (Array (ByteArray × ByteArray)) := do
  let .𝕃 items ← deserializeRLP d | none
  items.toArray.mapM fun
    | .𝕃 [.𝔹 k, .𝔹 v] => some (k, v)
    | _ => none

/-- Run the primitive `name` on `input`; `none` when the call fails. -/
def run (name : String) (input : ByteArray) : Option ByteArray :=
  match name with
  | "sha256" => SHA256.hash input
  | "ripemd160" => RIPEMD160.hash input
  | "blake2f" => BLAKE2F.blake2f input
  | "ecrecover" =>
    (Secp256k1.ecdsaRecover (input.extract 0 32) (input.extract 32 33) (input.extract 33 65)
      (input.extract 65 97)).toOption
  | "p256verify" => if P256.verifyInput input then toBytesBE 1 32 else ByteArray.empty
  | "bn_add" =>
    BN254.add (input.extract 0 32) (input.extract 32 64) (input.extract 64 96)
      (input.extract 96 128)
  | "bn_mul" => BN254.mul (input.extract 0 32) (input.extract 32 64) (input.extract 64 96)
  | "bn_pairing" => BN254.snarkv input
  | "kzg" => BLS12_381.pointEvaluation input
  | "trie" => Trie.root <$> triePairs input
  | _ =>
    if name.startsWith "bls_" then BLS12_381.precompile (name.drop 4).toNat! input
    else none

open BLS12_381 in
/-- Algebraic checks that do not need a reference implementation. -/
def properties : List (String × Bool) :=
  let a := 0x1234567890abcdef
  let b := 0xfedcba0987654321
  [ ("BLS12-381 generators are in their groups",
      Jac.isInfinity (g1Curve.mul G1 r) && Jac.isInfinity (g2Curve.mul G2 r))
  , ("BLS12-381 pairing is bilinear",
      pairingCheck [(g1Curve.mul G1 a, g2Curve.mul G2 b), (Jac.neg (g1Curve.mul G1 (a * b)), G2)])
  , ("BLS12-381 pairing is nondegenerate", !pairingCheck [(G1, G2)])
  , ("the KZG setup point is on the twist",
      ((Jac.toAffine tauG2).map fun (x, y) => g2Curve.onCurve x y) == some true)
  , ("hashing to G1 lands in G1",
      Jac.isInfinity (g1Curve.mul (mapToG1 (Fp.ofNat 12345)) r))
  , ("hashing to G2 lands in G2",
      Jac.isInfinity (g2Curve.mul (mapToG2 (Fp2.ofNats 12345 678)) r))
  , ("secp256k1 generator has order n",
      Jac.isInfinity (Secp256k1.curve.mul Secp256k1.G Secp256k1.n))
  , ("secp256r1 generator has order n", Jac.isInfinity (P256.curve.mul P256.G P256.n))
  , ("empty trie root",
      hex (Trie.root #[]) == "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
  ]

end CryptoTests

open CryptoTests in
def main : IO UInt32 := do
  let mut failures := 0
  let mut timings : Std.HashMap String Nat := {}
  for (name, input, expected) in vectors do
    let start ← IO.monoMsNow
    let actual := match run name (ofHex input) with
      | some out => hex out
      | none => "error"
    timings := timings.insert name (timings.getD name 0 + ((← IO.monoMsNow) - start))
    if actual != expected then
      failures := failures + 1
      IO.println s!"FAIL {name}\n  input:    {input}\n  expected: {expected}\n  actual:   {actual}"
  for (description, ok) in properties do
    if !ok then
      failures := failures + 1
      IO.println s!"FAIL {description}"
  let names := (timings.toList.map (·.1)).mergeSort
  for name in names do
    IO.println s!"{name}: {timings.getD name 0} ms"
  IO.println s!"{vectors.size} vectors and {properties.length} properties, {failures} failures"
  return if failures == 0 then 0 else 1
