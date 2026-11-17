import Lean.Data.Json

import Ethereum.UInt256
import Ethereum.Wheels

/-!
# JSON helpers

The fixtures encode numbers, addresses and byte strings as hex strings
(`"0x…"`). The `FromJson` instances for them are scoped to `Ethereum.Conform`,
so that they do not replace the instances elsewhere, such as the core one
that reads a `Nat` from a JSON number.
-/

namespace Ethereum

namespace Conform

open Lean (FromJson Json)

/-- The number that the hex string `s`, such as `0x1f`, encodes. -/
def hexNat? (s : String) : Except String ℕ := do
  let digits ← getBlob? s
  match Lean.Syntax.decodeNatLitVal? ("0x" ++ toString digits) with
  | some n => pure n
  | none => throw s!"not a hex number: {s}"

def hexUInt256? (s : String) : Except String UInt256 := do
  let n ← hexNat? s
  if n < UInt256.size then pure (.ofNat n) else throw s!"not a 256-bit number: {s}"

def hexAddress? (s : String) : Except String AccountAddress := do
  let n ← hexNat? s
  if n < AccountAddress.size then pure (.ofNat n) else throw s!"not an address: {s}"

/-- The hex number in the field `k` of `json`. -/
def getHexNat? (json : Json) (k : String) : Except String ℕ :=
  json.getObjValAs? String k >>= hexNat?

scoped instance : FromJson UInt256 := ⟨(·.getStr? >>= hexUInt256?)⟩
scoped instance : FromJson ByteArray := ⟨(·.getStr? >>= getBlob? >>= ByteArray.ofBlob)⟩

/-- The JSON object `json`, as a map from its decoded keys to its decoded values. -/
def getObjMap? {α β : Type} [Ord α] [Std.TransCmp (compare : α → α → Ordering)] [FromJson β]
    (key : String → Except String α) (json : Json) : Except String (Std.ExtTreeMap α β compare) := do
  (← json.getObj?).foldlM (init := ∅) fun map k v => do
    pure <| map.insert (← key k) (← Lean.fromJson? v)

def readJsonFile (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok json => pure json
  | .error err => throw <| .userError s!"{path}: {err}"

end Conform

end Ethereum
