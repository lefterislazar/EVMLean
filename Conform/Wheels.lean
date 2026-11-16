import Lean.Data.Json
import Ethereum.UInt256
import Ethereum.Wheels
import Batteries.Data.RBMap


namespace Lean.Json

/--
Turn non-existance of the key into default initialisation.

This silences ONLY the `property not found:` error.
If the parsing of an existing value fails, we propagate the error.
-/
def getObjValAsD (j : Json) (α : Type) [FromJson α] (k : String) (D : α) : Except String α :=
  match j.getObjVal? k with
    | .error _   => pure D
    | .ok    val => fromJson? val

/--
`getObjValAsD! = getObjValAsD default` for inhabited types.
-/
def getObjValAsD! (j : Json) (α : Type) [FromJson α] [Inhabited α] (k : String) : Except String α :=
  getObjValAsD j α k default

def getObjVals?
  (self : Json) (α β : Type) [Ord α] [FromJson α] [FromJson β] : Except String (Batteries.RBMap α β compare) := do
  let keys := (← self.getObj?).toArray.map Prod.fst
  let mut result : Batteries.RBMap α β compare := ∅
  for k in keys do
    if let .ok key := FromJson.fromJson? (.str k) then
      result := result.insert key (← self.getObjValAs? β k)
  pure result

def fromFile (path : System.FilePath) : IO Json := do
  let .ok json ← Json.parse <$> IO.FS.readFile path | panic! s!"Failed to parse Json at: {path}"
  pure json

end Lean.Json

namespace Ethereum

section WithConform

namespace UInt256

def fromBlob? (blob : Blob) : Except String UInt256 :=
  .ofNat <$> ((·.1) <| blob.foldr (init := (.ok 0, 0)) λ digit (acc, exp) ↦
    (do pure <| (←acc) + (16 ^ exp) * (←cToHex? digit), exp + 1))

end UInt256

def Nat.fromBlob? (blob : Blob) : Except String ℕ :=
  ((·.1) <| blob.foldr (init := (.ok 0, 0)) λ digit (acc, exp) ↦
    (do pure <| (←acc) + (16 ^ exp) * (←cToHex? digit), exp + 1))

namespace AccountAddress

def fromBlob? (s : Blob) : Except String AccountAddress := (Fin.ofNat _ ·.toNat) <$> UInt256.fromBlob? s

end AccountAddress

end WithConform

end Ethereum
