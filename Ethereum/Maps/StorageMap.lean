/- Storage uses an extensional tree map so equality depends on slot contents. -/

import Std.Data.ExtTreeMap.Lemmas
import Mathlib.Data.Multiset.Sort

import Ethereum.Wheels
import Ethereum.State.TrieRoot
import Ethereum.SpongeHash.Keccak256

import Ethereum.FFI.ffi

namespace Std.ExtTreeMap

def find? {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : ExtTreeMap α β cmp) (key : α) : Option β :=
  m.get? key

def findD {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : ExtTreeMap α β cmp) (key : α) (fallback : β) : β :=
  (m.find? key).getD fallback

def find! {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Inhabited β]
    (m : ExtTreeMap α β cmp) (key : α) : β :=
  (m.find? key).getD (panic! "key is not in the map")

theorem find?_congr {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    {k₁ k₂ : α} (m : ExtTreeMap α β cmp) (h : cmp k₁ k₂ = .eq) :
    m.find? k₁ = m.find? k₂ := by
  simpa [find?, ExtTreeMap.get?_eq_getElem?] using
    (ExtTreeMap.getElem?_congr (t := m) h)

@[simp] theorem find?_insert_of_eq {α β : Type} {cmp : α → α → Ordering}
    [Std.TransCmp cmp] {k' k : α} {v : β}
    (m : ExtTreeMap α β cmp) (h : cmp k' k = .eq) :
    (m.insert k v).find? k' = some v := by
  rw [find?_congr (m.insert k v) h]
  simp [find?, ExtTreeMap.get?_eq_getElem?]

theorem find?_insert_of_ne {α β : Type} {cmp : α → α → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {k' k : α} {v : β}
    (m : ExtTreeMap α β cmp) (h : cmp k' k ≠ .eq) :
    (m.insert k v).find? k' = m.find? k' := by
  have h' : cmp k k' ≠ .eq := by
    intro heq
    have hkk' : k = k' := Std.LawfulEqCmp.eq_of_compare heq
    subst k
    exact h Std.ReflCmp.compare_self
  simp [find?, ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert, h']

end Std.ExtTreeMap

namespace Ethereum

section RemoveLater

abbrev Storage : Type := Std.ExtTreeMap UInt256 UInt256 compare

def Storage.toFinmap (self : Storage) : Finmap (λ _ : UInt256 ↦ UInt256) :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

def toBlobs (pair : UInt256 × UInt256) : Option (String × String) := do
  let kec := KEC pair.1.toByteArray
  let rlp ← RLP (.𝔹 (BE pair.2.toNat))
  pure (Ethereum.toHex kec, Ethereum.toHex rlp)

def computeTrieRoot (storage : Storage) : Option ByteArray :=
  match Array.mapM toBlobs storage.toArray with
    | none => .none
    | some pairs => (ByteArray.ofBlob (blobComputeTrieRoot pairs)).toOption

end RemoveLater

end Ethereum
