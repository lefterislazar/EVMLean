/- Storage uses an extensional tree map so equality depends on slot contents. -/

import Std.Data.ExtTreeMap.Lemmas
import Mathlib.Data.Multiset.Sort

import Ethereum.Wheels
import Ethereum.State.TrieRoot
import Ethereum.SpongeHash.Keccak256


namespace Ethereum

section RemoveLater

abbrev Storage : Type := Std.ExtTreeMap UInt256 UInt256 compare

def Storage.toFinmap (self : Storage) : Finmap (λ _ : UInt256 ↦ UInt256) :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

def toTriePair (pair : UInt256 × UInt256) : Option (ByteArray × ByteArray) := do
  let kec := KEC pair.1.toByteArray
  let rlp ← RLP (.𝔹 (BE pair.2.toNat))
  pure (kec, rlp)

def computeTrieRoot (storage : Storage) : Option ByteArray :=
  Trie.root <$> Array.mapM toTriePair storage.toArray

end RemoveLater

end Ethereum
