import Ethereum.UInt256

namespace Ethereum

-- Saturating bounded integer of size 2^256
structure Sat256 where
  val : ℕ
  isLt : LT.lt val UInt256.size

namespace Sat256

def sub (a b : Sat256) : Sat256 :=
  ⟨a.val - b.val, Nat.lt_of_le_of_lt (m := a.val) (Nat.sub_le a.val b.val) a.2⟩

def natSub (a : Sat256) (b : ℕ) : Sat256 :=
  ⟨a.val - b, Nat.lt_of_le_of_lt (m := a.val) (Nat.sub_le a.val b) a.2⟩

def toUInt256 (a : Sat256) : UInt256 := ⟨⟨a.val, a.isLt⟩⟩

def toNat (a : Sat256) : ℕ := a.val

def ofUInt256 (a : UInt256) : Sat256 := ⟨a.val.val, a.val.isLt⟩

instance : Sub Sat256 := ⟨Sat256.sub⟩

instance : LT Sat256 where
  lt a b := LT.lt a.val b.val

instance : LE Sat256 where
  le a b := LE.le a.val b.val

instance : Inhabited Sat256 where
  default := ⟨0, by simp [UInt256.size]⟩

instance : Repr UInt256 where
  reprPrec n _ := repr n.toNat

end Sat256

