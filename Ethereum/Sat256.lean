import Ethereum.UInt256

namespace Ethereum

-- Saturating bounded integer of size 2^256
structure Sat256 where
  val : ℕ
  isLt : LT.lt val UInt256.size

namespace Sat256

def sub (a b : Sat256) : Sat256 :=
  ⟨a.val - b.val, Nat.lt_of_le_of_lt (m := a.val) (Nat.sub_le a.val b.val) a.2⟩

def subNat (a : Sat256) (b : ℕ) : Sat256 :=
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

instance {n : ℕ} : OfNat Sat256 n where
  ofNat := ⟨min n (UInt256.size - 1),
    by
      apply Nat.lt_of_le_of_lt
      · apply Nat.min_le_right
      · simp [UInt256.size]⟩

instance : Repr Sat256 where
  reprPrec n _ := repr n.toNat

@[ext] theorem ext {a b : Sat256} (h : a.toNat = b.toNat) : a = b := by
  cases a
  cases b
  simp [toNat] at h
  subst h
  rfl

@[simp] theorem eq_iff_toNat {a b : Sat256} :
    a = b ↔ a.toNat = b.toNat := by
  constructor
  · intro h
    rw [h]
  · exact ext

@[simp] theorem le_iff_toNat {a b : Sat256} :
    a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

@[simp] theorem lt_iff_toNat {a b : Sat256} :
    a < b ↔ a.toNat < b.toNat := Iff.rfl

@[simp] theorem subNat_toNat (a : Sat256) (n : Nat) :
    (a.subNat n).toNat = a.toNat - n := rfl

@[simp] theorem toUInt256_toNat (a : Sat256) :
    a.toUInt256.toNat = a.toNat := rfl

@[simp] theorem ofUInt256_toNat (a : UInt256) :
    (Sat256.ofUInt256 a).toNat = a.toNat := rfl

@[simp] theorem subNat_zero (a : Sat256) :
    a.subNat 0 = a := by
  ext
  simp

@[simp] theorem subNat_subNat (a : Sat256) (m n : Nat) :
    (a.subNat m).subNat n = a.subNat (m + n) := by
  ext
  simp
  omega

theorem subNat_assoc (a : Sat256) (m n : Nat) :
    (a.subNat m).subNat n = (a.subNat n).subNat m := by
  ext
  simp
  omega

theorem subNat_sub_add_of_sub_sub (a : Sat256) (m n : Nat) :
    (a.subNat m).subNat n = a.subNat (m + n) :=
  a.subNat_subNat m n

theorem subNat_le (a : Sat256) (n : Nat) :
    (a.subNat n).toNat ≤ a.toNat := by
  simp

theorem subNat_eq_zero_of_le {a : Sat256} {n : Nat}
    (h : a.toNat ≤ n) :
    a.subNat n = 0 := by
  cases a with
  | mk val isLt =>
    apply ext
    change val - n = 0
    simp [toNat] at h
    omega

theorem subNat_add_cancel {a : Sat256} {n : Nat}
    (h : n ≤ a.toNat) :
    (a.subNat n).toNat + n = a.toNat := by
  simp
  omega

end Sat256

end Ethereum
