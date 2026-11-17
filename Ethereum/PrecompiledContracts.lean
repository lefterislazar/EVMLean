import Mathlib.Data.Nat.Log

import Ethereum.Maps.AccountMap
import Ethereum.UInt256
import Ethereum.State.Substate
import Ethereum.State.ExecutionEnv
import Ethereum.Exception
import Ethereum.Wheels

import Ethereum.EllipticCurves
import Ethereum.SHA256
import Ethereum.RIP160
import Ethereum.BN_ADD
import Ethereum.BN_MUL
import Ethereum.SNARKV
import Ethereum.BLAKE2_F
import Ethereum.PointEval
import Ethereum.P256Verify
import Ethereum.BLS12_381

import Ethereum.FFI.ffi

open Ethereum

def Ξ_ECREC
  (σ : (AccountMap))
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ := 3000

  if g.toNat < gᵣ then
    (∅, ⟨0⟩, A, .empty)
  else
    let d := I.calldata
    let h := d.readBytes 0 32
    let v := d.readBytes 32 32
    let r := d.readBytes 64 32
    let s := d.readBytes 96 32
    let v' : ℕ := fromByteArrayBigEndian v
    let r' : ℕ := fromByteArrayBigEndian r
    let s' : ℕ := fromByteArrayBigEndian s
    let o :=
      if v' < 27 || 28 < v' || r' = 0 || r' >= secp256k1n || s' = 0 || s' >= secp256k1n then
        .empty
      else
        match ECDSARECOVER h ⟨#[.ofNat v' - 27]⟩ r s with
          | .ok s =>
              ByteArray.zeroes 12 ++ (KEC s).extract 12 32
          | .error e =>
            dbg_trace s!"Ξ_ECREC failed: {e}"
            .empty
    (σ, g - .ofNat gᵣ, A, o)

def Ξ_SHA256
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ :=
    let l := I.calldata.size
    let ceil := ( l + 31 ) / 32
    60 + 12 * ceil

  if g.toNat < gᵣ then
    (∅, ⟨0⟩, A, .empty)
  else
    let o :=
      match ffi.SHA256 I.calldata with
        | .ok s => s
        | .error e =>
          dbg_trace s!"Ξ_SHA56 failed: {e}"
          .empty
    (σ, g - .ofNat gᵣ, A, o)

def Ξ_RIP160
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ :=
    let l := I.calldata.size
    let ceil := ( l + 31 ) / 32
    600 + 120 * ceil

  if g.toNat < gᵣ then
    (∅, ⟨0⟩, A, .empty)
  else
    let o :=
      match RIP160 I.calldata with
        | .ok s => s
        | .error e =>
          dbg_trace s!"Ξ_RIP160 failed: {e}"
          .empty
    (σ, g - .ofNat gᵣ, A, o)

def Ξ_ID
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ :=
    let l := I.calldata.size
    let ceil := ( l + 31 ) / 32
    15 + 3 * ceil

  if g.toNat < gᵣ then
    (∅, ⟨0⟩, A, .empty)
  else
    let o := I.calldata
    (σ, g - .ofNat gᵣ, A, o)

def nat_of_slice
  (B: ByteArray)
  (start: ℕ)
  (width: ℕ) : ℕ
:=
  let slice := B.readWithoutPadding start width
  let padding := width - slice.size
  fromByteArrayBigEndian slice <<< (8 * padding)

def expModAux (m : ℕ) (a : ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => a % m
  | n@(k + 1) =>
    if n % 2 == 1 then
      expModAux m (a * c % m) (c * c % m) (n / 2)
    else
      expModAux m (a % m)     (c * c % m) (n / 2)

def expMod (m b n : ℕ) : ℕ := expModAux m 1 b n

/--
`adjusted_exponent_length` of EIP-2565. From Osaka on, EIP-7883 counts each
exponent byte beyond the first 32 as 16 bits instead of 8.
-/
def expmodAdjustedExponentLength
    (fork : Fork) (data : ByteArray) (baseLength exponentLength : ℕ) : ℕ :=
  let exponentHead := nat_of_slice data (96 + baseLength) (min exponentLength 32)
  let headBits := if exponentHead = 0 then 0 else Nat.log 2 exponentHead
  if exponentLength ≤ 32 then
    headBits
  else
    let bytesFactor := if fork.spec.eip7883 then 16 else 8
    bytesFactor * (exponentLength - 32) + headBits

/--
Gas of the `EXPMOD` precompile: EIP-2565 before Osaka, EIP-7883 from Osaka
on. `none` when an input length exceeds the EIP-7823 bound of 1024 bytes
(Osaka), which makes the call fail.
-/
def expmodRequiredGas (fork : Fork) (data : ByteArray) : Option ℕ :=
  let baseLength := nat_of_slice data 0 32
  let exponentLength := nat_of_slice data 32 32
  let modulusLength := nat_of_slice data 64 32
  if fork.spec.eip7823 ∧ (baseLength > 1024 ∨ exponentLength > 1024 ∨ modulusLength > 1024) then
    none
  else
    let maxLength := max baseLength modulusLength
    let words := (maxLength + 7) / 8
    let iterations := max (expmodAdjustedExponentLength fork data baseLength exponentLength) 1
    if fork.spec.eip7883 then
      let complexity := if maxLength > 32 then 2 * words ^ 2 else 16
      some <| max 500 (complexity * iterations)
    else
      some <| max 200 (words ^ 2 * iterations / 3)

def Ξ_EXPMOD
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let data := I.calldata
  let base_length := nat_of_slice data 0 32
  let exp_length := nat_of_slice data 32 32
  let modulus_length := nat_of_slice data 64 32
  match expmodRequiredGas I.fork data with
  | none => (∅, ⟨0⟩, A, .empty)
  | some gᵣ =>
    if g.toNat < gᵣ then
      (∅, ⟨0⟩, A, .empty)
    else
      let modulus := nat_of_slice data (96 + base_length + exp_length) modulus_length
      let o : ByteArray :=
        if modulus_length == 0 || modulus == 0 then
          ByteArray.zeroes modulus_length
        else
          let base := nat_of_slice data 96 base_length
          let exp := nat_of_slice data (96 + base_length) exp_length
          let expmod_base := BE (expMod modulus base exp)
          let expmod_zeroes :=
            if modulus_length ≥ expmod_base.size then
              ByteArray.zeroes (modulus_length - expmod_base.size)
            else
              ByteArray.empty
          expmod_zeroes ++ expmod_base
      (σ, g - .ofNat gᵣ, A, o)

private def expmodOutput :=
  let (_, _, o) :=
    Ξ_EXPMOD
      default
      ⟨3000⟩
      default
      { (default : ExecutionEnv) with
        calldata := l_B ++ l_E ++ l_M ++ B ++ E ++ M
      }
  o
 where
  l_B : ByteArray := UInt256.toByteArray ⟨2⟩
  l_E : ByteArray := UInt256.toByteArray ⟨1⟩
  l_M : ByteArray := UInt256.toByteArray ⟨1⟩
  B : ByteArray := ⟨#[1, 0]⟩ -- 2^8
  E : ByteArray := ⟨#[2]⟩
  M : ByteArray := ⟨#[100]⟩

def Ξ_BN_ADD
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ := 150

  if g.toNat < gᵣ then
    (∅, ⟨0⟩, A, .empty)
  else
    let d := I.calldata
    let x := (d.readBytes 0 32, d.readBytes 32 32)
    let y := (d.readBytes 64 32, d.readBytes 96 32)
    let o := BN_ADD x.1 x.2 y.1 y.2
    match o with
      | .ok o => (σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_BN_ADD failed: {e}"
        -- (σ, g - gᵣ, A, .empty)
        (∅, ⟨0⟩, A, .empty)

private def bn_addOutput₀ :=
  let (_, _, _, o) :=
    Ξ_BN_ADD
      default
      ⟨3000⟩
      default
      { (default : ExecutionEnv) with
        calldata := x₁ ++ y₁ ++ x₂ ++ y₂
      }
  o
 where
  x₁ : ByteArray := UInt256.toByteArray ⟨0⟩
  y₁ : ByteArray := UInt256.toByteArray ⟨0⟩
  x₂ : ByteArray := UInt256.toByteArray ⟨1⟩
  y₂ : ByteArray := UInt256.toByteArray ⟨2⟩

private def bn_addOutput₁ :=
  let (_, _, _, o) :=
    Ξ_BN_ADD
      default
      ⟨3000⟩
      default
      { (default : ExecutionEnv) with
        calldata := bn_addOutput₀ ++ x ++ y
      }
  o
 where
  x : ByteArray := UInt256.toByteArray ⟨1⟩
  y : ByteArray := UInt256.toByteArray ⟨2⟩

def Ξ_BN_MUL
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ := 6000

  if g.toNat < gᵣ then
    (∅, ⟨0⟩, A, .empty)
  else
    let d := I.calldata
    let x := (d.readBytes 0 32, d.readBytes 32 32)
    let n := d.readBytes 64 32
    let o := BN_MUL x.1 x.2 n
    match o with
      | .ok o => (σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_BN_MUL failed: {e}"
        -- (σ, g - gᵣ, A, .empty)
        (∅, ⟨0⟩, A, .empty)

private def bn_mulOutput :=
  let (_, _, _, o) :=
    Ξ_BN_MUL
      default
      ⟨100000⟩
      default
      { (default : ExecutionEnv) with
        calldata := x₁ ++ y₁ ++ n
      }
  o
 where
  x₁ : ByteArray := UInt256.toByteArray ⟨1⟩
  y₁ : ByteArray := UInt256.toByteArray ⟨2⟩
  n  : ByteArray := UInt256.toByteArray ⟨2⟩

def Ξ_SNARKV
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let d := I.calldata
  let k := d.size / 192
  let gᵣ : ℕ := 34000 * k + 45000

  if g.toNat < gᵣ then
    (∅, ⟨0⟩, A, .empty)
  else
    let o := SNARKV d
    match o with
      | .ok o => (σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_SNARKV failed: {e}"
        (∅, ⟨0⟩, A, .empty)

private def snarkvOutput :=
  let (_, _, _, o) :=
    Ξ_SNARKV
      default
      ⟨100000⟩
      default
      { (default : ExecutionEnv) with
        calldata := x ++ y ++ ByteArray.zeroes (32 * 4)
      }
  o
 where
  x : ByteArray := UInt256.toByteArray ⟨1⟩
  y : ByteArray := UInt256.toByteArray ⟨2⟩

def Ξ_BLAKE2_F
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let d := I.calldata
  let gᵣ : ℕ := fromByteArrayBigEndian (d.extract 0 4)

  if g.toNat < gᵣ then
    dbg_trace "failed"
    (∅, ⟨0⟩, A, .empty)
  else
    let o := ffi.BLAKE2 d
    match o with
      | .ok o => (σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_BLAKE2_F failed: {e}"
        (∅, ⟨0⟩, A, .empty)

def Ξ_PointEval
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let d := I.calldata
  let gᵣ : ℕ := 50000

  if g.toNat < gᵣ then
    (∅, ⟨0⟩, A, .empty)
  else
    let o := PointEval d
    match o with
      | .ok o => (σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_PointEval failed: {e}"
        (∅, ⟨0⟩, A, .empty)

/-- EIP-7951 `P256VERIFY` at `0x100` (Osaka). -/
def Ξ_P256VERIFY
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ := 6900
  if g.toNat < gᵣ then
    (∅, ⟨0⟩, A, .empty)
  else
    match P256Verify I.calldata with
    | .ok o => (σ, g - .ofNat gᵣ, A, o)
    | .error e =>
      dbg_trace s!"Ξ_P256VERIFY failed: {e}"
      (∅, ⟨0⟩, A, .empty)

private def blsG1Discounts : Array ℕ := #[
  1000,949,848,797,764,750,738,728,719,712,705,698,692,687,682,677,
  673,669,665,661,658,654,651,648,645,642,640,637,635,632,630,627,
  625,623,621,619,617,615,613,611,609,608,606,604,603,601,599,598,
  596,595,593,592,591,589,588,586,585,584,582,581,580,579,577,576,
  575,574,573,572,570,569,568,567,566,565,564,563,562,561,560,559,
  558,557,556,555,554,553,552,551,550,549,548,547,547,546,545,544,
  543,542,541,540,540,539,538,537,536,536,535,534,533,532,532,531,
  530,529,528,528,527,526,525,525,524,523,522,522,521,520,520,519]

private def blsG2Discounts : Array ℕ := #[
  1000,1000,923,884,855,832,812,796,782,770,759,749,740,732,724,717,
  711,704,699,693,688,683,679,674,670,666,663,659,655,652,649,646,
  643,640,637,634,632,629,627,624,622,620,618,615,613,611,609,607,
  606,604,602,600,598,597,595,593,592,590,589,587,586,584,583,582,
  580,579,578,576,575,574,573,571,570,569,568,567,566,565,563,562,
  561,560,559,558,557,556,555,554,553,552,552,551,550,549,548,547,
  546,545,545,544,543,542,541,541,540,539,538,537,537,536,535,535,
  534,533,532,532,531,530,530,529,528,528,527,526,526,525,524,524]

/-- EIP-2537 multi-scalar-multiplication discount for `k` pairs, per mille. -/
private def blsDiscount (discounts : Array ℕ) (k : ℕ) : ℕ :=
  if k = 0 then 0 else discounts[k - 1]?.getD (discounts[127]?.getD 0)

/-- Gas of the EIP-2537 precompile at address `operation`. -/
def blsRequiredGas (operation inputSize : ℕ) : ℕ :=
  match operation with
  | 11 => 375
  | 12 =>
    let k := inputSize / 160
    k * 12000 * blsDiscount blsG1Discounts k / 1000
  | 13 => 600
  | 14 =>
    let k := inputSize / 288
    k * 22500 * blsDiscount blsG2Discounts k / 1000
  | 15 => 32600 * (inputSize / 384) + 37700
  | 16 => 5500
  | 17 => 23800
  | _ => 0

private theorem blsDiscount_ge (discounts : Array ℕ) (m : ℕ)
    (hall : ∀ x ∈ discounts.toList, m ≤ x) (hlast : m ≤ discounts[127]?.getD 0)
    {k : ℕ} (hk : 1 ≤ k) : m ≤ blsDiscount discounts k := by
  unfold blsDiscount
  rw [if_neg (by omega)]
  cases h : discounts[k - 1]? with
  | none => simpa using hlast
  | some x => exact hall x (Array.mem_def.mp (Array.mem_of_getElem? h))

set_option maxRecDepth 65536 in
/-- Every valid EIP-2537 input costs gas. -/
theorem blsRequiredGas_pos_of_valid {operation size : ℕ}
    (h : blsInputLengthValid operation size = true) : 0 < blsRequiredGas operation size := by
  unfold blsInputLengthValid at h
  split at h
  · simp [blsRequiredGas]
  · -- G1MSM
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    have hk : 1 ≤ size / 160 := by omega
    have hd : 519 ≤ blsDiscount blsG1Discounts (size / 160) :=
      blsDiscount_ge _ _ (by decide) (by decide) hk
    have hm : 1 * 12000 * 519 ≤ size / 160 * 12000 * blsDiscount blsG1Discounts (size / 160) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hk) hd
    simp only [blsRequiredGas]
    exact Nat.div_pos (by omega) (by norm_num)
  · simp [blsRequiredGas]
  · -- G2MSM
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    have hk : 1 ≤ size / 288 := by omega
    have hd : 524 ≤ blsDiscount blsG2Discounts (size / 288) :=
      blsDiscount_ge _ _ (by decide) (by decide) hk
    have hm : 1 * 22500 * 524 ≤ size / 288 * 22500 * blsDiscount blsG2Discounts (size / 288) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hk) hd
    simp only [blsRequiredGas]
    exact Nat.div_pos (by omega) (by norm_num)
  · simp [blsRequiredGas]
  · simp [blsRequiredGas]
  · simp [blsRequiredGas]
  · simp at h

/-- Output size of the EIP-2537 precompile at address `operation`. -/
def blsOutputSize (operation : ℕ) : ℕ :=
  match operation with
  | 11 | 12 | 16 => 128
  | 13 | 14 | 17 => 256
  | 15 => 32
  | _ => 0

/-- The EIP-2537 BLS12-381 precompiles at `0x0b`–`0x11` (Prague). -/
def Ξ_BLS12_381
  (operation : ℕ)
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ := blsRequiredGas operation I.calldata.size
  if g.toNat < gᵣ then
    (∅, ⟨0⟩, A, .empty)
  else
    match BLS12_381 operation (blsOutputSize operation) I.calldata with
    | .ok o => (σ, g - .ofNat gᵣ, A, o)
    | .error _ => (∅, ⟨0⟩, A, .empty)

/--
The precompiled contract at address `p`, as a function of the state, the gas,
the substate and the execution environment. Which addresses are precompiles at
a fork is decided by `π` (see `toExecute`); this dispatch is fork independent.
Failure is signalled by an empty account map.
-/
def Ξ_PRECOMPILE
  (p : AccountAddress)
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  if p = 1 then Ξ_ECREC σ g A I
  else if p = 2 then Ξ_SHA256 σ g A I
  else if p = 3 then Ξ_RIP160 σ g A I
  else if p = 4 then Ξ_ID σ g A I
  else if p = 5 then Ξ_EXPMOD σ g A I
  else if p = 6 then Ξ_BN_ADD σ g A I
  else if p = 7 then Ξ_BN_MUL σ g A I
  else if p = 8 then Ξ_SNARKV σ g A I
  else if p = 9 then Ξ_BLAKE2_F σ g A I
  else if p = 10 then Ξ_PointEval σ g A I
  else if p = 11 then Ξ_BLS12_381 11 σ g A I
  else if p = 12 then Ξ_BLS12_381 12 σ g A I
  else if p = 13 then Ξ_BLS12_381 13 σ g A I
  else if p = 14 then Ξ_BLS12_381 14 σ g A I
  else if p = 15 then Ξ_BLS12_381 15 σ g A I
  else if p = 16 then Ξ_BLS12_381 16 σ g A I
  else if p = 17 then Ξ_BLS12_381 17 σ g A I
  else if p = 256 then Ξ_P256VERIFY σ g A I
  else default

/-- A property of every precompile result, and of the default result, holds
    for the dispatch. -/
theorem Ξ_PRECOMPILE_induction
    (P : AccountMap × UInt256 × Substate × ByteArray → Prop)
    {p : AccountAddress} {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hECREC : P (Ξ_ECREC σ g A I)) (hSHA256 : P (Ξ_SHA256 σ g A I))
    (hRIP160 : P (Ξ_RIP160 σ g A I)) (hID : P (Ξ_ID σ g A I))
    (hEXPMOD : P (Ξ_EXPMOD σ g A I)) (hBN_ADD : P (Ξ_BN_ADD σ g A I))
    (hBN_MUL : P (Ξ_BN_MUL σ g A I)) (hSNARKV : P (Ξ_SNARKV σ g A I))
    (hBLAKE2_F : P (Ξ_BLAKE2_F σ g A I)) (hPointEval : P (Ξ_PointEval σ g A I))
    (hBLS : ∀ op, P (Ξ_BLS12_381 op σ g A I)) (hP256 : P (Ξ_P256VERIFY σ g A I))
    (hdefault : P default) :
    P (Ξ_PRECOMPILE p σ g A I) := by
  unfold Ξ_PRECOMPILE
  by_cases h1 : p = 1
  · rw [if_pos h1]; exact hECREC
  rw [if_neg h1]
  by_cases h2 : p = 2
  · rw [if_pos h2]; exact hSHA256
  rw [if_neg h2]
  by_cases h3 : p = 3
  · rw [if_pos h3]; exact hRIP160
  rw [if_neg h3]
  by_cases h4 : p = 4
  · rw [if_pos h4]; exact hID
  rw [if_neg h4]
  by_cases h5 : p = 5
  · rw [if_pos h5]; exact hEXPMOD
  rw [if_neg h5]
  by_cases h6 : p = 6
  · rw [if_pos h6]; exact hBN_ADD
  rw [if_neg h6]
  by_cases h7 : p = 7
  · rw [if_pos h7]; exact hBN_MUL
  rw [if_neg h7]
  by_cases h8 : p = 8
  · rw [if_pos h8]; exact hSNARKV
  rw [if_neg h8]
  by_cases h9 : p = 9
  · rw [if_pos h9]; exact hBLAKE2_F
  rw [if_neg h9]
  by_cases h10 : p = 10
  · rw [if_pos h10]; exact hPointEval
  rw [if_neg h10]
  by_cases h11 : p = 11
  · rw [if_pos h11]; exact hBLS 11
  rw [if_neg h11]
  by_cases h12 : p = 12
  · rw [if_pos h12]; exact hBLS 12
  rw [if_neg h12]
  by_cases h13 : p = 13
  · rw [if_pos h13]; exact hBLS 13
  rw [if_neg h13]
  by_cases h14 : p = 14
  · rw [if_pos h14]; exact hBLS 14
  rw [if_neg h14]
  by_cases h15 : p = 15
  · rw [if_pos h15]; exact hBLS 15
  rw [if_neg h15]
  by_cases h16 : p = 16
  · rw [if_pos h16]; exact hBLS 16
  rw [if_neg h16]
  by_cases h17 : p = 17
  · rw [if_pos h17]; exact hBLS 17
  rw [if_neg h17]
  by_cases h256 : p = 256
  · rw [if_pos h256]; exact hP256
  rw [if_neg h256]
  exact hdefault
