import Ethereum.State.SubstateOps
import Ethereum.State.AccountOps

import Ethereum.Maps.AccountMap

import Ethereum.MachineState
import Ethereum.MachineStateOps

import Ethereum.State
import Ethereum.Wheels
import Ethereum.GasConstants

namespace Ethereum

namespace State

def addAccessedAccount (self : State) (addr : AccountAddress) : State :=
  { self with substate := self.substate.addAccessedAccount addr }

def addAccessedStorageKey (self : State) (sk : AccountAddress × UInt256) : State :=
  { self with substate := self.substate.addAccessedStorageKey sk }

/--
DEAD(σ, a). Section 4.1., equation 15.
-/
def dead (σ : AccountMap) (addr : AccountAddress) : Bool :=
  σ.find? addr |>.option True Account.emptyAccount

def accountExists (self : State) (addr : AccountAddress) : Bool := self.accountMap.find? addr |>.isSome

def lookupAccount (self : State) (addr : AccountAddress) : Option Account :=
  self.accountMap.find? addr

def updateAccount (addr : AccountAddress) (act : Account) (self : State) : State :=
  { self with accountMap := self.accountMap.insert addr act }

def setAccount (self : State) (addr : AccountAddress) (acc : Account) : State :=
  { self with accountMap := self.accountMap.insert addr acc }

def setSelfAccount (self : State) (acc : Account := default) : State :=
  self.setAccount self.executionEnv.codeOwner acc

def updateAccount! (self : State) (addr : AccountAddress) (f : Account → Account) : State :=
  let acc! := self.lookupAccount addr |>.getD default
  self.setAccount addr (f acc!)

def updateSelfAccount! (self : State) : (Account → Account) → State :=
  self.updateAccount! self.executionEnv.codeOwner

def balance (self : State) (k : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 k
  (self.addAccessedAccount addr, self.accountMap.find? addr |>.elim ⟨0⟩ (·.balance))

def initialiseAccount (addr : AccountAddress) (self : State) : State :=
  if self.accountExists addr then self else self.updateAccount addr default

def calldataload (self : State) (v : UInt256) : UInt256 :=
  uInt256OfByteArray <| self.executionEnv.calldata.readBytes v.toNat 32

def setNonce! (self : State) (addr : AccountAddress) (nonce : UInt256) : State :=
  self.updateAccount! addr (λ acc ↦ { acc with nonce := nonce })

def setSelfNonce! (self : State) (nonce : UInt256) : State :=
  self.setNonce! self.executionEnv.codeOwner nonce

def selfStorage! (self : State) : Storage :=
  self.lookupAccount self.executionEnv.codeOwner |>.getD default |>.storage

section CodeCopy

def extCodeSize (self : State) (a : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 a
  let s := self.lookupAccount addr |>.option ⟨0⟩ (.ofNat ∘ ByteArray.size ∘ (·.code))
  (self.addAccessedAccount addr, s)

def extCodeHash (self : State) (v : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 v
  let newState := self.addAccessedAccount addr
  if dead self.accountMap addr then (newState, ⟨0⟩) else
  let r := self.lookupAccount (AccountAddress.ofUInt256 v) |>.option ⟨0⟩ Account.codeHash
  (newState, r)

end CodeCopy

section Blocks

def blockHash (self : State) (blockNumber : UInt256) : UInt256 :=
  let v := self.executionEnv.header.number
  if v ≤ blockNumber.toNat || blockNumber.toNat + 256 < v then ⟨0⟩
  else
    let hashes := self.blockHashes
    hashes.getD blockNumber.toNat ⟨0⟩

def coinBase (self : State) : AccountAddress :=
  self.executionEnv.header.beneficiary

def timeStamp (self : State) : UInt256 :=
  .ofNat self.executionEnv.header.timestamp

def number (self : State) : UInt256 :=
  .ofNat self.executionEnv.header.number

def difficulty (self : State) : UInt256 :=
  .ofNat self.executionEnv.header.difficulty

def gasLimit (self : State) : UInt256 :=
  .ofNat self.executionEnv.header.gasLimit

def chainId (_ : State) : UInt256 := .ofNat Ethereum.chainId

def selfbalance (self : State) : UInt256 :=
  Batteries.RBMap.find? self.accountMap self.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)

def setCode (self : State) (code : ByteArray) : State :=
  { self with executionEnv.code := code }

end Blocks

section Storage

def setStorage! (self : State) (addr : AccountAddress) (strg : Storage) : State :=
  self.updateAccount! addr (λ acc ↦ { acc with storage := strg })

def setSelfStorage! (self : State) : Storage → State :=
  self.setStorage! self.executionEnv.codeOwner

def sload (self : State) (spos : UInt256) : State × UInt256 :=
  let Iₐ := self.executionEnv.codeOwner
  let v := self.lookupAccount Iₐ |>.option ⟨0⟩ (Account.lookupStorage (k := spos))
  let state' := self.addAccessedStorageKey (Iₐ, spos)
  (state', v)

def sstore (self : State) (spos sval : UInt256) : State :=
  let Iₐ := self.executionEnv.codeOwner
  let { storage := σ_Iₐ, .. } := self.accountMap.find! Iₐ
  let v₀ :=
    match self.σ₀.find? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.findD spos ⟨0⟩
  let v := σ_Iₐ.findD spos ⟨0⟩
  let v' := sval

  let r_dirtyclear : ℤ :=
    if v₀ ≠ .ofNat 0 && v = .ofNat 0 then - GasConstants.Rsclear else
    if v₀ ≠ .ofNat 0 && v' = .ofNat 0 then GasConstants.Rsclear else
    0

  let r_dirtyreset : ℤ :=
    if v₀ = v' && v₀ = .ofNat 0 then GasConstants.Gsset - GasConstants.Gwarmaccess else
    if v₀ = v' && v₀ ≠ .ofNat 0 then GasConstants.Gsreset - GasConstants.Gwarmaccess else
    0

  let ΔAᵣ : ℤ :=
    if v ≠ v' && v₀ = v && v' = .ofNat 0 then GasConstants.Rsclear else
    if v ≠ v' && v₀ ≠ v then r_dirtyclear + r_dirtyreset else
    0

  let newAᵣ : UInt256 :=
    match ΔAᵣ with
      | .ofNat n => self.substate.refundBalance + .ofNat n
      | .negSucc n => self.substate.refundBalance - .ofNat n - ⟨1⟩
  self.lookupAccount Iₐ |>.option self λ acc ↦
    let self' :=
      self.setAccount Iₐ (acc.updateStorage spos sval)
        |>.addAccessedStorageKey (Iₐ, spos)
    { self' with substate.refundBalance := newAᵣ }

def tload (self : State) (spos : UInt256) : State × UInt256 :=
  let Iₐ := self.executionEnv.codeOwner
  let v := self.lookupAccount Iₐ |>.option ⟨0⟩ (Account.lookupTransientStorage (k := spos))
  (self, v)

def tstore (self : State) (spos sval : UInt256) : State :=
  let Iₐ := self.executionEnv.codeOwner
  self.lookupAccount Iₐ |>.option self λ acc ↦
    self.updateAccount Iₐ (acc.updateTransientStorage spos sval)

end Storage

section Instructions

def incrPC (I : State) (pcΔ : ℕ := 1) : State :=
  { I with pc := I.pc + .ofNat pcΔ }

def replaceStackAndIncrPC (I : State) (s : Stack UInt256) (pcΔ : ℕ := 1) : State :=
  incrPC { I with stack := s } pcΔ

end Instructions

def liftMState {m} [Monad m] (f : Ethereum.State → m (Ethereum.State)) : State → m State :=
  λ s ↦ do f s 

instance {m} [Monad m] : CoeFun (Ethereum.State → m (Ethereum.State)) (λ _ ↦ State → m State) := ⟨liftMState⟩

def liftState (f : Ethereum.State → Ethereum.State) : State → State :=
  liftMState (m := Id) f

instance : CoeFun (Ethereum.State → Ethereum.State) (λ _ ↦ State → State) := ⟨liftState⟩

def isEmpty (self : State) : Bool := self.accountMap == ∅

end State

section Keccak

end Keccak

section Memory

def writeWord (self : State) (addr v : UInt256) : State :=
  let numOctets := 32
  let source : ByteArray := v.toByteArray
  { self with memory := source.write 0 self.memory addr.toNat numOctets }

def lookupMemory (self : State) (addr : UInt256) : UInt256 :=
  if addr.toNat ≥ self.memory.size ∨ addr ≥ self.activeWords * ⟨32⟩ then ⟨0⟩ else
    let bytes := self.memory.readWithPadding addr.toNat 32
    let val := fromByteArrayBigEndian bytes
    .ofNat val

def msize (self : State) : UInt256 :=
  self.activeWords * ⟨32⟩

def mload (self : State) (spos : UInt256) : UInt256 × State :=
  let val := lookupMemory self spos
  let self :=
    { self with
      activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 32)
    }
  (val, self)

def mstore (self : State) (spos sval : UInt256) : State :=
  let self := writeWord self spos sval
  { self with
    activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 32)
  }

def mstore8 (self : State) (spos sval : UInt256) : State :=
  let self := { self with memory := (⟨#[UInt8.ofNat sval.toNat]⟩ : ByteArray).write 0 self.memory spos.toNat 1 }
  { self with
    activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 1)
  }

def mcopy (self : State) (writeStart readStart s : UInt256) : State :=
  let self := { self with memory := self.memory.write readStart.toNat self.memory writeStart.toNat s.toNat }
  { self with
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat (max writeStart.toNat readStart.toNat) s.toNat)
  }

def gas (self : State) : UInt256 :=
  self.gasAvailable

def setReturnData (self : State) (r : ByteArray) : State :=
  { self with returnData := r }

def setHReturn (self : State) (r : ByteArray) : State :=
  { self with H_return := r }

def returndatasize (self : State) : UInt256 :=
  .ofNat self.returnData.size

def returndataat (self : State) (pos : UInt256) : UInt8 :=
  self.returnData.data.getD pos.toNat 0

def returndatacopy (self : State) (mstart rstart size : UInt256) : State :=
  let self := { self with memory := self.returnData.write rstart.toNat self.memory mstart.toNat size.toNat }
  { self with
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }

def evmReturn (self : State) (mstart s : UInt256) : State :=
  { self with
    H_return := self.memory.readWithPadding mstart.toNat s.toNat
    activeWords :=
      .ofNat <| MachineState.M self.activeWords.toNat mstart.toNat s.toNat
  }

def evmRevert (self : State) (mstart s : UInt256) : State :=
  let self := evmReturn self mstart s
  { self with
    activeWords :=
      .ofNat <| MachineState.M self.activeWords.toNat mstart.toNat s.toNat
  }

def keccak256 (self : State) (mstart s : UInt256) : UInt256 × State :=
  let bytes := self.memory.readWithPadding mstart.toNat s.toNat
  let kec := ffi.KEC bytes
  let newState :=
    { self with activeWords := .ofNat (MachineState.M self.activeWords.toNat mstart.toNat s.toNat) }
  (.ofNat (fromByteArrayBigEndian kec), newState)


def calldatacopy (self : State) (mstart datastart size : UInt256) : State :=
  { self with
    memory := self.executionEnv.calldata.write datastart.toNat self.memory mstart.toNat size.toNat
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }

def codeCopy  (self : State) (mstart cstart size : UInt256) : State :=
  { self with
    memory := self.executionEnv.code.write cstart.toNat self.memory mstart.toNat size.toNat
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }

def extCodeCopy' (self : State) (acc mstart cstart size : UInt256) : State :=
  let mstart := mstart.toNat
  let cstart := cstart.toNat
  let size := size.toNat
  let addr := AccountAddress.ofUInt256 acc
  let b : ByteArray := self.lookupAccount addr |>.option .empty (·.code)
  { self with
    memory := b.write cstart self.memory mstart size
    substate := .addAccessedAccount self.substate addr
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart size)
  }

end Memory

def logOp (μ₀ μ₁ : UInt256) (t : Array UInt256) (sState : State) : State :=
  let Iₐ := sState.executionEnv.codeOwner
  let mem := sState.memory.readWithPadding μ₀.toNat μ₁.toNat
  { sState with
    substate.logSeries := sState.substate.logSeries.push ⟨Iₐ, t, mem⟩
    activeWords := .ofNat (MachineState.M sState.activeWords.toNat μ₀.toNat μ₁.toNat)
  }

end Ethereum
