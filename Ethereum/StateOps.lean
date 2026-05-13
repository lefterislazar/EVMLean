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
  { I with machineState.pc := I.machineState.pc + .ofNat pcΔ }

def replaceStackAndIncrPC (I : State) (s : Stack UInt256) (pcΔ : ℕ := 1) : State :=
  incrPC { I with machineState.stack := s } pcΔ

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
  { self with machineState := self.machineState.writeWord addr v }


def calldatacopy (self : State) (mstart datastart size : UInt256) : State :=
  { self with
    machineState.memory := self.executionEnv.calldata.write datastart.toNat self.machineState.memory mstart.toNat size.toNat
    machineState.activeWords :=
      .ofNat (MachineState.M self.machineState.activeWords.toNat mstart.toNat size.toNat)
  }

def codeCopy  (self : State) (mstart cstart size : UInt256) : State :=
  { self with
    machineState.memory := self.executionEnv.code.write cstart.toNat self.machineState.memory mstart.toNat size.toNat
    machineState.activeWords :=
      .ofNat (MachineState.M self.machineState.activeWords.toNat mstart.toNat size.toNat)
  }

def extCodeCopy' (self : State) (acc mstart cstart size : UInt256) : State :=
  let mstart := mstart.toNat
  let cstart := cstart.toNat
  let size := size.toNat
  let addr := AccountAddress.ofUInt256 acc
  let b : ByteArray := self.lookupAccount addr |>.option .empty (·.code)
  { self with
    machineState.memory := b.write cstart self.machineState.memory mstart size
    substate := .addAccessedAccount self.substate addr
    machineState.activeWords :=
      .ofNat (MachineState.M self.machineState.activeWords.toNat mstart size)
  }

end Memory

def logOp (μ₀ μ₁ : UInt256) (t : Array UInt256) (sState : State) : State :=
  let Iₐ := sState.executionEnv.codeOwner
  let mem := sState.machineState.memory.readWithPadding μ₀.toNat μ₁.toNat
  { sState with
    substate.logSeries := sState.substate.logSeries.push ⟨Iₐ, t, mem⟩
    machineState.activeWords := .ofNat (MachineState.M sState.machineState.activeWords.toNat μ₀.toNat μ₁.toNat)
  }

end Ethereum
