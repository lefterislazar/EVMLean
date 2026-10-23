import Batteries.Data.RBMap
import Ethereum.Maps.StorageMap
import Ethereum.SpongeHash.Keccak256

import Ethereum.UInt256
import Ethereum.Wheels
import Ethereum.Fork

namespace Ethereum

/--
  Precompiled contract addresses, `π`, at a fork.
  - Cancun: `{1, …, 10}`, up to the EIP-4844 point evaluation.
  - Prague: adds the EIP-2537 BLS12-381 precompiles `{11, …, 17}`.
  - Osaka: adds the EIP-7951 secp256r1 verifier at `0x100`.
-/
def π (fork : Fork) : Batteries.RBSet AccountAddress compare :=
  let highest := if fork.spec.eip2537 then 17 else 10
  let base := Batteries.RBSet.ofList ((List.range (highest + 1)).tail.map (Fin.ofNat _)) compare
  if fork.spec.eip7951 then base.insert (Fin.ofNat _ 0x100) else base

/-- The EIP-7702 delegation designator prefix. -/
def DELEGATION_PREFIX : ByteArray := ⟨#[0xef, 0x01, 0x00]⟩

/-- The code `0xef0100 ++ target` installed by an EIP-7702 authorization. -/
def delegationDesignation (target : AccountAddress) : ByteArray :=
  DELEGATION_PREFIX ++ target.toByteArray

/-- The target of an EIP-7702 delegation designator, if `code` is one. -/
def delegationTarget? (code : ByteArray) : Option AccountAddress :=
  if code.size = 23 ∧ code.extract 0 3 = DELEGATION_PREFIX then
    some <| .ofNat <| fromByteArrayBigEndian (code.extract 3 23)
  else none

def isDelegationDesignation (code : ByteArray) : Bool :=
  (delegationTarget? code).isSome

inductive ToExecute where
  | Code (code : ByteArray)
  | Precompiled (precompiled : AccountAddress)

structure PersistentAccountState where
  nonce    : UInt256
  balance  : UInt256
  storage  : Storage
  code     : ByteArray
  deriving BEq, Inhabited, Repr

/--
The `Account` data. Section 4.1.

Suppose `a` is some address.

- `nonce`    -- σ[a]ₙ.
- `balance`  -- σ[a]_b.

In the yellow paper it is supposed to be a 256-bit hash of the root node of
a Merkle Tree. KEVM implemets it as just an key/value map.
- `storage`  -- σ[a]_s.
- `tstorage` -- Transiont storage; added in EIP-1153
- `codeHash` -- σ[a]_c.

For now, we assume no global map `GM` with which `GM[code_hash] ≡ code`.
- `code`
-/
structure Account extends PersistentAccountState where
  tstorage : Storage
deriving BEq, Inhabited

def PersistentAccountState.codeHash (self : PersistentAccountState) : UInt256 :=
  .ofNat <| fromByteArrayBigEndian (KEC self.code)

def Account.codeHash (self : Account) : UInt256 :=
  self.toPersistentAccountState.codeHash

end Ethereum
