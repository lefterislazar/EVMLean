/-
We need a more unified approach to maps.

This file shouldn't exist; but it does for now.
`Finmap`s have terrible computational behaviour, one needs some ordering lemmas to make them compute.

In `Conform`, we use `Lean.RBMap`, although we would ideally use `Batteries.RBMap`, but the `Lean.Json`
uses `Lean.RBMap`, which means that we would need an additional cast to `Batteries.RBMap`.

Furthermore, replacing everything with either of the `RBMaps` would then reintroduce this mess,
but with ordering lemmas needed for some `Decidable` instances.

When time allows, I suggest we replace everything with `Batteries.RBMap` and prove the reasoning lemmas we need.
This way, we get decent performance AND the ability to conveniently reason about the structure
a'la `Finmap`.

TODO - All of this is very ugly.
-/

import Batteries.Data.RBMap

import Ethereum.Wheels

import Ethereum.Maps.StorageMap

import Ethereum.State.Account
import Ethereum.State.AccountOps

namespace Ethereum

section RemoveLater

abbrev AddrMap (α : Type) [Inhabited α] := Batteries.RBMap AccountAddress α compare
abbrev AccountMap := AddrMap Account
abbrev PersistentAccountMap  := AddrMap (PersistentAccountState)
def AccountMap.toPersistentAccountMap  (a : AccountMap) : PersistentAccountMap :=
  a.mapVal (λ _ acc ↦ acc.toPersistentAccountState)

def AccountMap.increaseBalance  (σ : AccountMap) (addr : AccountAddress) (amount : UInt256)
  : AccountMap
:=
  match σ.find? addr with
    | none => σ.insert addr {(default : Account) with balance := amount}
    | some acc => σ.insert addr {acc with balance := acc.balance + amount}

/--
  Returns `none` in the case of an overflow below zero.
-/
def AccountMap.decreaseBalance  (σ : AccountMap) (addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap)
:=
  match σ.find? addr with
    | none => .none
    | some acc =>
      if acc.balance < amount then .none else .some (σ.insert addr {acc with balance := acc.balance - amount})

/--
  Returns `none` in the case of an overflow below zero.
-/
def AccountMap.transferBalance  (σ : AccountMap) (from_addr to_addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap)
:=
  match (σ.decreaseBalance from_addr amount) with
    | .none => .none
    | .some σ' => σ'.increaseBalance to_addr amount

def toExecute  (σ : AccountMap) (t : AccountAddress) : ToExecute :=
  if /- t is a precompiled account -/ t ∈ π then
    ToExecute.Precompiled t
  else Id.run do
    -- We use the code directly without an indirection a'la `codeMap[t]`.
    let .some tDirect := σ.find? t | ToExecute.Code default
    ToExecute.Code tDirect.code

def L_S (σ : PersistentAccountMap) : Array (ByteArray × ByteArray) :=
  σ.foldl
    (λ arr (addr : AccountAddress) acc ↦
      arr.push (p addr acc)
    )
    .empty
 where
  p (addr : AccountAddress) (acc : PersistentAccountState) : ByteArray × ByteArray :=
    (ffi.KEC addr.toByteArray, rlp acc)
  rlp (acc : PersistentAccountState) :=
    Option.get! <|
      RLP <|
        .𝕃
          [ .𝔹 (BE acc.nonce.toNat)
          , .𝔹 (BE acc.balance.toNat)
          , .𝔹 <| (computeTrieRoot acc.storage).getD .empty
          , .𝔹 acc.codeHash.toByteArray
          ]

def stateTrieRoot (σ : PersistentAccountMap) : Option ByteArray :=
  let a := Array.map toBlobPair (L_S σ)
  (ByteArray.ofBlob (blobComputeTrieRoot a)).toOption
 where
  toBlobPair entry : String × String :=
    let b₁ := Ethereum.toHex entry.1
    let b₂ := Ethereum.toHex entry.2
    (b₁, b₂)

end RemoveLater

end Ethereum
