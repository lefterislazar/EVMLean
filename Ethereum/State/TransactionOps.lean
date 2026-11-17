import Ethereum.State.Transaction
import Ethereum.State.BlockHeader
import Ethereum.State.ExecutionEnv

namespace Ethereum

def Transaction.to? : Transaction → Option AccountAddress
  | .legacy t | .access t | .dynamic t | .blob t | .setCode t => t.recipient

def Transaction.data : Transaction → ByteArray
  | .legacy t | .access t | .dynamic t | .blob t | .setCode t => t.data

def VERSIONED_HASH_VERSION_KZG : UInt8 := 1

def getTotalBlobGas (t : Transaction) : ℕ :=
  match t with
  | .blob t => GAS_PER_BLOB * t.blobVersionedHashes.length
  | _ => 0

def Transaction.blobVersionedHashes (t : Transaction) : List ByteArray :=
  match t with
  | .blob t => t.blobVersionedHashes
  | _ => []

def calcBlobFee (fork : Fork) (header: BlockHeader) (t : Transaction) : ℕ :=
  let totalBlobGas := getTotalBlobGas t
  totalBlobGas * header.getBlobGasprice fork

end Ethereum
