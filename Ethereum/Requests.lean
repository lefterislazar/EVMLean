import Ethereum.FFI.ffi
import Ethereum.State.Substate

/-!
# Execution-layer requests (Prague)

EIP-7685 commits a block to the requests its execution produces: deposits
(EIP-6110), extracted from deposit-contract logs, and withdrawal (EIP-7002)
and consolidation (EIP-7251) requests, returned by system calls to their
request contracts after the block's transactions.
-/

namespace Ethereum

def SYSTEM_ADDRESS : AccountAddress := 0xfffffffffffffffffffffffffffffffffffffffe

/-- EIP-4788 beacon block root contract (Cancun). -/
def BEACON_ROOTS_ADDRESS : AccountAddress := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02

/-- EIP-2935 historical block hashes contract (Prague). -/
def HISTORY_STORAGE_ADDRESS : AccountAddress := 0x0000F90827F1C53a10cb7A02335B175320002935

/-- EIP-6110 deposit contract of mainnet, used by the test fixtures. -/
def DEPOSIT_CONTRACT_ADDRESS : AccountAddress := 0x00000000219ab540356cBB839Cbe05303d7705Fa

/-- EIP-7002 withdrawal request contract. -/
def WITHDRAWAL_REQUEST_ADDRESS : AccountAddress := 0x00000961Ef480Eb55e80D19ad83579A64c007002

/-- EIP-7251 consolidation request contract. -/
def CONSOLIDATION_REQUEST_ADDRESS : AccountAddress := 0x0000BBdDc7CE488642fb579F8B00f3a590007251

/-- Gas given to system calls (EIP-4788, EIP-2935, EIP-7002, EIP-7251). -/
def SYSTEM_TRANSACTION_GAS : ℕ := 30000000

/-- `keccak256("DepositEvent(bytes,bytes,bytes,bytes,bytes)")` -/
def DEPOSIT_EVENT_SIGNATURE_HASH : UInt256 :=
  ⟨0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5⟩

/--
The request payload of an ABI-encoded `DepositEvent`: public key (48 bytes),
withdrawal credentials (32), amount (8), signature (96) and index (8). The
event must have the canonical layout of five dynamic `bytes` fields.
-/
def parseDepositEvent (data : ByteArray) : Except String ByteArray := do
  if data.size ≠ 576 then throw "invalid deposit event length"
  let word (i : ℕ) : ℕ := fromByteArrayBigEndian (data.extract (32 * i) (32 * i + 32))
  let offsets := [160, 256, 320, 384, 512]
  for (expected, i) in offsets.zipIdx do
    if word i ≠ expected then throw "invalid deposit event offset"
  let fields := [(160, 48), (256, 32), (320, 8), (384, 96), (512, 8)]
  let mut payload := ByteArray.empty
  for (offset, size) in fields do
    if fromByteArrayBigEndian (data.extract offset (offset + 32)) ≠ size then
      throw "invalid deposit event field size"
    payload := payload ++ data.extract (offset + 32) (offset + 32 + size)
  pure payload

/-- EIP-6110: the deposit requests of a block, from its logs in order. -/
def depositRequests (logs : LogSeries) : Except String ByteArray :=
  logs.foldlM (init := .empty) λ output log ↦ do
    if log.address = DEPOSIT_CONTRACT_ADDRESS ∧ log.topics[0]? = some DEPOSIT_EVENT_SIGNATURE_HASH then
      pure <| output ++ (← parseDepositEvent log.data)
    else
      pure output

/-- EIP-7685: `sha256(sha256(type₀ ++ data₀) ++ …)` over the non-empty requests. -/
def computeRequestsHash (requests : List (UInt8 × ByteArray)) : Except String ByteArray := do
  let requests := requests.filter (¬·.2.isEmpty)
  let hashes ← requests.mapM λ (type, data) ↦ ffi.SHA256 (⟨#[type]⟩ ++ data)
  ffi.SHA256 (hashes.foldl (· ++ ·) .empty)

end Ethereum
