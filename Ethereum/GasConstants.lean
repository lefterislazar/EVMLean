import Ethereum.UInt256

namespace GasConstants

section FeeSchedule

def Gzero : ℕ              := 0
def Gjumpdest : ℕ          := 1
def Gbase : ℕ              := 2
def Gverylow : ℕ           := 3
def Glow : ℕ               := 5
def Gmid : ℕ               := 8
def Ghigh : ℕ              := 10
def Gwarmaccess : ℕ        := 100
def Gaccesslistaddress : ℕ := 2400
def Gaccessliststorage : ℕ := 1900
def Gcoldaccountaccess : ℕ := 2600
def Gcoldsload : ℕ         := 2100
def Gsset : ℕ              := 20000
def Gsreset : ℕ            := 2900
def Rsclear : ℕ            := 4800
def Gselfdestruct : ℕ      := 5000
def Gcreate : ℕ            := 32000
def Gcodedeposit : ℕ       := 200
def Ginitcodeword : ℕ      := 2
def Gcallvalue : ℕ         := 9000
def Gcallstipend : ℕ       := 2300
def Gnewaccount : ℕ        := 25000
def Gexp : ℕ               := 10
def Gexpbyte : ℕ           := 50
def Gmemory : ℕ            := 3
def Gtxcreate : ℕ          := 32000
def Gtxdatazero : ℕ        := 4
def Gtxdatanonzero : ℕ     := 16
def Gtransaction : ℕ       := 21000
def Glog : ℕ               := 375
def Glogdata : ℕ           := 8
def Glogtopic : ℕ          := 375
def Gkeccak256 : ℕ         := 30
def Gkeccak256word : ℕ     := 6
def Gcopy : ℕ              := 3
def Gblockhash : ℕ         := 20
def HASH_OPCODE_GAS : ℕ    := 3
/-- EIP-7702 (Prague) base cost of an authorization for an existing account. -/
def Gauthbase : ℕ          := 12500
/-- EIP-7623 (Prague) cost per calldata token in the transaction floor. -/
def Gfloorpertoken : ℕ     := 10

end FeeSchedule

end GasConstants

namespace GasConstants

/-! ## Amsterdam (EIP-2780, EIP-7976, EIP-7981, EIP-8038) -/

/-- EIP-2780: the base cost of a transaction. -/
def GtxbaseAmsterdam : ℕ    := 12000
/-- EIP-2780: the cost of a transaction that moves value to another account. -/
def Gtxvalue : ℕ            := 6000
/-- EIP-8038: the cost of writing an account. -/
def Gaccountwrite : ℕ       := 9000
/-- EIP-8038: the cold account access cost. -/
def GcoldaccountaccessAmsterdam : ℕ := 3000
/-- EIP-8038: accessing and writing a new account, of a creation. -/
def Gcreateaccess : ℕ       := Gaccountwrite + GcoldaccountaccessAmsterdam
/-- EIP-8038: writing a storage slot away from its value at the start of the
    transaction. -/
def Gstoragewrite : ℕ       := 10000
/-- EIP-8038: the refund for clearing a storage slot that was set at the start
    of the transaction, `(Gstoragewrite + Gcoldsload) * 4800 / 5000`. -/
def RsclearAmsterdam : ℕ    := (Gstoragewrite + Gcoldsload) * 4800 / 5000
/-- EIP-8038: a call that moves value writes the recipient's account and gives
    the stipend. -/
def GcallvalueAmsterdam : ℕ := Gaccountwrite + Gcallstipend
/-- EIP-8038: the access list costs, the cold costs less the warm one. -/
def GaccesslistaddressAmsterdam : ℕ := GcoldaccountaccessAmsterdam - Gwarmaccess
def GaccessliststorageAmsterdam : ℕ := Gcoldsload - Gwarmaccess
/-- EIP-7976: the floor cost of a calldata token. -/
def GfloorpertokenAmsterdam : ℕ := 16
/-- EIP-7981: the floor tokens of an access list address and storage key. -/
def Gaccesslistaddresstokens : ℕ := 80
def Gaccessliststoragetokens : ℕ := 128
/-- EIP-8038: the execution cost of an authorization: its 101 bytes at the
    floor token cost, two cold accesses and two warm ones. -/
def GauthexecutionAmsterdam : ℕ :=
  101 * GfloorpertokenAmsterdam + 2 * GcoldaccountaccessAmsterdam + 2 * Gwarmaccess
/-- EIP-7825 and EIP-8037: the execution gas a transaction can spend, and the
    largest gas limit of a transaction. -/
def TX_MAX_GAS_LIMIT : ℕ       := 2 ^ 24
def TX_MAX_TOTAL_GAS_LIMIT : ℕ := 2 ^ 32 - 1

end GasConstants
