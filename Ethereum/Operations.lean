import Ethereum.UInt256
import Ethereum.MachineState

import Mathlib.Data.Finmap

namespace Ethereum

set_option autoImplicit true

-- inductive OperationType where
--   | Yul
--   | EVM
--   deriving DecidableEq, Repr

namespace Operation

section Operation

/--
  Stop and Arithmetic Operations
-/
inductive SAOp : Type where
  /--
    Stop: halts program execution
    δ: 0 ; α : 0
  -/
  | protected STOP : SAOp
  /--
    ADD: adds two stack values.
    δ: 2 ; α : 1
  -/
  | protected ADD : SAOp
  /--
    MUL: multiplies two stack values.
    δ: 2 ; α : 1
  -/
  | protected MUL : SAOp
  /--
    SUB: subtracts two stack values.
    δ: 2 ; α : 1
  -/
  | protected SUB : SAOp
  /--
    DIV: divides two stack values.
    δ: 2 ; α: 1
  -/
  | protected DIV : SAOp
  /--
    SDIV: signed integer division
    δ: 2 ; α: 1
  -/
  | protected SDIV : SAOp
  /--
    MOD: Modulo remainder operation
    δ: 2 ; α: 1
  -/
  | protected MOD : SAOp
  /--
    SMOD: signed integer remainder
    δ: 2 ; α: 1
  -/
  | protected SMOD : SAOp
  /--
    ADDMOD: addition modulo operation
    δ: 3 ; α: 1
  -/
  | protected ADDMOD : SAOp
  /--
    MULMOD: multiplication modulo operation
    δ: 3 ; α: 1
  -/
  | protected MULMOD : SAOp
  /--
    EXP: Exponential operation
    δ:2 ; α: 1
  -/
  | protected EXP : SAOp
  /--
    SIGNEXTEND: Extend length of two's complement signed integer
    δ: 2 ; α: 1
  -/
  | protected SIGNEXTEND : SAOp
  deriving DecidableEq, Repr

/--
  Comparison & Bitwise Logic Operations
-/
inductive CBLOp : Type where
  /--
    LT: less than comparison
    δ: 2 ; α: 1
  -/
  | protected LT : CBLOp
  /--
    GT: greater than comparison
    δ: 2 ; α: 1
  -/
  | protected GT : CBLOp
  /--
    SLT: signed less-than comparison
    δ:2 ; α: 1
  -/
  | protected SLT : CBLOp
  /--
    SGT: signed greater-than comparison
    δ: 2 ; α: 1
  -/
  | protected SGT : CBLOp
  /--
    EQ: equality test
    δ:2 ; α : 1
  -/
  | protected EQ : CBLOp
  /--
    ISZERO: simple not operation
    δ: 1 ; α : 1
  -/
  | protected ISZERO : CBLOp
  /--
    AND: bitwise and
    δ:2 ; α: 1
  -/
  | protected AND : CBLOp
  /--
    OR: bitwise or
    δ: 2 ; α: 1
  -/
  | protected OR : CBLOp
  /--
    XOR: bitwise xor
    δ: 2 ; α: 1
  -/
  | protected XOR : CBLOp
  /--
    NOT: bitwise not
    δ:1 ; α: 1
  -/
  | protected NOT : CBLOp
  /--
    BYTE: retrieve single byte from a word
    δ:2 ; α:1
  -/
  | protected BYTE : CBLOp
  /--
    SHL: shift left operation
    δ:2 ; α: 1
  -/
  | protected SHL : CBLOp
  /--
    SHR: logical shift right operation
    δ:2 ; α:1
  -/
  | protected SHR : CBLOp
  /--
    SAR: arithmetical shift right operation
    δ:2 ; α:1
  -/
  | protected SAR : CBLOp
  deriving DecidableEq, Repr

/--
  Keccak operation.
-/
inductive KOp : Type where
  /--
    KECCAK256: compute KECCAK256 hash
    δ:2 ; α: 1
  -/
  | protected KECCAK256 : KOp
  deriving DecidableEq, Repr

/--
  Environment Information.
-/
inductive EOp : Type where
  /--
    ADDRESS: get the address of current executing account
    δ:0 ; α: 1
  -/
  | protected ADDRESS : EOp
  /--
    BALANCE: get the balance of an input account
    δ:1 ; α: 1
  -/
  | protected BALANCE : EOp
  /--
    ORIGIN: get execution origination address
    δ:0 ; α: 1
  -/
  | protected ORIGIN : EOp
  /--
    CALLER: returns the caller address
    δ: 0 ; α: 1
  -/
  | protected CALLER : EOp
  /--
    CALLVALUE: get deposited value by the instruction / transaction
    responsible for this execution.
    δ: 0 ; α: 1
  -/
  | protected CALLVALUE : EOp
  /--
    CALLDATALOAD: get input data of current environment
    δ: 1 ;  α: 1
  -/
  | protected CALLDATALOAD : EOp
  /--
    CALLDATASIZE: get size of input data in current environment
    δ: 0 ; α: 1
  -/
  | protected CALLDATASIZE : EOp
  /--
    CALLDATACOPY: copy input data from environment to memory
    δ: 3 ; α: 0
  -/
  | protected CALLDATACOPY : EOp
  /--
    CODESIZE: get the size of code running in current environment
    δ:0 ; α: 1
  -/
  | protected GASPRICE : EOp
  /--
    CODECOPY: Copy code running in current environment to memory
    δ: 3 ; α: 0
  -/
  | protected CODESIZE : EOp
  /--
    GASPRICE: Gas price in current execution environment
    δ: 0 ; α: 1
  -/
  | protected CODECOPY : EOp
  /--
    EXTCODESIZE: get the size of an account's code
    δ:1 ; α: 1
  -/
  | protected EXTCODESIZE : EOp
  /--
    EXTCODECOPY: copy an account's code to memory
    δ: 4 ; α: 0
  -/
  | protected EXTCODECOPY : EOp
  /--
    RETURNDATASIZE: get the size of output data from the previous call
                    from the current environment.
    δ: 0 ; α: 1
  -/
  | protected RETURNDATASIZE : EOp
  /--
    RETURNDATACOPY: copy output data from previous call to memory
    δ: 3 ; α: 0
  -/
  | protected RETURNDATACOPY : EOp
  /--
    EXTCODEHASH: get hash of an account's code
    δ: 1 ; α: 1
  -/
  | protected EXTCODEHASH : EOp
  deriving DecidableEq, Repr

/--
  Block Information.
-/
inductive BOp : Type where
  /--
    BLOCKHASH: get the hash of one of the 256 most recent blocks
    δ:1 ; α: 1
  -/
  | protected BLOCKHASH : BOp
  /--
    COINBASE: get current's block beneficiary address
    δ: 0 ; α: 1
  -/
  | protected COINBASE : BOp
  /--
    TIMESTAMP: get current block's timestamp
    δ: 0 ; α: 1
  -/
  | protected TIMESTAMP : BOp
  /--
    NUMBER: get current block's number
    δ: 0 ; α: 1
  -/
  | protected NUMBER : BOp
  | protected PREVRANDAO : BOp
  /--
    GASLIMIT: get the gas limit for the current block
    δ: 0 ; α: 1
  -/
  | protected GASLIMIT : BOp
  /--
    CHAINID: returns the chainid, β
    δ: 0 ; α: 1
  -/
  | protected CHAINID : BOp
  /--
    SELFBALANCE: get the balance of the current executing account
    δ: 0 ; α: 1
  -/
  | protected SELFBALANCE : BOp
  | protected BASEFEE : BOp
  | protected BLOBHASH : BOp
  | protected BLOBBASEFEE : BOp
  deriving DecidableEq, Repr

/--
  Stack, Memory, Storage and Flow Operations
-/
inductive SMSFOp : Type where
  /--
    POP: remove an item from the stack
    δ: 1 ; α: 0
  -/
  | protected POP : SMSFOp
  /--
    MLOAD: load word from memory
    δ: 1 ; α: 1
  -/
  | protected MLOAD : SMSFOp
  /--
    MSTORE: save word in memory
    δ: 2 ; α: 0
  -/
  | protected MSTORE : SMSFOp
  /--
    SLOAD: load word from storage
    δ: 1 ; α: 1
  -/
  | protected SLOAD : SMSFOp
  /--
    SSTORE: Save word to storage
    δ:2 ; α: 0
  -/
  | protected SSTORE : SMSFOp
  /--
    MSTORE8: save byte in memory
    δ: 2 ; α: 0
  -/
  | protected MSTORE8 : SMSFOp
  /--
    JUMP: modify program counter
    δ:1 ; α: 0
  -/
  | protected JUMP : SMSFOp
  /--
    JUMPI: conditionally modify program counter
    δ: 2 ; α: 0
  -/
  | protected JUMPI : SMSFOp
  /--
    PC: get program counter before increment
    δ: 0 ; α: 1
  -/
  | protected PC : SMSFOp
  /--
    MSIZE: get the size of active memory in bytes
    δ: 0 ; α: 1
  -/
  | protected MSIZE : SMSFOp
  /--
    GAS: get the amount of available gas
    δ: 0 ; α: 1
  -/
  | protected GAS : SMSFOp
  /--
    JUMPDEST: mark a valid destination for jumps
    δ: 0 ; α: 0
  -/
  | protected JUMPDEST : SMSFOp
  /--
    EIP-1153
    https://eips.ethereum.org/EIPS/eip-1153
    TLOAD: load word from transient memory
    δ: 1 ; α: 1
  -/
  | protected TLOAD : SMSFOp
  /--
    EIP-1153
    https://eips.ethereum.org/EIPS/eip-1153
    TSTORE: Save word to transient memory
    δ: 2 ; α: 0
  -/
  | protected TSTORE : SMSFOp
  /--
    EIPS-5656
    MCOPY: copy memory areas
    δ: 3 ; α: 0
  -/
  | protected MCOPY : SMSFOp  deriving DecidableEq, Repr

/--
  Push operations.

  PUSH0 : pushes `0` to stack.
    δ: 0 ; α: 1

  PUSHn : pushes n bytes to stack.
    δ: 0 ; α: 1
-/
inductive POp : Type where
  | protected PUSH0 : POp
  | protected PUSH1 : POp
  | protected PUSH2 : POp
  | protected PUSH3 : POp
  | protected PUSH4 : POp
  | protected PUSH5 : POp
  | protected PUSH6 : POp
  | protected PUSH7 : POp
  | protected PUSH8 : POp
  | protected PUSH9 : POp
  | protected PUSH10 : POp
  | protected PUSH11 : POp
  | protected PUSH12 : POp
  | protected PUSH13 : POp
  | protected PUSH14 : POp
  | protected PUSH15 : POp
  | protected PUSH16 : POp
  | protected PUSH17 : POp
  | protected PUSH18 : POp
  | protected PUSH19 : POp
  | protected PUSH20 : POp
  | protected PUSH21 : POp
  | protected PUSH22 : POp
  | protected PUSH23 : POp
  | protected PUSH24 : POp
  | protected PUSH25 : POp
  | protected PUSH26 : POp
  | protected PUSH27 : POp
  | protected PUSH28 : POp
  | protected PUSH29 : POp
  | protected PUSH30 : POp
  | protected PUSH31 : POp
  | protected PUSH32 : POp
  deriving DecidableEq, Repr

/--
  Duplicate Operations.

  DUPn: duplicates the nth item on the stack.
    δ: n ; α: n + 1
-/
inductive DOp : Type where
  | protected DUP1
  | protected DUP2
  | protected DUP3
  | protected DUP4
  | protected DUP5
  | protected DUP6
  | protected DUP7
  | protected DUP8
  | protected DUP9
  | protected DUP10
  | protected DUP11
  | protected DUP12
  | protected DUP13
  | protected DUP14
  | protected DUP15
  | protected DUP16
  deriving DecidableEq, Repr

/--
  Exchange Operations.

  SWAPn: swaps the 1st and nth element of the stack.
    δ: n + 1 ; α: n + 1

-/
inductive ExOp : Type where
  | protected SWAP1  : ExOp
  | protected SWAP2  : ExOp
  | protected SWAP3  : ExOp
  | protected SWAP4  : ExOp
  | protected SWAP5  : ExOp
  | protected SWAP6  : ExOp
  | protected SWAP7  : ExOp
  | protected SWAP8  : ExOp
  | protected SWAP9  : ExOp
  | protected SWAP10 : ExOp
  | protected SWAP11 : ExOp
  | protected SWAP12 : ExOp
  | protected SWAP13 : ExOp
  | protected SWAP14 : ExOp
  | protected SWAP15 : ExOp
  | protected SWAP16 : ExOp
  deriving DecidableEq, Repr

/--
  Logging Operations.

  LOGn: append log record with n topics.
    δ: n + 2 ; α : 0
-/
inductive LOp : Type where
  | protected LOG0 : LOp
  | protected LOG1 : LOp
  | protected LOG2 : LOp
  | protected LOG3 : LOp
  | protected LOG4 : LOp
  deriving DecidableEq, Repr

/--
  System Operations.
-/
inductive SOp : Type where
  /--
    CREATE: create a new account with associated code
    δ: 3 ; α: 1
  -/
  | protected CREATE : SOp
  /--
    CALL: message call into an account
    δ: 7 ; α: 1
  -/
  | protected CALL : SOp
  /--
    CALLCODE: message call into this account with an alternative account's code
    δ: 7 ; α: 1
  -/
  | protected CALLCODE : SOp
  /--
    RETURN: Halt execution returning output data
    δ: 2 ; α: 0
  -/
  | protected RETURN : SOp
  /--
    DELEGATECALL: message call into this account with an alternative account's code
                  but persisting the current values for sender and value
    δ: 6 ; α: 1
  -/
  | protected DELEGATECALL : SOp
  /--
    CREATE2: create a new account with associated code
    δ: 4 ; α: 1
  -/
  | protected CREATE2 : SOp
  /--
    STATICCALL: static message call into an account
    δ: 6 ; α: 1
  -/
  | protected STATICCALL : SOp
  /--
    REVERT: halt execution reverting state changes but returning data and remaining gas
    δ: 2 ; α: 0
  -/
  | protected REVERT : SOp
  /--
    INVALID: invalid opcode
    δ: ∅ ; α: ∅
  -/
  | protected INVALID : SOp
  /--
    SELFDESTRUCT: halt and send entire balance to target.
    Deprecated; see EIP-6780
    δ: 1 ; α: 0
  -/
  | protected SELFDESTRUCT : SOp
  deriving DecidableEq, Repr

end Operation

end Operation

open Operation

inductive Operation : Type where
  | protected StopArith    : SAOp → Operation
  | protected CompBit      : CBLOp  → Operation
  | protected Keccak       : KOp → Operation
  | protected Env          : EOp → Operation
  | protected Block        : BOp → Operation
  | protected StackMemFlow : SMSFOp → Operation
  | protected Push         : POp → Operation
  | protected Dup          : DOp → Operation
  | protected Exchange     : ExOp → Operation
  | protected Log          : LOp → Operation
  | protected System       : SOp → Operation
  deriving DecidableEq, Repr
namespace Operation

@[match_pattern]
abbrev STOP        : Operation := .StopArith .STOP
abbrev ADD         : Operation := .StopArith .ADD
abbrev MUL         : Operation := .StopArith .MUL
abbrev SUB         : Operation := .StopArith .SUB
abbrev DIV         : Operation := .StopArith .DIV
abbrev SDIV        : Operation := .StopArith .SDIV
abbrev MOD         : Operation := .StopArith .MOD
abbrev SMOD        : Operation := .StopArith .SMOD
abbrev ADDMOD      : Operation := .StopArith .ADDMOD
abbrev MULMOD      : Operation := .StopArith .MULMOD
abbrev EXP         : Operation := .StopArith .EXP
abbrev SIGNEXTEND  : Operation := .StopArith .SIGNEXTEND

abbrev LT      : Operation := .CompBit .LT
abbrev GT      : Operation := .CompBit .GT
abbrev SLT     : Operation := .CompBit .SLT
abbrev SGT     : Operation := .CompBit .SGT
abbrev EQ      : Operation := .CompBit .EQ
abbrev ISZERO  : Operation := .CompBit .ISZERO
abbrev AND     : Operation := .CompBit .AND
abbrev OR      : Operation := .CompBit .OR
abbrev XOR     : Operation := .CompBit .XOR
abbrev NOT     : Operation := .CompBit .NOT
abbrev BYTE    : Operation := .CompBit .BYTE
abbrev SHL     : Operation := .CompBit .SHL
abbrev SHR     : Operation := .CompBit .SHR
abbrev SAR     : Operation := .CompBit .SAR

abbrev KECCAK256  : Operation := .Keccak .KECCAK256

abbrev ADDRESS         : Operation := .Env .ADDRESS
abbrev BALANCE         : Operation := .Env .BALANCE
abbrev ORIGIN          : Operation := .Env .ORIGIN
abbrev CALLER          : Operation := .Env .CALLER
abbrev CALLVALUE       : Operation := .Env .CALLVALUE
abbrev CALLDATALOAD    : Operation := .Env .CALLDATALOAD
abbrev CALLDATASIZE    : Operation := .Env .CALLDATASIZE
abbrev CALLDATACOPY    : Operation := .Env .CALLDATACOPY
abbrev CODESIZE        : Operation := .Env .CODESIZE
abbrev GASPRICE        : Operation := .Env .GASPRICE
abbrev CODECOPY        : Operation := .Env .CODECOPY
abbrev EXTCODECOPY     : Operation := .Env .EXTCODECOPY
abbrev EXTCODESIZE     : Operation := .Env .EXTCODESIZE
abbrev RETURNDATASIZE  : Operation := .Env .RETURNDATASIZE
abbrev RETURNDATACOPY  : Operation := .Env .RETURNDATACOPY
abbrev EXTCODEHASH     : Operation := .Env .EXTCODEHASH

abbrev BLOCKHASH    : Operation := .Block .BLOCKHASH
abbrev COINBASE     : Operation := .Block .COINBASE
abbrev TIMESTAMP    : Operation := .Block .TIMESTAMP
abbrev NUMBER       : Operation := .Block .NUMBER
abbrev PREVRANDAO   : Operation := .Block .PREVRANDAO
abbrev GASLIMIT     : Operation := .Block .GASLIMIT
abbrev CHAINID      : Operation := .Block .CHAINID
abbrev SELFBALANCE  : Operation := .Block .SELFBALANCE
abbrev BASEFEE      : Operation := .Block .BASEFEE
abbrev BLOBHASH     : Operation := .Block .BLOBHASH
abbrev BLOBBASEFEE  : Operation := .Block .BLOBBASEFEE

abbrev POP        : Operation    := .StackMemFlow .POP
abbrev MLOAD      : Operation    := .StackMemFlow .MLOAD
abbrev MSTORE     : Operation    := .StackMemFlow .MSTORE
abbrev SLOAD      : Operation    := .StackMemFlow .SLOAD
abbrev SSTORE     : Operation    := .StackMemFlow .SSTORE
abbrev MSTORE8    : Operation    := .StackMemFlow .MSTORE8
abbrev JUMP                          : Operation := .StackMemFlow .JUMP
abbrev JUMPI                         : Operation := .StackMemFlow .JUMPI
abbrev PC                            : Operation    := .StackMemFlow .PC
abbrev MSIZE      : Operation    := .StackMemFlow .MSIZE
abbrev GAS        : Operation    := .StackMemFlow .GAS
abbrev JUMPDEST                      : Operation := .StackMemFlow .JUMPDEST
abbrev TLOAD    : Operation    := .StackMemFlow .TLOAD
abbrev TSTORE   : Operation    := .StackMemFlow .TSTORE
abbrev MCOPY    : Operation := .StackMemFlow .MCOPY

abbrev PUSH0  : Operation := .Push .PUSH0
abbrev PUSH1  : Operation := .Push .PUSH1
abbrev PUSH2  : Operation := .Push .PUSH2
abbrev PUSH3  : Operation := .Push .PUSH3
abbrev PUSH4  : Operation := .Push .PUSH4
abbrev PUSH5  : Operation := .Push .PUSH5
abbrev PUSH6  : Operation := .Push .PUSH6
abbrev PUSH7  : Operation := .Push .PUSH7
abbrev PUSH8  : Operation := .Push .PUSH8
abbrev PUSH9  : Operation := .Push .PUSH9
abbrev PUSH10 : Operation := .Push .PUSH10
abbrev PUSH11 : Operation := .Push .PUSH11
abbrev PUSH12 : Operation := .Push .PUSH12
abbrev PUSH13 : Operation := .Push .PUSH13
abbrev PUSH14 : Operation := .Push .PUSH14
abbrev PUSH15 : Operation := .Push .PUSH15
abbrev PUSH16 : Operation := .Push .PUSH16
abbrev PUSH17 : Operation := .Push .PUSH17
abbrev PUSH18 : Operation := .Push .PUSH18
abbrev PUSH19 : Operation := .Push .PUSH19
abbrev PUSH20 : Operation := .Push .PUSH20
abbrev PUSH21 : Operation := .Push .PUSH21
abbrev PUSH22 : Operation := .Push .PUSH22
abbrev PUSH23 : Operation := .Push .PUSH23
abbrev PUSH24 : Operation := .Push .PUSH24
abbrev PUSH25 : Operation := .Push .PUSH25
abbrev PUSH26 : Operation := .Push .PUSH26
abbrev PUSH27 : Operation := .Push .PUSH27
abbrev PUSH28 : Operation := .Push .PUSH28
abbrev PUSH29 : Operation := .Push .PUSH29
abbrev PUSH30 : Operation := .Push .PUSH30
abbrev PUSH31 : Operation := .Push .PUSH31
abbrev PUSH32 : Operation := .Push .PUSH32

abbrev DUP1  : Operation := .Dup .DUP1
abbrev DUP2  : Operation := .Dup .DUP2
abbrev DUP3  : Operation := .Dup .DUP3
abbrev DUP4  : Operation := .Dup .DUP4
abbrev DUP5  : Operation := .Dup .DUP5
abbrev DUP6  : Operation := .Dup .DUP6
abbrev DUP7  : Operation := .Dup .DUP7
abbrev DUP8  : Operation := .Dup .DUP8
abbrev DUP9  : Operation := .Dup .DUP9
abbrev DUP10 : Operation := .Dup .DUP10
abbrev DUP11 : Operation := .Dup .DUP11
abbrev DUP12 : Operation := .Dup .DUP12
abbrev DUP13 : Operation := .Dup .DUP13
abbrev DUP14 : Operation := .Dup .DUP14
abbrev DUP15 : Operation := .Dup .DUP15
abbrev DUP16 : Operation := .Dup .DUP16

abbrev SWAP1  : Operation := .Exchange .SWAP1
abbrev SWAP2  : Operation := .Exchange .SWAP2
abbrev SWAP3  : Operation := .Exchange .SWAP3
abbrev SWAP4  : Operation := .Exchange .SWAP4
abbrev SWAP5  : Operation := .Exchange .SWAP5
abbrev SWAP6  : Operation := .Exchange .SWAP6
abbrev SWAP7  : Operation := .Exchange .SWAP7
abbrev SWAP8  : Operation := .Exchange .SWAP8
abbrev SWAP9  : Operation := .Exchange .SWAP9
abbrev SWAP10 : Operation := .Exchange .SWAP10
abbrev SWAP11 : Operation := .Exchange .SWAP11
abbrev SWAP12 : Operation := .Exchange .SWAP12
abbrev SWAP13 : Operation := .Exchange .SWAP13
abbrev SWAP14 : Operation := .Exchange .SWAP14
abbrev SWAP15 : Operation := .Exchange .SWAP15
abbrev SWAP16 : Operation := .Exchange .SWAP16

abbrev LOG0  : Operation := .Log .LOG0
abbrev LOG1  : Operation := .Log .LOG1
abbrev LOG2  : Operation := .Log .LOG2
abbrev LOG3  : Operation := .Log .LOG3
abbrev LOG4  : Operation := .Log .LOG4

abbrev CREATE        : Operation := .System .CREATE
abbrev CALL          : Operation := .System .CALL
abbrev CALLCODE      : Operation := .System .CALLCODE
abbrev RETURN        : Operation := .System .RETURN
abbrev DELEGATECALL  : Operation := .System .DELEGATECALL
abbrev CREATE2       : Operation := .System .CREATE2
abbrev STATICCALL    : Operation := .System .STATICCALL
abbrev REVERT        : Operation := .System .REVERT
abbrev INVALID       : Operation := .System .INVALID
abbrev SELFDESTRUCT  : Operation := .System .SELFDESTRUCT

def isPush  : Operation → Bool
  | .Push _ => true
  | _ => false

def isJump  : Operation → Bool
  | .JUMP => true
  | .JUMPI => true
  | _ => false

def isPC  : Operation → Bool
  | .PC => true
  | _ => false

def isJumpdest  : Operation → Bool
  | .JUMPDEST => true
  | _ => false

def isDup  : Operation → Bool
  | .Dup _ => true
  | _ => false

def isSwap  : Operation → Bool
  | .Exchange _ => true
  | _ => false

def isCreate  : Operation → Bool
  | .CREATE => true
  | .CREATE2 => true
  | _ => false

def isCall  : Operation → Bool
  | .CALL => true
  | .CALLCODE => true
  | .DELEGATECALL => true
  | .STATICCALL => true
  | _ => false


end Operation

open Ethereum.UInt256

def exp (a b : UInt256) : UInt256 :=
  a ^ b

abbrev fromBool := Bool.toUInt256

def lt (a b : UInt256) :=
  fromBool (a < b)

def gt (a b : UInt256) :=
  fromBool (a > b)

-- def slt (a b : UInt256) :=
--   fromBool (Ethereum.UInt256.slt a b)

-- def sgt (a b : UInt256) :=
--   fromBool (Ethereum.UInt256.sgt a b)

def eq (a b : UInt256) :=
  fromBool (a = b)

def isZero (a : UInt256) :=
  fromBool (eq0 a)

end Ethereum

open Ethereum
