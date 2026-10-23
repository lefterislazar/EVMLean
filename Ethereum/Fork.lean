/-!
# Execution-layer forks

The semantics is parametric in the active execution-layer fork. A `Fork` is
carried in the execution environment (`ExecutionEnv.fork`) and passed
explicitly to the message-call (`Θ`), contract-creation (`Lambda`) and
transaction (`Υ`) functions.

Fork-dependent rules do not compare forks. Each one tests the flag of the EIP
that introduced it in `Fork.spec`, the `ForkSpec` of the fork, for example
`fork.spec.eip7702`. The table `Fork.spec` is the single place that says which
EIPs a fork enables. `Fork.spec_monotone` checks that a later fork never
disables an EIP enabled by an earlier one.

Only the forks from Cancun onward are modelled.
-/

namespace Ethereum

/-- Execution-layer forks supported by the model, in activation order. -/
inductive Fork where
  | cancun
  | prague
  | osaka
  /-- Blob-parameter-only forks (EIP-7892). They differ from Osaka only in
      their blob schedule. -/
  | bpo1
  | bpo2
  | bpo3
  | bpo4
deriving BEq, DecidableEq, Inhabited, Repr

namespace Fork

/-- Position of the fork in activation order. -/
def rank : Fork → Nat
  | .cancun => 0
  | .prague => 1
  | .osaka => 2
  | .bpo1 => 3
  | .bpo2 => 4
  | .bpo3 => 5
  | .bpo4 => 6

instance : LE Fork := ⟨fun a b => a.rank ≤ b.rank⟩
instance : LT Fork := ⟨fun a b => a.rank < b.rank⟩

instance (a b : Fork) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.rank ≤ b.rank))
instance (a b : Fork) : Decidable (a < b) := inferInstanceAs (Decidable (a.rank < b.rank))

theorem le_def {a b : Fork} : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

@[simp] theorem cancun_le (f : Fork) : Fork.cancun ≤ f := Nat.zero_le _

def all : List Fork := [.cancun, .prague, .osaka, .bpo1, .bpo2, .bpo3, .bpo4]

/-- The fork names used by the `ethereum/execution-spec-tests` fixtures. -/
def name : Fork → String
  | .cancun => "Cancun"
  | .prague => "Prague"
  | .osaka => "Osaka"
  | .bpo1 => "BPO1"
  | .bpo2 => "BPO2"
  | .bpo3 => "BPO3"
  | .bpo4 => "BPO4"

def parse? (s : String) : Option Fork := all.find? (·.name == s)

end Fork

/-- A fixed fork, or a network that switches fork at a block timestamp. -/
inductive ForkNetwork where
  | fixed (fork : Fork)
  | transition (before after : Fork) (timestamp : Nat)
deriving BEq, DecidableEq, Inhabited, Repr

namespace ForkNetwork

def activeFork : ForkNetwork → Nat → Fork
  | .fixed fork, _ => fork
  | .transition before after activation, timestamp =>
      if timestamp < activation then before else after

/-- Parses fixture network names such as `Prague` or `PragueToOsakaAtTime15k`. -/
def parse? (s : String) : Option ForkNetwork :=
  match Fork.parse? s with
  | some fork => some (.fixed fork)
  | none => Id.run do
    for before in Fork.all do
      for after in Fork.all do
        if s == before.name ++ "To" ++ after.name ++ "AtTime15k" then
          return some (.transition before after 15000)
    return none

end ForkNetwork

def GAS_PER_BLOB : Nat := 2 ^ 17

/-- Blob parameters of a fork (EIP-7840). -/
structure BlobSchedule where
  targetBlobs : Nat
  maxBlobs : Nat
  baseFeeUpdateFraction : Nat
deriving BEq, DecidableEq, Inhabited, Repr

namespace BlobSchedule

def targetBlobGas (schedule : BlobSchedule) : Nat := schedule.targetBlobs * GAS_PER_BLOB
def maxBlobGas (schedule : BlobSchedule) : Nat := schedule.maxBlobs * GAS_PER_BLOB

end BlobSchedule

/--
The rules of a fork: one flag for each EIP after Cancun that changes the
execution layer, and the blob schedule. Every flag defaults to `false`, so the
Cancun rules are the record with no flag set.
-/
structure ForkSpec where
  -- Prague
  /-- EIP-2537: the BLS12-381 precompiles at `0x0b` to `0x11`. -/
  eip2537 : Bool := false
  /-- EIP-2935: the parent block hash is stored by a system call. -/
  eip2935 : Bool := false
  /-- EIP-7623: the calldata floor on the gas a transaction is charged. -/
  eip7623 : Bool := false
  /-- EIP-7685: execution-layer requests in the block header. The requests
      are the EIP-6110 deposits, the EIP-7002 withdrawals and the EIP-7251
      consolidations. -/
  eip7685 : Bool := false
  /-- EIP-7702: set-code transactions and delegation designators. -/
  eip7702 : Bool := false
  -- Osaka
  /-- EIP-7594: at most 6 blobs per transaction. -/
  eip7594 : Bool := false
  /-- EIP-7823: `EXPMOD` input lengths are bounded by 1024 bytes. -/
  eip7823 : Bool := false
  /-- EIP-7825: the transaction gas limit is capped at `2 ^ 24`. -/
  eip7825 : Bool := false
  /-- EIP-7883: the `EXPMOD` repricing. -/
  eip7883 : Bool := false
  /-- EIP-7918: the blob base fee is bounded below by execution costs. -/
  eip7918 : Bool := false
  /-- EIP-7934: the RLP-encoded block size limit. -/
  eip7934 : Bool := false
  /-- EIP-7939: the `CLZ` instruction. -/
  eip7939 : Bool := false
  /-- EIP-7951: the secp256r1 verifier precompile at `0x100`. -/
  eip7951 : Bool := false
  /-- The blob schedule. Its changes (EIP-7691 in Prague, the BPO forks of
      EIP-7892) need no flag. -/
  blobSchedule : BlobSchedule
deriving BEq, DecidableEq, Repr

namespace ForkSpec

/-- The EIP flags of a spec. Keep in sync with the fields of `ForkSpec`. -/
def flags (s : ForkSpec) : List Bool :=
  [ s.eip2537, s.eip2935, s.eip7623, s.eip7685, s.eip7702
  , s.eip7594, s.eip7823, s.eip7825, s.eip7883, s.eip7918, s.eip7934, s.eip7939, s.eip7951 ]

/-- Every EIP enabled in `a` is enabled in `b`. -/
def Extends (b a : ForkSpec) : Prop :=
  (a.flags.zip b.flags).all (fun (x, y) => !x || y) = true

instance (b a : ForkSpec) : Decidable (b.Extends a) := inferInstanceAs (Decidable (_ = _))

def cancun : ForkSpec where
  blobSchedule := ⟨3, 6, 3338477⟩

def prague : ForkSpec :=
  { cancun with
    eip2537 := true
    eip2935 := true
    eip7623 := true
    eip7685 := true
    eip7702 := true
    -- EIP-7691
    blobSchedule := ⟨6, 9, 5007716⟩ }

def osaka : ForkSpec :=
  { prague with
    eip7594 := true
    eip7823 := true
    eip7825 := true
    eip7883 := true
    eip7918 := true
    eip7934 := true
    eip7939 := true
    eip7951 := true }

end ForkSpec

namespace Fork

/-- The rules of each fork. The BPO forks (EIP-7892) are Osaka with another
    blob schedule. BPO1 and BPO2 are the mainnet values. BPO3 and BPO4 are
    test-only forks, with the values used by the `execution-spec-tests`
    fixtures. -/
def spec : Fork → ForkSpec
  | .cancun => .cancun
  | .prague => .prague
  | .osaka => .osaka
  | .bpo1 => { ForkSpec.osaka with blobSchedule := ⟨10, 15, 8346193⟩ }
  | .bpo2 => { ForkSpec.osaka with blobSchedule := ⟨14, 21, 11684671⟩ }
  | .bpo3 => { ForkSpec.osaka with blobSchedule := ⟨21, 32, 20609697⟩ }
  | .bpo4 => { ForkSpec.osaka with blobSchedule := ⟨14, 21, 13739630⟩ }

/-- A later fork enables every EIP of an earlier one. -/
theorem spec_monotone {a b : Fork} (h : a ≤ b) : b.spec.Extends a.spec := by
  revert h
  cases a <;> cases b <;> decide

/-- The EIP-7883 `EXPMOD` pricing only applies together with the EIP-7823
    input bounds. -/
theorem eip7823_of_eip7883 {fork : Fork} (h : fork.spec.eip7883 = true) :
    fork.spec.eip7823 = true := by
  revert h
  cases fork <;> decide

end Fork

/-- Chain configuration: the fork schedule and the chain id. -/
structure ChainConfig where
  network : ForkNetwork
  chainId : Nat := 1
deriving BEq, Inhabited, Repr

namespace ChainConfig

def activeFork (config : ChainConfig) (timestamp : Nat) : Fork :=
  config.network.activeFork timestamp

end ChainConfig

end Ethereum
