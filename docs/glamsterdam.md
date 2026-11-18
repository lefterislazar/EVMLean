# Amsterdam (Glamsterdam)

Status and plan for the Amsterdam execution-layer fork, [EIP-7773]. The
reference is the Python execution specs (EELS) at the release the fixtures are
pinned to, `tests@v21.0.2`: `src/ethereum/forks/amsterdam`, compared with
`src/ethereum/forks/bpo2`.

The model gains an EIP's rules together with its `ForkSpec` flag
(`Ethereum/Fork.lean`). `ForkSpec.amsterdam` enables only the EIPs implemented
so far, so the model never claims a rule that it lacks; until all of them are,
the Amsterdam fixtures are not part of the default conformance run.

## Status

| EIP | Change | Status |
|---|---|---|
| [8024] | `DUPN`, `SWAPN`, `EXCHANGE` | Implemented (flag `eip8024`) |
| [7843] | `SLOTNUM`, header `slotNumber` | Implemented (flag `eip7843`) |
| [2780] | Resource-based intrinsic transaction gas | Implemented (flag `eip2780`) |
| [7976] | Calldata floor cost | Implemented (flag `eip7976`) |
| [7981] | Access list cost | Implemented (flag `eip7981`) |
| [8037] | State creation gas: the state-gas dimension | Implemented (flag `eip8037`) |
| [8038] | State-access gas cost update | Implemented (flag `eip8038`) |
| [7778] | Block gas accounting without refunds | Implemented (flag `eip7778`) |
| [7708] | ETH transfers emit a log | Implemented (flag `eip7708`) |
| [7954] | Maximum contract size `0x10000` | Implemented (flag `eip7954`) |
| [8246] | `SELFDESTRUCT` no longer burns | Implemented (flag `eip8246`) |
| [8282] | Builder execution requests | Implemented (flag `eip8282`); checked by the blockchain tests only, after EIP-7928 |
| [7928] | Block-level access lists, header `blockAccessListHash` | Header field parsed; flag `eip7928` off |
| [7997] | Deterministic factory contract | Not in EELS at `tests@v21.0.2`: nothing to model yet |

All 16,908 Amsterdam state-test cases pass. The blockchain tests need
EIP-7928: every Amsterdam header commits to the block's access list.

## Forks

The fork order is that of EELS: Cancun, Prague, Osaka, BPO1, BPO2,
Amsterdam. EELS also has `bpo3` to `bpo5`, unscheduled placeholders with the
BPO2 blob schedule; the model's former test-only BPO3 and BPO4, whose
parameters came from the `tests@v20.0.2` fixtures, were removed. The fixtures'
test-only `AmsterdamBPOIncrease` and `AmsterdamBPODecrease` networks are not
modelled.

## Validation

Every Amsterdam block header commits to the block's access list (EIP-7928), so
no Amsterdam blockchain test can pass before EIP-7928 is implemented. The state
tests run a single transaction on a pre-state and check the state root, the
logs and the post-state, without a header: they validate the transaction-level
EIPs one at a time.

```
lake test -- --state-tests --dirs for_amsterdam
lake test -- --dirs for_amsterdam,for_bpo2toamsterdamattime15k
```

The state-test runner (`Conform/Run.lean`, `runStateCase`) passes all 40,162
state-test cases of Cancun, Prague and Osaka, and all 16,908 of Amsterdam;
the blockchain tests of the earlier forks (47,436 cases) all pass. Before the
gas changes, 1,593 Amsterdam cases passed; with the gas meter alone, 11,421.

## The gas meter (EIP-8037, with 2780, 7976, 7981 and 8038)

These five EIPs are entangled in EELS, and nearly every Amsterdam test depends
on all of them. They change how gas flows through frames.

### What EELS does

- **Intrinsic gas** (`transactions.py`, `calculate_intrinsic_cost`). The
  execution part is `TX_BASE` (12000), plus a recipient charge, plus calldata,
  access list and authorization costs. The recipient charge is `CREATE_ACCESS`
  (12000) for a creation, and 3000 for a call to another account, plus
  `TX_VALUE_COST` (6000) when value moves; a self-transfer pays none. The
  access list adds a data surcharge of `(80 + 128 * slots) * 16` per entry
  (EIP-7981). Authorizations cost 7816 each. The calldata floor is
  `TX_BASE + recipient + 64 * len(data) + surcharge` (EIP-7976).
- **Validation** (`validate_transaction`): the gas limit is bounded by
  `TX_MAX_TOTAL_GAS_LIMIT` (`2^32 - 1`). The EIP-7825 cap of `2^24` bounds the
  intrinsic execution gas and the floor, not the gas limit. Blob and set-code
  checks move here, and the order of the checks changes.
- **The split** (`allocate_evm_gas`): of `tx.gas - intrinsic`, at most
  `2^24 - intrinsic` is the execution grant; the rest is the state-gas
  reservoir. Below `2^24` gas the reservoir is empty.
- **The meter** (`vm/gas.py`, `GasMeter`): each frame has `gas_left`, a
  reservoir `state_gas_left`, a `state_gas_baseline` that a rollback refills
  the reservoir to, the refund counter, and the state gas "spilled" into
  `gas_left` once the reservoir is empty. State charges (`STORAGE_SET` 97920,
  `NEW_ACCOUNT` 183600, `AUTH_BASE` 35190, 1530 per deposited code byte) draw
  from the reservoir, then spill. A child receives the whole reservoir (no
  63/64 rule). A reverted or halted child gives its spill back and resets its
  reservoir to the baseline; a successful merge repays outstanding spill from
  the reservoir. Some state refunds (a storage slot restored to zero, a
  failed account creation) are credits, last in first out, outside the refund
  counter and its 1/5 cap.
- **Repricing (EIP-8038)**: `COLD_ACCOUNT_ACCESS` 3000; `STORAGE_WRITE` 10000
  replaces the 20000/5000 store costs, whose new-slot part is now state gas;
  `CALL_VALUE` 11300; `EXTCODESIZE` and `EXTCODECOPY` add a 100 code read;
  `SSTORE` always charges its access cost; storage-clear refund 11616.
- **Settlement** (`settle_transaction_gas`): the sender pays
  `max(used - refund, floor)`; the block counts execution and state gas
  separately, before refunds (EIP-7778), and the header's `gasUsed` is their
  maximum.

### In the model

The execution gas stays a single counter (`MachineState.gasAvailable`)
threaded through `Ξ`, `Θ`, `Lambda` and `Υ`. The rest of the EELS meter is
placed where the model already gives it the right lifetime, so that `Θ` and
`Lambda` keep their signatures:

- **The reservoir and the spill** are in the substate
  (`Substate.stateGasReservoir`, `Substate.stateGasSpilled`). A child frame
  receives the substate, so it receives the whole reservoir, and a failed
  child returns its caller's substate, which is EELS's rollback to the
  baseline (`restore_state_gas`). The spill is cumulative over the
  transaction's frames; a frame records its value at entry
  (`ExecutionEnv.stateGasSpillBaseline`), and its own spill is the excess.
- **The operations** are those of `vm/gas.py`, on the execution gas and the
  substate (`Ethereum/StateGas.lean`: `charge`, `credit`, `repaySpill`), and on
  a frame's state (`chargeStateGas`, `creditStateGas`, `repayStateGasSpill` in
  `Ethereum/Semantics.lean`). A charge that the reservoir and the execution
  gas do not cover is an exceptional halt.
- **Frames**: a reverted frame returns its execution gas and its own spill
  (`revertGas`). After a child that succeeded, the caller repays its spill
  from the reservoir. `CALL` with value to a dead account and `CREATE` at a
  dead address charge `NEW_ACCOUNT` before the callee's gas is computed (the
  call's gas cap subtracts the spill, `CcallStateSpill`), and credit it back
  when no account was created; a colliding creation keeps it, as in EELS.
- **The charge sites**: `SSTORE` (`sstoreStateGas`: `STORAGE_SET` on the
  first set of a slot that was zero, credited back when it is cleared again),
  `SELFDESTRUCT` to a dead account, the code deposit in `Lambda` (hashing in
  execution gas, 1530 per byte in state gas), and the transaction's top frame:
  `Θ` and `Lambda` at depth 0 charge what EELS's `create_evm` does (the
  created account or recipient, a delegation's access).
- **Execution prices** (EIP-8038, and EIP-8037's removal of the old creation
  charges) are in the cost functions of `Ethereum/Gas.lean`, each under its
  flag: `Gcoldaccount`, `Csstore`, `Cselfdestruct`, `Cxfer`, `Cnew`,
  `Ccreate`, `Ccoderead`; the refunds in `State.sstore`.
- **The transaction** (`ΥAmsterdam`): the intrinsic cost (`intrinsicCost`,
  EIP-2780, 7976, 7981), the split into execution grant and reservoir, the
  authorizations charging the meter (`applyAuthorizationsAmsterdam`), whose
  charges survive a failure of the frame, a failure before the frame runs
  (the delegations undone, the execution gas spent, the reservoir whole), and
  settlement. `validateTransactionAmsterdam` has EELS's checks and their
  order. The block counts execution and state gas (EIP-7778,
  `executionGasUsedInBlock`, `stateGasUsedInBlock`), and the header's
  `gasUsed` is their maximum.

Each EIP's rule is under its own flag, following the split of the EIPs:
EIP-8038 reprices execution gas (cold account access, `ACCOUNT_WRITE`,
`STORAGE_WRITE`, `CREATE_ACCESS`, the clear refund, the code read), and
EIP-8037 moves `GAS_CREATE`, `GAS_NEW_ACCOUNT`, `GAS_STORAGE_SET` and the code
deposit into state gas. EIP-8037 requires EIP-8038 and EIP-2780, and the
model defines the meter only with all three.

A system call runs its contract as a transaction's top frame, with a
reservoir for 16 storage slots (`StateGas.SYSTEM_RESERVOIR`), as EELS's
`process_unchecked_system_transaction`.

One ordering differs from EELS without changing any outcome: `SSTORE` checks
its execution cost before crediting `STORAGE_SET`, where EELS credits first.
Both need more than the 2300 stipend, which exceeds that cost whenever a
credit happens.

### The proofs

A frame's gas can now increase: a revert returns its spill, an `SSTORE` that
clears a slot set from spilled gas credits it back, and a parent repays its
spill after a successful child. What never increases is the frame's gas
together with its own spill, `frameGas` (`Ethereum/Theory/GasLemmas.lean`):
state charges, credits and repayments move gas between the two, and every
step that continues spends some of it. Inside a frame the spill never falls
below its value at entry. The gas theorems are restated with it:
`Xstep_gas_decreases_of_continues` and the fuel bound of `NoOutOfFuel` speak
of `frameGas`, and a call's bound needs its callee's, so `childGasBound`
proves by induction on the depth that `Θ` and `Lambda` return at most the
gas and spill they were given (`Theta_gas_le` keeps its statement). `Ξ` gives
`X` one more step of fuel than the frame's gas counting the spill of its
entry charges, which it can get back. `memoryPaidByGas` (`ReturnDataBound`)
bounds memory with `frameGas`.

## The other EIPs

- **EIP-7843**: opcode `0x4B`, gas 2, pushes the header's slot number.
- **EIP-7954**: the largest code `0x10000` and init code `0x20000`, as
  `Fork.maxCodeSize` and `Fork.maxInitCodeSize`.
- **EIP-8246**: a `SELFDESTRUCT` to itself no longer burns the balance. A
  contract created and destroyed in the same transaction keeps its balance:
  at the end of the transaction its nonce, code and storage are cleared, and
  the account is deleted if it is then empty (`destroyAccounts`).
- **EIP-7708**: a value transfer from one account to another in `CALL`,
  `CREATE`, `CREATE2`, the transaction itself, and `SELFDESTRUCT` to another
  account, logs `Transfer(from, to, value)` from `0xff…fe`
  (`LogEntry.transfer`). `Θ` and `Lambda` add the log to the substate the
  callee starts with, so it precedes the callee's own logs and is discarded
  with them when the callee fails. Nothing is logged for zero, `CALLCODE`
  (sender and recipient are the same), `DELEGATECALL` (no transfer),
  withdrawals or fees.
- **EIP-8282**: two more checked system calls after the consolidation
  requests, to `0x0000BFF4…8282` (request type 3) and `0x000064D6…8282`
  (type 4).
- **EIP-7928**: the state layer records the accounts and storage slots read
  (reads survive reverts) and the post-transaction balance, nonce, code and
  storage changes, by index: 0 for the system calls before the transactions,
  `i + 1` for transaction `i`, `n + 1` for withdrawals and requests. The list
  is sorted and RLP-encoded, and its hash is checked against the header, as is
  the item limit `gas_limit / 2000`. It changes no state or gas, so it comes
  after the gas meter; it needs EELS's ordering of gas checks before state
  reads, so that a failed check records no read.

[EIP-7773]: https://eips.ethereum.org/EIPS/eip-7773
[2780]: https://eips.ethereum.org/EIPS/eip-2780
[7708]: https://eips.ethereum.org/EIPS/eip-7708
[7778]: https://eips.ethereum.org/EIPS/eip-7778
[7843]: https://eips.ethereum.org/EIPS/eip-7843
[7928]: https://eips.ethereum.org/EIPS/eip-7928
[7954]: https://eips.ethereum.org/EIPS/eip-7954
[7976]: https://eips.ethereum.org/EIPS/eip-7976
[7981]: https://eips.ethereum.org/EIPS/eip-7981
[7997]: https://eips.ethereum.org/EIPS/eip-7997
[8024]: https://eips.ethereum.org/EIPS/eip-8024
[8037]: https://eips.ethereum.org/EIPS/eip-8037
[8038]: https://eips.ethereum.org/EIPS/eip-8038
[8246]: https://eips.ethereum.org/EIPS/eip-8246
[8282]: https://eips.ethereum.org/EIPS/eip-8282
