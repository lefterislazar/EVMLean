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
| [8024] | `DUPN`, `SWAPN`, `EXCHANGE` | Implemented (flag `eip8024`)¹ |
| [7843] | `SLOTNUM`, header `slotNumber` | Implemented (flag `eip7843`)¹ |
| [7928] | Block-level access lists, header `blockAccessListHash` | Header field parsed; flag `eip7928` off |
| [2780] | Resource-based intrinsic transaction gas | Planned, with the gas meter |
| [7976] | Calldata floor cost | Planned, with the gas meter |
| [7981] | Access list cost | Planned, with the gas meter |
| [8037] | State creation gas: the state-gas dimension | Planned: the gas meter |
| [8038] | State-access gas cost update | Planned, with the gas meter |
| [7778] | Block gas accounting without refunds | Planned, after the gas meter |
| [7708] | ETH transfers emit a log | Planned |
| [7954] | Maximum contract size `0x10000` | Planned: the limits become functions of the fork, also in the ~30 proof statements that restate them |
| [8246] | `SELFDESTRUCT` no longer burns | Planned |
| [8282] | Builder execution requests | Planned |
| [7997] | Deterministic factory contract | Not in EELS at `tests@v21.0.2`: nothing to model yet |

¹ The fixtures cannot check these fully yet: all but one of the state tests
of each exceed the old `2^24` transaction gas cap, which EIP-8037 lifts. In
the remaining one, `test_stack_access_opcodes_mainnet` and
`test_slotnum_mainnet`, the stored results match; only the sender's fee
differs, by the gas of the EIPs below. The EIP-8024 immediate decoders also
agree with EELS on all 256 immediates.

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

The state-test runner (`Conform/Run.lean`, `runStateCase`) passes all 14,665
Osaka state-test cases. With no Amsterdam gas changes yet, 1,593 of the 16,908
Amsterdam state-test cases pass. Most failures are
`GAS_LIMIT_EXCEEDS_MAXIMUM`: Amsterdam transactions may exceed the EIP-7825
cap of `2^24` gas, which EIP-8037 applies to execution gas only. Most of the
others are `INTRINSIC_GAS_TOO_LOW` (EIP-2780, 7976 and 7981) and post-states
that the gas changes of EIP-8037 and 8038 explain.

## The gas meter (EIP-8037, with 2780, 7976, 7981 and 8038)

These five EIPs are entangled in EELS, and nearly every Amsterdam test depends
on all of them. They change how gas flows through frames, so they are one
step, designed before it is written.

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

Gas is a single `UInt256` (`MachineState.gasAvailable`) threaded through `Ξ`,
`Θ`, `Lambda` and `Υ`, and `Ethereum/Theory` proves facts about it
(`GasLemmas`, `NoOutOfFuel` and the frame lemmas). A single counter cannot
express EIP-8037 even with an empty reservoir: a reverted child gets its
spill back, and state credits bypass the refund cap. The plan:

1. A `GasMeter` structure in `MachineState`, with the EELS fields and
   operations (`chargeGas`, `chargeStateGas`, `restoreStateGas`,
   `creditStateGasRefund`, `repayStateGasSpill`, ...) as functions with their
   own lemmas. Before Amsterdam, every state charge is zero, so the meter
   reduces to the current counter; the existing lemmas are restated through
   it.
2. Frames: `Θ` and `Lambda` take and return a meter. The child drains the
   parent's reservoir, and the parent incorporates the child as EELS does,
   distinguishing success, revert and exceptional halt.
3. The charge sites, each under its flag: `SSTORE`, `CALL` with value to a
   new account, `CREATE` and `CREATE2`, the code deposit, `SELFDESTRUCT`, the
   top-level creation and value transfer, and the EIP-7702 authorizations
   (`set_delegation`, `commit_state_gas`).
4. `Υ`: the intrinsic cost, the split, and settlement; then the block counters
   of EIP-7778 in `Ethereum/Block.lean`.

The state tests check each step: the `GAS_LIMIT_EXCEEDS_MAXIMUM` and
`INTRINSIC_GAS_TOO_LOW` failures go first, then the gas-cost mismatches.

## The other EIPs

- **EIP-7843**: opcode `0x4B`, gas 2, pushes the header's slot number.
- **EIP-7954**: `MAX_CODE_SIZE` `0x10000`, `MAX_INIT_CODE_SIZE` `0x20000`.
- **EIP-8246**: a contract created and destroyed in the same transaction keeps
  its balance; at the end of the transaction its nonce, code and storage are
  cleared, and the account is deleted if it is then empty.
- **EIP-7708**: a value transfer from one account to another in `CALL`,
  `CREATE`, `CREATE2`, the transaction itself, and `SELFDESTRUCT` to another
  account, logs `Transfer(from, to, value)` from `0xff…fe`, before the
  callee's own logs. Nothing is logged for zero, `CALLCODE`, `DELEGATECALL`,
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
