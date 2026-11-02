This repository contains a formal model of the EVM in Lean 4.
It is an EVM-focused port of Nethermind's
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean) to a newer version of
Lean, with the Yul model removed.
The aim is to simplify proof development over the model.

Everything here is work in progress and is subject to change therefore.

The changes in this repository are intended to ease proof development over the
EVM model, with some tradeoffs against executable performance. They do not
relax the behavioral compatibility target. The conformance suite has changed:
the model is now tested against the
[execution-spec-tests](https://github.com/ethereum/execution-specs) fixtures,
which cover every fork it supports from Cancun to Osaka, instead of the
EthereumTests Cancun suite used by the EVMYulLean baseline. That suite remains
available (see [Conformance testing](#conformance-testing)). For a summary of
the main differences from Nethermind's upstream project, see
[nethermind-changes.md](nethermind-changes.md).

# Requirements
- Python packages: coincurve, typing-extensions, pycryptodome, eth-typing, py-ecc,
  cryptography

# Project structure

## Primops
The `Operation` describing all of the primitive operations:
```
Ethereum/Operations.lean
```

## Forks
The semantics is parametric in the execution-layer fork, from Cancun to Osaka
and the blob-parameter-only forks BPO1 to BPO4:
```
Ethereum/Fork.lean
```
The active fork is part of the execution environment (`ExecutionEnv.fork`) and
an explicit argument of the message-call (`Θ`), contract-creation (`Lambda`)
and transaction (`Υ`) functions. Each fork-dependent rule tests the fork with
`≥`, so a rule introduced at a fork stays active afterwards. The modelled
changes beyond Cancun are:

- Prague: BLS12-381 precompiles (EIP-2537), historical block hashes in state
  (EIP-2935), execution-layer requests (EIP-6110, EIP-7002, EIP-7251,
  EIP-7685), the calldata cost floor (EIP-7623), the blob schedule increase
  (EIP-7691) and set-code transactions (EIP-7702).
- Osaka: the `EXPMOD` input bounds and repricing (EIP-7823, EIP-7883), the
  transaction gas limit cap (EIP-7825), the blob base fee reserve price
  (EIP-7918), the block size limit (EIP-7934), the `CLZ` opcode (EIP-7939),
  the secp256r1 precompile (EIP-7951) and the per-transaction blob limit
  (EIP-7594).
- BPO1 to BPO4: blob schedules only (EIP-7892).

Transaction validity, sender recovery and the application of a transaction to
the state (`validateTransaction`, `applyTransaction`) are in
`Ethereum/Transaction.lean`. The block-level transition (header validity,
system calls, withdrawals, requests and block validity, with `applyBlock` as
the entry point) is in `Ethereum/Block.lean`.

## EVM
The model of the EVM state `EVM.State`:
```
Ethereum/State.lean
```

The semantic function `step`:
```
Ethereum/Semantics.lean
```

## Cryptographic trust boundaries

Ethereum's Keccak-256 is implemented as transparent Lean in
[`Ethereum/SpongeHash/Keccak256.lean`](Ethereum/SpongeHash/Keccak256.lean).
The implementation includes Keccak-f[1600], Ethereum's legacy `0x01` domain
suffix, multi-block absorption, and a proof that every digest contains exactly
32 bytes. It is exposed as `Ethereum.Keccak256.hash`, with `Ethereum.KEC` used
by the executable EVM semantics. Keccak calls reachable from the semantics
therefore do not cross an FFI boundary.

The other cryptographic primitives use external implementations:

- SHA-256 and the BLAKE2 compression function `F` are C functions linked
  through the FFI (`Ethereum/FFI`).
- ECDSA public-key recovery (`ECRECOVER`, transaction senders and EIP-7702
  authorities), RIPEMD-160, the alt_bn128 operations (`BN_ADD`, `BN_MUL`,
  `SNARKV`), the KZG point evaluation (EIP-4844), the BLS12-381 operations
  (EIP-2537, Prague) and secp256r1 signature verification (EIP-7951, Osaka)
  are Python helpers in `Ethereum/EllipticCurvesPy`.

The Lean wrappers of the precompiles with a fixed result size pass successful
results through
[`Ethereum.checkedPrecompileOutput`](Ethereum/PrecompileOutput.lean), which
rejects outputs whose size does not match the size prescribed for that
precompile. The secp256r1 wrapper instead builds its output in Lean: the
32-byte word `1` for a valid signature and empty output otherwise. This makes
the return-data size proofs independent of assumptions about external output
lengths. It does not prove that the external implementations compute the
correct cryptographic values; conformance testing remains the behavioral check
for those implementations.

## Conformance testing
The model is tested against the blockchain fixtures of
[execution-spec-tests](https://github.com/ethereum/execution-specs), pinned to
release `tests@v20.0.2`. The test running infrastructure can be found in:
```
Conform/
```

Passing this suite is the baseline behavioral trust check for the executable EVM
model. Any changes are accepted under the constraint that these
conformance tests continue to pass.

Fetch the fixtures once, then run the conformance tests:
```
scripts/fetch-eest.sh 20.0.2
lake test -- <NUM_THREADS> 2> out_discard.txt
```
where `<NUM_THREADS>` is the number of threads running conformance tests in
parallel; it defaults to the number of processors. We recommend redirecting
`stderr` into a file to not pollute the output.

This runs every fixture network from Cancun on, including the fork transition
networks. The threads take fixture files, or slices of large ones, from a
shared queue, slow tests first and then the most expensive files. The
following environment variables adjust a run:

- `EEST_FIXTURES` points to another `fixtures/blockchain_tests` directory.
- `CONFORM_DIRS` restricts the run to a comma-separated list of fixture
  directories, such as `for_osaka`.
- `CONFORM_FILTER` restricts the run to the tests whose name contains one of
  its `|`-separated substrings.
- `CONFORM_TIMED=1` writes the running time of every test, slowest first, to
  `timings_1.txt`, and `CONFORM_PROGRESS=<file>` logs each test as it starts
  and finishes.
- `CONFORM_SUITE=legacy` runs the legacy Cancun suite of
  [ethereum/tests](https://github.com/ethereum/tests) and
  [ethereum/legacytests](https://github.com/ethereum/legacytests) instead of
  the fixtures. Fetch it once with `scripts/fetch-legacy-tests.sh`, which
  downloads the test directories at
  pinned commits; `LEGACY_FIXTURES` points to another copy. It includes
  performance tests (`vmPerformance` and a few others), which take up to an
  hour each; `CONFORM_SKIP_PERF=1` leaves them out.

# License

This repository is based on Nethermind's [EVMYulLean](https://github.com/NethermindEth/EVMYulLean), which is licensed under the Apache License, Version 2.0. This modified copy is distributed under the Apache License, Version 2.0; see [LICENSE](LICENSE).

Notable modifications include porting the project to a newer Lean version, stripping the Yul portions, and adapting the remaining EVM model and project structure for proof development. See [NOTICE](NOTICE) for attribution and modification notes.

Some included third-party components carry their own licenses, including `sha2/LICENSE.md` and `keccak256/LICENSE`.
