This repository contains a formal model of the EVM in Lean 4.
It is an EVM-focused port of Nethermind's
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean) to a newer version of
Lean, with the Yul model removed.
The aim is to simplify proof development over the model.

Everything here is work in progress and is subject to change therefore.

The changes in this repository are intended to ease proof development over the
EVM model, with some tradeoffs against executable performance. They do not
relax the behavioral compatibility target. The conformance suite has changed,
and the model is now tested against the EEST:
[execution-spec-tests](https://github.com/ethereum/execution-specs).

For a summary of the main differences from Nethermind's upstream project, see
[nethermind-changes.md](nethermind-changes.md).

# Requirements
- Python packages: coincurve, typing-extensions, pycryptodome, eth-typing, py-ecc,
  cryptography

# Project structure

## Forks
The semantics is parametric in the execution-layer fork, from Cancun to Osaka:
```
Ethereum/Fork.lean
```

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
precompile.

## Conformance testing
The model is tested against the blockchain fixtures of
[execution-spec-tests](https://github.com/ethereum/execution-specs), pinned to
release `tests@v21.0.2`. The test running infrastructure can be found in:
```
Conform/
```
Run the conformance tests with:
```
lake test 2> out_discard.txt
```
We recommend redirecting `stderr` into a file to not pollute the output.

The first run downloads the pinned fixtures.
The pins and the fetching are in `lakefile.lean`.

This runs every fixture network from Cancun on.

`lake test -- --help` lists conformance parameters:

- `--threads N` runs on `N` threads; by default, one per processor.
- `--dirs D1,D2,...` restricts the run to these fixture directories, such as
  `for_osaka`.
- `--filter S1|S2|...` restricts the run to the tests whose name contains one
  of these substrings.
- `--fixtures PATH` runs the fixtures in `PATH` instead of fetching the pinned
  ones.
- `--timed` writes the running time of every test, slowest first, to
  `.cache/conform/timings.txt`, and `--progress` logs each test as it starts
  and finishes to `.cache/conform/progress.txt`.
- `--legacy` runs the legacy Cancun suite of
  [ethereum/tests](https://github.com/ethereum/tests) and
  [ethereum/legacytests](https://github.com/ethereum/legacytests) instead of
  the fixtures. Its performance tests (`vmPerformance` and a few others),
  which take up to an hour each, are left out unless `--perf`.

# License

This repository is based on Nethermind's [EVMYulLean](https://github.com/NethermindEth/EVMYulLean), which is licensed under the Apache License, Version 2.0. This modified copy is distributed under the Apache License, Version 2.0; see [LICENSE](LICENSE).

Notable modifications include porting the project to a newer Lean version, stripping the Yul portions, and adapting the remaining EVM model and project structure for proof development. See [NOTICE](NOTICE) for attribution and modification notes.

Some included third-party components carry their own licenses, including `sha2/LICENSE.md` and `keccak256/LICENSE`.
