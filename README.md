This repository contains a formal model of the EVM in Lean 4.
It is an EVM-focused port of Nethermind's
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean) to a newer version of
Lean, with the Yul model removed.
The aim is to simplify proof development over the model.

Everything here is work in progress and is subject to change therefore.

The changes in this repository are intended to ease proof development over the
EVM model, with some tradeoffs against executable performance. They do not
relax the behavioral compatibility target: the model continues to pass the same
pinned Ethereum conformance suite and test driver used by the EVMYulLean
baseline. For a summary of the main differences from Nethermind's
upstream project, see
[nethermind-changes.md](nethermind-changes.md).

# Requirements
- Python packages: coincurve, typing-extensions, pycryptodome, eth-typing, py-ecc

# Project structure

## Primops
The `Operation` describing all of the primitive operations:
```
Ethereum/Operations.lean
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
The implementation includes Keccak-f[1600], Ethereum's legacy `0x01` domain
suffix, multi-block absorption, and a proof that every digest contains exactly
32 bytes. It is exposed as `Ethereum.Keccak256.hash`, with `Ethereum.KEC` used
by the executable EVM semantics. Keccak calls reachable from the semantics
therefore do not cross an FFI boundary.

Several cryptographic precompiles still use external implementations. Their
Lean wrappers pass successful results through
[`Ethereum.checkedPrecompileOutput`](Ethereum/PrecompileOutput.lean), which
rejects outputs whose size does not match the result size prescribed for that
precompile. This makes the return-data size proofs independent of assumptions
about external output lengths. It does not prove that the external
implementations compute the correct cryptographic values; conformance testing
remains the behavioral check for those implementations.

## Conformance testing
A git submodule with EVM conformance tests is in:
```
EthereumTests/
```

The test running infrastructure can be found in:
```
Conform/
```

Passing this suite is the baseline behavioral trust check for the executable EVM
model. Any changes are accepted under the constraint that these
conformance tests continue to pass.

To execute conformance tests, make sure the `EthereumTests` directory is the appropriate git submodule and run:
```
lake test -- <NUM_THREADS> 2> out_discard.txt
```
where `<NUM_THREADS>` is the number of threads running conformance tests in parallel. Note that the default is `1`.
We recommend redirecting `stderr` into a file to not pollute the output.

# License

This repository is based on Nethermind's [EVMYulLean](https://github.com/NethermindEth/EVMYulLean), which is licensed under the Apache License, Version 2.0. This modified copy is distributed under the Apache License, Version 2.0; see [LICENSE](LICENSE).

Notable modifications include porting the project to a newer Lean version, stripping the Yul portions, and adapting the remaining EVM model and project structure for proof development. See [NOTICE](NOTICE) for attribution and modification notes.

Some included third-party components carry their own licenses, including `EthereumTests/LICENSE`, `sha2/LICENSE.md`, and `keccak256/LICENSE`.
