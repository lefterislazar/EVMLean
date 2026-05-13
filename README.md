This repository contains a formal model of the EVM in Lean 4.
It is a port of Nethermind's [EVMYulLean](https://github.com/NethermindEth/EVMYulLean) to a newer version of Lean, with the Yul parts strip.
The aim is to simplify working with the model for research purposes.

Everything here is work in progress and is subject to change therefore.

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

## Conformance testing
A git submodule with EVM conformance tests is in:
```
EthereumTests/
```

The test running infrastructure can be found in:
```
Conform/
```

To execute conformance tests, make sure the `EthereumTests` directory is the appropriate git submodule and run:
```
lake test -- <NUM_THREADS> 2> out_discard.txt
```
where `<NUM_THREADS>` is the number of threads running conformance tests in parallel. Note that the default is `1`.
We recommend redirecting `stderr` into a file to not pollute the output.
