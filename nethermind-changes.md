# Main Changes from Nethermind's EVMYulLean

This repository is derived from Nethermind's
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean), but has a narrower
focus: supporting proof development over the EVM semantics.

The changes favor definitions that are easier to inspect and reason about in
Lean. Some of them trade executable performance for simpler proof obligations
or a smaller trusted surface. They do not relax the behavioral compatibility
target: the EVM model continues to pass the Ethereum conformance tests used by
the original project.

This document summarizes the main conceptual differences. It is not intended to
be an exhaustive file-by-file changelog.

## Updated Lean Version

The project was ported to a newer version of Lean. The resulting compatibility
changes are not intended to alter the modeled EVM behavior.

## EVM-Only Model

The Yul model and its tests were removed. The generic layer that distinguished
EVM operations and state from their Yul counterparts was also specialized to
the EVM.

As part of this change, the previous split between generic state, shared machine
state, and EVM state was simplified into the EVM-specific structures in
`Ethereum/State.lean` and `Ethereum/MachineState.lean`. This removes Yul-related
parameters and projections from EVM proofs, at the cost of no longer providing
Yul semantics.

## Reduced Use of Fuel

The original model threaded an explicit fuel argument through most of the
execution semantics. Reaching zero fuel produced an `OutOfFuel` exception,
independently of the EVM's own gas and call-depth limits.

In this repository, recursive message calls and contract creation instead use
the EVM call-depth bound to justify termination. The outer opcode loop `X`
retains fuel, but its caller derives that fuel from the available gas rather
than exposing an independent execution parameter.

This makes the high-level semantics less dependent on an artificial termination
mechanism while preserving a structurally recursive opcode loop. The associated
proof in `Ethereum/Theory/NoOutOfFuel.lean` connects fuel exhaustion to gas
consumption.

## Zero-Saturating Gas

Available gas was changed from `UInt256`, whose subtraction wraps modulo
`2^256`, to the zero-saturating `Sat256` type in `Ethereum/Sat256.lean`.
Out-of-gas checks still occur before gas is charged.

The new representation prevents modular underflow from appearing in
intermediate definitions and provides simpler monotonicity and subtraction
lemmas for proofs.

## Transparent `ByteArray.zeroes`

The original `ByteArray.zeroes` was an opaque Lean function implemented through
the C FFI. It is now defined transparently in Lean using `Array.replicate`.

This is be slower during execution, but it lets proofs inspect the definition
directly and removes one foreign primitive from the trusted surface. The change
is contained primarily in `Ethereum/Wheels.lean` and `Ethereum/FFI/ffi.lean`.

## Added `Xstep`

The body of the opcode loop was factored into `Xstep`, representing one opcode
in the current call frame. The recursive loop `X` is then expressed by repeated
applications of this step.

An `Xstep` can still execute a nested message call or contract creation when the
current opcode requires it. The boundary is nevertheless useful for stating
per-opcode properties and reasoning about finite execution sequences.

The definitions are in `Ethereum/Semantics.lean`, with supporting results in
`Ethereum/Theory/ProgressLemmas.lean` and
`Ethereum/Theory/GasLemmas.lean`.

## Simplified Exception Paths

After recursive calls were moved away from explicit fuel, `Lambda` and `Theta`
no longer needed to return exceptions solely to carry fuel exhaustion. They now
return their semantic results directly, while exceptional execution of nested
EVM code is still represented as a failed call or contract creation.

This also follows the presentation in the
[Yellow Paper](https://ethereum.github.io/yellowpaper/paper.pdf), where
`Lambda` and `Theta` return semantic result tuples rather than propagating a
separate exception result.

This does not remove EVM exceptions generally. Opcode-level exceptional halts
and the exception result of the opcode loop remain part of the model.

## Added EVM Proof Library

The [`Ethereum/Theory`](Ethereum/Theory/README.md) directory contains the proof
development built over the EVM model. It includes results about opcode behavior,
gas consumption, execution progress, account locality, storage preservation and
extensionality, and return-data bounds.
