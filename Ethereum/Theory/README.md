# EVM Proof Development

This directory contains proofs about the EVM model defined under `Ethereum`.
The files are organized by the property being established rather than by EVM
component.

## Files

- [`OpcodeLemmas.lean`](OpcodeLemmas.lean) gives explicit characterizations of
  `step` for individual opcodes. These results provide a convenient starting
  point for proofs about concrete instructions.

- [`GasLemmas.lean`](GasLemmas.lean) establishes positivity, monotonicity, and
  decrease properties for gas costs and carries them through `Z`, `step`,
  `Xstep`, `X`, calls, and precompiled contracts.

- [`NoOutOfFuel.lean`](NoOutOfFuel.lean) separates the model's recursion fuel
  from EVM gas. In particular, it shows that execution with fuel derived from
  the available gas cannot fail with the artificial `OutOfFuel` exception.

- [`ProgressLemmas.lean`](ProgressLemmas.lean) relates `Xstep` to the recursive
  opcode loop `X`. It also defines `XstepN`, a relation describing finite
  sequences of steps.

- [`ReturnDataBound.lean`](ReturnDataBound.lean) derives bounds on return-data
  size from the available gas and propagates them through calls, contract
  creation, and precompiled contracts. Bounds for FFI-backed precompiles use
  explicit output-size assumptions declared in that file.

- [`AccountLocality.lean`](AccountLocality.lean) develops relations describing
  which changes to an account are consistent with EVM execution and carries
  them through steps, calls, and contract creation. **The intended locality
  property for effects after calls is work in progress, including its formal
  statement. The current relations and theorems should not yet be treated as a
  definitive formulation of that property.**

- [`StorageExtensionality.lean`](StorageExtensionality.lean) defines
  extensional equality for storage, accounts, and account maps, and proves that
  the execution semantics respects that equality.

- [`StaticStorage.lean`](StaticStorage.lean) proves preservation results for
  static execution, including that static calls preserve persistent storage,
  transient storage, and account code.

All modules are imported by `Ethereum.lean`. The directory is active proof
development, so theorem interfaces and file boundaries may still change.
