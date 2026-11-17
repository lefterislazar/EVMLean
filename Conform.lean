import Conform.Json
import Conform.Fixture
import Conform.Network
import Conform.Exceptions
import Conform.Run
import Conform.Driver
import Conform.Suites

/-!
# Conformance testing

The model is tested against blockchain test fixtures. The modules, from the
fixture to the run of a suite:

- `Conform.Json`: JSON helpers and the hex encoding of the fixtures.
- `Conform.Fixture`: the blockchain test format and its decoding.
- `Conform.Network`: the chain configuration of a fixture's network.
- `Conform.Exceptions`: whether a block is rejected with an expected exception.
- `Conform.Run`: running one test, independently of where it comes from.
- `Conform.Driver`: finding, scheduling and logging the tests of fixture files.
- `Conform.Suites`: `runEEST` and `runLegacy`, which run the
  `execution-spec-tests` fixtures and the legacy suite.

`Conform.Main` is the `conform` executable that `lake test` runs.
-/
