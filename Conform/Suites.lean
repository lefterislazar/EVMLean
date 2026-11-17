import Conform.Driver

/-!
# The test suites

- `runEEST`: the blockchain fixtures of an `execution-spec-tests` release.
- `runLegacy`: the Cancun blockchain tests of `ethereum/tests` and
  `ethereum/legacytests`.

`lake test` fetches the pinned fixtures of the suite (see `lakefile.lean`), and
names them in `EEST_FIXTURES` or `LEGACY_FIXTURES`.

Both are in the same fixture format (see `Conform.Fixture`); they differ only
in where their files are and which of their tests are left out.
-/

namespace Ethereum

namespace Conform

/-- The directory in the environment variable `envVar`, which `lake test` sets. -/
def fixturesDirectory (envVar : String) : IO (Option System.FilePath) := do
  let some fixtures := (← IO.getEnv envVar).map System.FilePath.mk
    | IO.eprintln s!"{envVar} is not set. Run the tests with `lake test`, which fetches the fixtures."
      return none
  unless ← fixtures.pathExists do
    IO.eprintln s!"{envVar}: no fixtures at {fixtures}."
    return none
  return fixtures

/--
The fixture directories of the networks that the model supports. Each
directory holds the tests of one network, so the model supports every test in
them.
-/
def eestDirectories : Array System.FilePath :=
  #["for_cancun", "for_cancuntopragueattime15k", "for_prague", "for_praguetoosakaattime15k",
    "for_osaka", "for_osakatobpo1attime15k", "for_bpo1tobpo2attime15k",
    "for_bpo2tobpo3attime15k", "for_bpo3tobpo4attime15k"]

/--
Run the `execution-spec-tests` blockchain fixtures in `EEST_FIXTURES` on
`threads` threads. `CONFORM_DIRS` restricts the run to a comma-separated list
of the fixture directories.
-/
def runEEST (threads : ℕ) : IO UInt32 := do
  let some fixtures ← fixturesDirectory "EEST_FIXTURES" | return 1
  let selected := (← IO.getEnv "CONFORM_DIRS").map (·.splitOn ",")
  let roots ← eestDirectories.filterMapM λ d ↦ do
    let root := fixtures / d
    let wanted := selected.all (·.contains d.toString)
    pure <| if wanted ∧ (← root.pathExists) then some root else none
  IO.println s!"EEST fixtures in {fixtures}: {roots.size} directories."
  (← IO.getStdout).flush
  report (← runTests roots threads)

/-- Tests of the legacy suite that take from a minute to an hour. -/
def legacyPerformanceTests : Array String :=
  #["static_Call50000bytesContract50_2_d1g0v0_Cancun",
    "static_Call50000bytesContract50_2_d0g0v0_Cancun",
    "static_Call50000bytesContract50_3_d1g0v0_Cancun",
    "static_Call50000_sha256_d0g0v0_Cancun",
    "static_Call50000_sha256_d1g0v0_Cancun",
    "CALLBlake2f_MaxRounds_d0g0v0_Cancun"]

/--
Run the legacy suite in `LEGACY_FIXTURES` on `threads` threads: the refilled
block tests of `ethereum/tests` in `BlockchainTests` and the Cancun
general-state corpus of `ethereum/legacytests` in
`LegacyTests/Cancun/BlockchainTests`. The files of the Cancun corpus mix
networks, from Berlin to Cancun; the tests of the networks that the model does
not support are reported as skipped.

The performance tests, in the `vmPerformance` directory and a few others, take
from a minute to an hour each. They are left out unless `CONFORM_PERF=1`.
-/
def runLegacy (threads : ℕ) : IO UInt32 := do
  let some fixtures ← fixturesDirectory "LEGACY_FIXTURES" | return 1
  let cancun := fixtures / "LegacyTests" / "Cancun" / "BlockchainTests"
  let performanceDirectory := cancun / "GeneralStateTests" / "VMTests" / "vmPerformance"
  -- The `ethereum/tests` v17.2 refill also names tests by their filler path,
  -- as in `BlockchainTests/ValidBlocks/bcExploitTest/SuicideIssue.json::SuicideIssue_Cancun`.
  let isPerformanceTest (testName : String) :=
    legacyPerformanceTests.any fun name => testName == name || testName.endsWith ("::" ++ name)
  let includePerf := (← IO.getEnv "CONFORM_PERF").isSome
  IO.println <|
    if includePerf then "Conformance tests, including the performance tests."
    else "Conformance tests, without the performance tests."
  (← IO.getStdout).flush
  report (← runTests #[fixtures / "BlockchainTests", cancun] threads
    (skipFile := fun path => ¬includePerf ∧ isUnder performanceDirectory path)
    (skipTest := fun testName => ¬includePerf ∧ isPerformanceTest testName))

end Conform

end Ethereum
