import Conform.TestRunner

def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def logFile (phase : ℕ) : System.FilePath := s!"tests_{phase}.txt"

def liveFailureLog : System.FilePath := "failures_live.txt"

open Ethereum.Conform in
instance : ToString TestResult where
  toString tr := tr.elim "Success." id

open Ethereum.Conform in
def log (testFile : System.FilePath) (testName : String) (result : TestResult) (phase : ℕ := 0) : IO Unit :=
  IO.FS.withFile (logFile phase) .append λ h ↦ h.putStrLn s!"{testFile.fileName.get!}[{testName}] - {result}\n"

/--
A unit of work: tests of one fixture file, run by one thread, which parses the
file once. `cost` estimates the unit's running time, for scheduling.
-/
structure WorkUnit where
  path  : System.FilePath
  names : Array String
  cost  : ℕ

/--
Whether the fixture test `testname` is the test `name`. The `ethereum/tests`
v17.2 refill also names tests by their filler path, as in
`BlockchainTests/ValidBlocks/bcExploitTest/SuicideIssue.json::SuicideIssue_Cancun`.
-/
def isTest (name testname : String) : Bool :=
  testname == name || testname.endsWith ("::" ++ name)

/-- Whether `path` lies in the directory `dir`, comparing path components. -/
def isUnder (dir path : System.FilePath) : Bool :=
  let parts (p : System.FilePath) := p.components.filter (· ≠ "")
  (parts dir).isPrefixOf (parts path)

/--
Split the selected tests of each fixture file into work units. A large file is
split into up to `threads` units, so that its tests spread over the threads; a
unit's cost is its share of the file's size.
-/
def workUnits (threads : ℕ) (files : Array (System.FilePath × ℕ × Array String))
    (isFirst : WorkUnit → Bool := fun _ => false) : IO (Array WorkUnit) := do
  let largeFile : ℕ := 4 * 1024 * 1024
  let mut units := #[]
  for (path, total, names) in files do
    if names.isEmpty then continue
    let size := (← path.metadata).byteSize.toNat
    let pieces := if size > largeFile then min threads names.size else 1
    let chunk := (names.size + pieces - 1) / pieces
    for k in [0:pieces] do
      let part := names.extract (k * chunk) ((k + 1) * chunk)
      unless part.isEmpty do
        units := units.push { path, names := part, cost := size * part.size / max total 1 }
  -- The `isFirst` units go first, then the most expensive ones.
  return units.qsort fun a b =>
    if isFirst a != isFirst b then isFirst a else a.cost > b.cost

/--
Run the work units on `threads` threads. Each thread repeatedly takes the
next unit from a shared queue, most expensive first, so that threads finish
together.
-/
def runWorkUnits (units : Array WorkUnit) (threads : ℕ) :
    IO (Array (Ethereum.Conform.TestId × Ethereum.Conform.TestResult × ℕ)) := do
  let next ← IO.mkRef 0
  let worker : IO (Array (Ethereum.Conform.TestId × Ethereum.Conform.TestResult × ℕ)) := do
    let mut results := #[]
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      let some unit := units[i]? | break
      results := results ++ (← Ethereum.Conform.processTests (unit.names.map (unit.path, ·)))
    return results
  let mut tasks := #[]
  for _ in [0:max threads 1] do
    tasks := tasks.push (← IO.asTask worker .dedicated)
  let mut results := #[]
  for task in tasks do
    results := results ++ (← IO.ofExcept task.get)
  return results

def testFiles (roots              : Array System.FilePath)
              (slowDirectories    : Array System.FilePath := #[])
              (slowTests          : Array String := #[])
              (skipSlow           : Bool := false)
              (phase              : ℕ)
              (threads            : ℕ := 1) : IO (Nat × Array String) := do
  let isSlowTest (testname : String) := slowTests.any (isTest · testname)
  -- `CONFORM_FILTER` selects the tests whose name contains one of its
  -- `|`-separated substrings.
  let filter := (← IO.getEnv "CONFORM_FILTER").getD ""
  let isToBeTested (testname : String) : Bool :=
    ¬(skipSlow ∧ isSlowTest testname) ∧
      (filter.isEmpty ∨ (filter.splitOn "|").any (fun f => (testname.splitOn f).length > 1))

  let mut found := #[]
  for root in roots do
    found := found ++ Array.filter isTestFile (← System.FilePath.walkDir root)

  let testFiles := found.filter fun p =>
    ¬(skipSlow ∧ slowDirectories.any (isUnder · p))
  let testFiles := testFiles.filter fun p => p.components.all (· != ".meta")

  let mut selected : Array (System.FilePath × ℕ × Array String) := #[]
  for path in testFiles do
    let json ← Lean.Json.fromFile path
    match json.getObj? with
    | .error _ => panic! "Malformed test json."
    | .ok x =>
        let names := x.toArray.filterMap fun (name, val) =>
          let supported := match val.getObjVal? "network" >>= Lean.Json.getStr? with
            | .ok network => (Ethereum.Conform.parseNetwork? network).isSome
            | .error _ => false
          if supported && isToBeTested name then some name else none
        selected := selected.push (path, x.size, names)

  if ←System.FilePath.pathExists (logFile phase) then IO.FS.removeFile (logFile phase)

  -- Slow tests start first, so that they do not finish last.
  let units ← workUnits threads selected fun u =>
    slowDirectories.any (isUnder · u.path) ∨ u.names.any isSlowTest
  let scheduled := units.foldl (· + ·.names.size) 0
  IO.println s!"Scheduled {scheduled} tests in {units.size} units on {threads} thread{if threads == 1 then "" else "s"}."
  IO.println s!"Running..."
  (← IO.getStdout).flush
  let results ← runWorkUnits units threads

  let mut numSuccess := 0
  let mut failedTests : Array String := .empty
  for ((file, test), res, _) in results do
    log file test res phase
    match res with
    | none => numSuccess := numSuccess + 1
    | some err =>
      failedTests := failedTests.push s!"{file.fileName.get!}[{test}]"
      IO.FS.withFile liveFailureLog .append fun h =>
        h.putStrLn s!"{file.fileName.get!}[{test}] {err}"

  -- `CONFORM_TIMED` writes the running time of every test, slowest first.
  if (← IO.getEnv "CONFORM_TIMED").isSome then
    let timings := results.qsort (·.2.2 > ·.2.2)
    IO.FS.withFile s!"timings_{phase}.txt" .write fun h =>
      for ((file, test), _, ms) in timings do
        h.putStrLn s!"{ms.toFloat / 1000.0}s {file}[{test}]"
  return (numSuccess, failedTests)

/-- The `execution-spec-tests` release the conformance driver is pinned to. -/
def defaultFixturesVersion : String := "20.0.2"

/-- Where `scripts/fetch-eest.sh` extracts the pinned release's blockchain fixtures. -/
def defaultFixtures : System.FilePath :=
  s!".cache/eest/tests-v{defaultFixturesVersion}/fixtures/blockchain_tests"

/-- Where `scripts/fetch-legacy-tests.sh` places the legacy EthereumTests suite. -/
def defaultLegacyFixtures : System.FilePath :=
  ".cache/legacy-tests/c67e485ff8b5-1f581b8ccdc4"

def nproc : IO Nat := do
  let out ← IO.Process.output {cmd := "nproc", stdin := .null}
  return out.stdout.trimAscii.toString.toNat? |>.getD 1

def main (args : List String) : IO UInt32 := do

  let NumThreads : ℕ := args.head? <&> String.toNat! |>.getD (←nproc)

  let printResults (result : ℕ × Array String) : IO (Array String) := do
    let (success, failure) := result
    IO.println s!"Total tests: {success + failure.size}"
    IO.println s!"The post was NOT equal to the resulting state: {failure.size}"
    IO.println s!"Succeeded: {success}"
    let total := failure.size + success
    IO.println s!"Success rate of: {if total = 0 then 100.0 else (success.toFloat / total.toFloat) * 100.0}"
    IO.println s!"Failed tests:\n{failure}"
    return failure

  if ←System.FilePath.pathExists liveFailureLog then IO.FS.removeFile liveFailureLog

  /-
    The performance tests take from a minute to several minutes each: the
    `vmPerformance` directory and a few others. They run by default, first.
    `CONFORM_SKIP_PERF=1` leaves them out.
  -/
  let perfTests : Array String :=
    #["static_Call50000bytesContract50_2_d1g0v0_Cancun",
      "static_Call50000bytesContract50_2_d0g0v0_Cancun",
      "static_Call50000bytesContract50_3_d1g0v0_Cancun",
      "static_Call50000_sha256_d0g0v0_Cancun",
      "static_Call50000_sha256_d1g0v0_Cancun",
      "CALLBlake2f_MaxRounds_d0g0v0_Cancun"]
  let skipPerf := (← IO.getEnv "CONFORM_SKIP_PERF").isSome

  /-
    By default, run the `execution-spec-tests` blockchain fixtures fetched by
    `scripts/fetch-eest.sh` (or found at `EEST_FIXTURES`): every network from
    Cancun on. `CONFORM_SUITE=legacy` runs the legacy Cancun suite fetched by
    `scripts/fetch-legacy-tests.sh` (or found at `LEGACY_FIXTURES`) instead.
  -/
  if (← IO.getEnv "CONFORM_SUITE") != some "legacy" then
    let fixtures : System.FilePath :=
      ((← IO.getEnv "EEST_FIXTURES").map System.FilePath.mk).getD defaultFixtures
    unless ← fixtures.pathExists do
      IO.eprintln s!"No fixtures at {fixtures}. Fetch them with `scripts/fetch-eest.sh {defaultFixturesVersion}`,"
      IO.eprintln "set EEST_FIXTURES, or set CONFORM_SUITE=legacy to run the legacy EthereumTests suite."
      return 1
    let directories : Array System.FilePath :=
      #["for_cancun", "for_cancuntopragueattime15k", "for_prague", "for_praguetoosakaattime15k",
        "for_osaka", "for_osakatobpo1attime15k", "for_bpo1tobpo2attime15k",
        "for_bpo2tobpo3attime15k", "for_bpo3tobpo4attime15k"]
    -- `CONFORM_DIRS` restricts the run to a comma-separated list of directories.
    let selected := (← IO.getEnv "CONFORM_DIRS").map (·.splitOn ",")
    let roots ← directories.filterMapM λ d ↦ do
      let root := fixtures / d
      let wanted := selected.all (·.contains d.toString)
      pure <| if wanted ∧ (← root.pathExists) then some root else none
    IO.println s!"EEST fixtures in {fixtures}: {roots.size} directories."
    (← IO.getStdout).flush
    -- Tests that take minutes, which start first so that they do not finish last.
    let slowFixtures : Array String :=
      #["tests/prague/eip2935_historical_block_hashes_from_state/test_block_hashes.py::test_block_hashes_history_at_transition[fork_CancunToPragueAtTime15k-blockchain_test-blocks_before_fork_1-blocks_after_fork_257]"]
    let failed ← testFiles (roots := roots) (slowTests := slowFixtures)
                           (phase := 1) (threads := NumThreads) >>= printResults
    return if failed.isEmpty then 0 else 1

  /-
    The legacy suite: the refilled block tests of ethereum/tests in
    `BlockchainTests` and the Cancun general-state corpus of
    ethereum/legacytests in `LegacyTests/Cancun/BlockchainTests`.
  -/
  let legacyFixtures : System.FilePath :=
    ((← IO.getEnv "LEGACY_FIXTURES").map System.FilePath.mk).getD defaultLegacyFixtures
  unless ← legacyFixtures.pathExists do
    IO.eprintln s!"No legacy tests at {legacyFixtures}. Fetch them with `scripts/fetch-legacy-tests.sh`,"
    IO.eprintln "or set LEGACY_FIXTURES."
    return 1
  let legacyRoot := legacyFixtures / "LegacyTests" / "Cancun" / "BlockchainTests"
  let perfDir := legacyRoot / "GeneralStateTests" / "VMTests" / "vmPerformance"

  IO.println <|
    if skipPerf then "Conformance tests, without the performance tests."
    else "Conformance tests, including the performance tests."
  (← IO.getStdout).flush
  let failed ← testFiles (roots := #[legacyFixtures / "BlockchainTests", legacyRoot])
                         (slowDirectories := #[perfDir])
                         (slowTests := perfTests)
                         (skipSlow := skipPerf)
                         (phase := 1)
                         (threads := NumThreads) >>= printResults

  return if failed.isEmpty then 0 else 1
