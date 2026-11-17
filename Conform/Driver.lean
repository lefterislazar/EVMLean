import Conform.Fixture
import Conform.Network
import Conform.Run

/-!
# Running the tests of fixture files

Finds the tests in directories of fixture files, runs them on several threads
and logs the results. The driver reads only the `network` of a test before
running it, to leave out the tests of networks that the model does not
support.
-/

namespace Ethereum

namespace Conform

abbrev TestId : Type := System.FilePath × String

/-- `none` when the test passed, otherwise why it failed. -/
def TestResult := Option String

instance : ToString TestResult where
  toString result := result.elim "Success." id

def logFile : System.FilePath := "tests_1.txt"

def liveFailureLog : System.FilePath := "failures_live.txt"

def timingsFile : System.FilePath := "timings_1.txt"

def log (testFile : System.FilePath) (testName : String) (result : TestResult) : IO Unit :=
  IO.FS.withFile logFile .append λ h ↦ h.putStrLn s!"{testFile.fileName.get!}[{testName}] - {result}\n"

/--
Run the tests `names` of the fixture file `path`, parsing the file once. Every
result comes with the test's running time in milliseconds.
-/
def runFile (path : System.FilePath) (names : Array String) :
    IO (Array (TestId × TestResult × ℕ)) := do
  -- `CONFORM_PROGRESS` names a file that records each test as it starts and
  -- finishes, to see which tests are running.
  let progress := (← IO.getEnv "CONFORM_PROGRESS").map System.FilePath.mk
  let file ← readJsonFile path
  let mut results := #[]
  for testName in names do
    let start ← IO.monoMsNow
    if let some progress := progress then
      IO.FS.withFile progress .append (·.putStrLn s!"start {testName} FROM {path}")
    let result : TestResult :=
      match file.getObjValAs? BlockchainTest testName with
      | .error err => some s!"Cannot decode: {err}"
      | .ok test =>
        match run test with
        | .error failure => some (toString failure)
        | .ok () => none
    let elapsed := (← IO.monoMsNow) - start
    if let some progress := progress then
      IO.FS.withFile progress .append (·.putStrLn s!"done {elapsed}ms {testName}")
    results := results.push ((path, testName), result, elapsed)
  return results

/-- Whether `path` lies in the directory `dir`, comparing path components. -/
def isUnder (dir path : System.FilePath) : Bool :=
  let parts (p : System.FilePath) := p.components.filter (· ≠ "")
  (parts dir).isPrefixOf (parts path)

/--
Run the tests `names` of each fixture file `path` of `files` on `threads`
threads. Each thread repeatedly takes the next file from a shared queue, in
the order of `files`.
-/
def runFiles (files : Array (System.FilePath × Array String)) (threads : ℕ) :
    IO (Array (TestId × TestResult × ℕ)) := do
  let next ← IO.mkRef 0
  let worker : IO (Array (TestId × TestResult × ℕ)) := do
    let mut results := #[]
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      let some (path, names) := files[i]? | break
      results := results ++ (← runFile path names)
    return results
  let mut tasks := #[]
  for _ in [0:max threads 1] do
    tasks := tasks.push (← IO.asTask worker .dedicated)
  let mut results := #[]
  for task in tasks do
    results := results ++ (← IO.ofExcept task.get)
  return results

/-- Whether the model supports the network of the fixture test `test`. -/
def isSupported (test : Lean.Json) : Bool :=
  match test.getObjVal? "network" >>= Lean.Json.getStr? with
  | .ok network => (parseNetwork? network).isSome
  | .error _ => false

/--
Run the tests of the fixture files in `roots` on `threads` threads, leaving
out the files that `skipFile` selects and the tests that `skipTest` selects.
The largest files start first, so that they do not finish last. Returns the
number of tests that passed, and the tests that failed.
-/
def runTests (roots : Array System.FilePath) (threads : ℕ)
    (skipFile : System.FilePath → Bool := fun _ => false)
    (skipTest : String → Bool := fun _ => false) : IO (ℕ × Array String) := do
  -- `CONFORM_FILTER` selects the tests whose name contains one of its
  -- `|`-separated substrings.
  let filter := (← IO.getEnv "CONFORM_FILTER").getD ""
  let isToBeTested (testName : String) : Bool :=
    ¬skipTest testName ∧
      (filter.isEmpty ∨ (filter.splitOn "|").any (fun f => (testName.splitOn f).length > 1))

  let mut found := #[]
  for root in roots do
    found := found ++ (← System.FilePath.walkDir root).filter (·.extension == some "json")
  let files := found.filter fun p => ¬skipFile p ∧ p.components.all (· != ".meta")

  let mut selected : Array (System.FilePath × Array String × ℕ) := #[]
  for path in files do
    let json ← readJsonFile path
    match json.getObj? with
    | .error err => throw <| .userError s!"{path}: {err}"
    | .ok tests =>
        let names := tests.toArray.filterMap fun (name, test) =>
          if isSupported test && isToBeTested name then some name else none
        unless names.isEmpty do
          selected := selected.push (path, names, (← path.metadata).byteSize.toNat)

  for file in [logFile, liveFailureLog] do
    if ← file.pathExists then IO.FS.removeFile file

  -- The largest files start first, so that they do not finish last.
  let queue := (selected.qsort (·.2.2 > ·.2.2)).map fun (path, names, _) => (path, names)
  let scheduled := queue.foldl (· + ·.2.size) 0
  IO.println s!"Scheduled {scheduled} tests in {queue.size} files on {threads} thread{if threads == 1 then "" else "s"}."
  IO.println s!"Running..."
  (← IO.getStdout).flush
  let results ← runFiles queue threads

  let mut numSuccess := 0
  let mut failedTests : Array String := .empty
  for ((file, test), res, _) in results do
    log file test res
    match res with
    | none => numSuccess := numSuccess + 1
    | some err =>
      failedTests := failedTests.push s!"{file.fileName.get!}[{test}]"
      IO.FS.withFile liveFailureLog .append fun h =>
        h.putStrLn s!"{file.fileName.get!}[{test}] {err}"

  -- `CONFORM_TIMED` writes the running time of every test, slowest first.
  if (← IO.getEnv "CONFORM_TIMED").isSome then
    let timings := results.qsort (·.2.2 > ·.2.2)
    IO.FS.withFile timingsFile .write fun h =>
      for ((file, test), _, ms) in timings do
        h.putStrLn s!"{ms.toFloat / 1000.0}s {file}[{test}]"
  return (numSuccess, failedTests)

/-- Print the results of `runTests`, and return the exit code: 0 when every test passed. -/
def report (results : ℕ × Array String) : IO UInt32 := do
  let (success, failure) := results
  let total := success + failure.size
  IO.println s!"Total tests: {total}"
  IO.println s!"The post was NOT equal to the resulting state: {failure.size}"
  IO.println s!"Succeeded: {success}"
  IO.println s!"Success rate of: {if total = 0 then 100.0 else (success.toFloat / total.toFloat) * 100.0}"
  IO.println s!"Failed tests:\n{failure}"
  return if failure.isEmpty then 0 else 1

end Conform

end Ethereum
