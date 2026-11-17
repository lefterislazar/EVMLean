import Lake
open Lake DSL System

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.29.0"

package «evmlean» {
  moreLeanArgs := #["-DautoImplicit=false", "-s", "65536"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]
}

def cloneWithCache (pkg : NPackage _name) (dirname url : String) : FetchM (Job GitRepo) := do
  let repoDir : GitRepo := ⟨pkg.dir / dirname⟩
  if !(← repoDir.dir.pathExists) then dbg_trace s!"Cloning: {url}"; GitRepo.clone url repoDir
  return pure repoDir

target cloneSha2 pkg : GitRepo := cloneWithCache pkg "sha2" "https://github.com/amosnier/sha-2.git"

target cloneKeccak256 pkg : GitRepo := cloneWithCache pkg "keccak256" "https://github.com/brainhub/SHA3IUF.git"

def hash256CDir (hash256repo : GitRepo) : FilePath :=
  hash256repo.dir

abbrev compiler := "cc"

target ffi.o pkg : FilePath := do
  let sha2 ← (←cloneSha2.fetch).await
  let keccak256 ← (←cloneKeccak256.fetch).await
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "Ethereum" / "FFI" / "ffi.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", sha2.dir.toString,
    "-I", keccak256.dir.toString
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildFFILib (pkg : Package) (repo : GitRepo) (fileName : String) : FetchM (Job FilePath) := do
  let srcJob ← inputTextFile $ repo.dir / fileName |>.addExtension "c"
  let oFile := pkg.buildDir / fileName |>.addExtension "o"
  let includeArgs := #["-I", repo.dir.toString]
  let weakArgs := includeArgs
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildSha256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneSha2.fetch).await).1 fileName

def buildKeccak256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneKeccak256.fetch).await).1 fileName

extern_lib libleanffi pkg := do
  -- In the static lib we include:
  -- the `sha-256` library itself
  let sha256O ← buildSha256Obj pkg "sha-256"
  let keccak256 ← buildKeccak256Obj pkg "sha3"
  -- our own `ffi.c`
  let ffiO ← ffi.o.fetch

  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[sha256O, keccak256, ffiO]

lean_lib «Conform»

@[default_target]
lean_lib «Ethereum»

lean_exe «conform» where
  root := `Conform.Main

/-! ## Conformance test fixtures

`lake test` fetches the pinned fixtures of the conformance suite that it runs
into `.cache`, then runs `conform` on them. `conform` itself does not access
the network.
-/

/-- The `execution-spec-tests` release of the fixtures, and the SHA-256 of its `fixtures.tar.gz`. -/
def eestVersion := "21.0.2"
def eestSha256 := "e2fa7ea2ea516459f9ab92284b2927892f318f4e1f78ca802cb05a6c3b479ed9"

/-- The commits of `ethereum/tests` and `ethereum/legacytests` of the legacy suite. -/
def legacyTestsCommit := "c67e485ff8b5be9abc8ad15345ec21aa22e290d9"
def legacyLegacyTestsCommit := "1f581b8ccdc4c63acf5f2c5c1b155c690c32a8eb"

def runCommand (cmd : String) (args : Array String) : IO Unit := do
  let code ← (← IO.Process.spawn {cmd, args}).wait
  unless code == 0 do
    throw <| .userError s!"`{cmd} {" ".intercalate args.toList}` failed with exit code {code}"

def commandOutput (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output {cmd, args}
  unless out.exitCode == 0 do
    throw <| .userError s!"`{cmd} {" ".intercalate args.toList}` failed: {out.stderr}"
  return out.stdout.trimAscii.toString

/--
The directory `directory`, which `fill` fills on first use. `fill` fills a
scratch directory, which becomes `directory` once complete, so that an
interrupted fetch does not leave a partial `directory`.
-/
def cachedDirectory (directory : FilePath) (fill : FilePath → IO Unit) : IO FilePath := do
  if ← (directory / ".complete").pathExists then return directory
  let scratch : FilePath := directory.toString ++ ".partial"
  if ← scratch.pathExists then IO.FS.removeDirAll scratch
  IO.FS.createDirAll scratch
  fill scratch
  IO.FS.writeFile (scratch / ".complete") ""
  if ← directory.pathExists then IO.FS.removeDirAll directory
  IO.FS.rename scratch directory
  return directory

/-- The `blockchain_tests` fixtures of the pinned `execution-spec-tests` release, fetched into `cache`. -/
def fetchEEST (cache : FilePath) : IO FilePath := do
  IO.FS.createDirAll cache
  let archive := cache / s!"fixtures-tests-v{eestVersion}.tar.gz"
  let release ← cachedDirectory (cache / s!"tests-v{eestVersion}") fun scratch => do
    unless ← archive.pathExists do
      IO.println s!"Downloading the execution-spec-tests fixtures of tests@v{eestVersion}."
      let download : FilePath := archive.toString ++ ".partial"
      runCommand "curl" #["--fail", "--location", "--retry", "3", "--output", download.toString,
        s!"https://github.com/ethereum/execution-specs/releases/download/tests%40v{eestVersion}/fixtures.tar.gz"]
      IO.FS.rename download archive
    let sha256 := (← commandOutput "sha256sum" #[archive.toString]).splitOn " " |>.head!
    unless sha256 == eestSha256 do
      IO.FS.removeFile archive
      throw <| .userError s!"{archive} has SHA-256 {sha256}, not {eestSha256}; removed it"
    IO.println s!"Extracting {archive}."
    runCommand "tar" #["-xzf", archive.toString, "-C", scratch.toString]
  return release / "fixtures" / "blockchain_tests"

/-- The directory `directory` of the repository `repo` at `commit`, checked out as `destination`. -/
def fetchGitDirectory (repo commit directory : String) (destination : FilePath) : IO Unit := do
  IO.println s!"Fetching {directory} of {repo} at {commit}."
  let clone : FilePath := destination.toString ++ ".clone"
  let git (args : Array String) := runCommand "git" (#["-C", clone.toString] ++ args)
  runCommand "git" #["init", "--quiet", clone.toString]
  git #["remote", "add", "origin", repo]
  git #["sparse-checkout", "set", directory]
  git #["fetch", "--quiet", "--depth", "1", "--filter=blob:none", "origin", commit]
  git #["-c", "advice.detachedHead=false", "checkout", "--quiet", "FETCH_HEAD"]
  let head ← commandOutput "git" #["-C", clone.toString, "rev-parse", "HEAD"]
  unless head == commit do
    throw <| .userError s!"{repo} checked out {head}, not {commit}"
  if let some parent := destination.parent then IO.FS.createDirAll parent
  IO.FS.rename (clone / directory) destination
  IO.FS.removeDirAll clone

/--
The legacy suite, fetched into `cache`: `BlockchainTests` of `ethereum/tests`,
and `Cancun/BlockchainTests` of `ethereum/legacytests` as
`LegacyTests/Cancun/BlockchainTests`.
-/
def fetchLegacy (cache : FilePath) : IO FilePath := do
  IO.FS.createDirAll cache
  let name := String.ofList (legacyTestsCommit.toList.take 12) ++ "-" ++
    String.ofList (legacyLegacyTestsCommit.toList.take 12)
  cachedDirectory (cache / name) fun scratch => do
    fetchGitDirectory "https://github.com/ethereum/tests.git" legacyTestsCommit
      "BlockchainTests" (scratch / "BlockchainTests")
    fetchGitDirectory "https://github.com/ethereum/legacytests.git" legacyLegacyTestsCommit
      "Cancun/BlockchainTests" (scratch / "LegacyTests" / "Cancun" / "BlockchainTests")

/--
`lake test -- [OPTION]...` runs the conformance tests: the
`execution-spec-tests` fixtures, or the legacy suite with `--legacy`. It
first fetches the pinned fixtures of the suite, unless `--fixtures` names a
copy, then runs `conform` with the options (see `lake test -- --help`).
-/
@[test_driver]
script test (args) do
  let ws ← getWorkspace
  let cache := ws.root.dir / ".cache"
  let mut args := args
  unless "--help" ∈ args ∨ "--fixtures" ∈ args do
    let fixtures ←
      if "--legacy" ∈ args then fetchLegacy (cache / "legacy-tests")
      else fetchEEST (cache / "eest")
    args := args ++ ["--fixtures", fixtures.toString]
  let some conform := ws.findLeanExe? `conform
    | error "no `conform` executable"
  let conform ← ws.runBuild conform.fetch {}
  (← IO.Process.spawn {cmd := conform.toString, args := args.toArray, env := ← getAugmentedEnv}).wait
