import Lake
open Lake DSL System

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.29.0"

package «evmlean» {
  moreLeanArgs := #["-DautoImplicit=false", "-s", "65536"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]
}

lean_lib «Conform»

@[default_target]
lean_lib «Ethereum»

@[test_driver]
lean_exe «conform» where
  root := `Conform.Main

lean_exe «gigahorse» where
  root := `Gigahorse.Main

lean_lib «CryptoTests»

/-- Tests of the cryptographic primitives against reference vectors. -/
lean_exe «crypto-tests» where
  root := `CryptoTests.Main
