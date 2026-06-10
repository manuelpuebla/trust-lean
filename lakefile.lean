import Lake
open Lake DSL

package «TrustLean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

require leanExtensions from git
  "https://github.com/lambdaclass/lean_extensions.git" @ "a78bc66074108f7f859bf99251c791e8b2cc2e36"

target axiomGuardPlugin : Dynlib := do
  let some lib ← findLeanLib? `LeanExtensions | error "could not find the `LeanExtensions` lean_lib"
  lib.shared.fetch

@[default_target]
lean_lib «TrustLean» where
  roots := #[`TrustLean]
  plugins := #[axiomGuardPlugin]
  leanOptions := #[⟨`linter.axiomGuard.allowedAxioms, "Lean.trustCompiler, Lean.ofReduceBool, Lean.ofReduceNat"⟩]

lean_lib «Tests» where
  roots := #[`Tests]
  globs := #[.submodules `Tests]
  plugins := #[axiomGuardPlugin]
  leanOptions := #[⟨`linter.axiomGuard.allowedAxioms, "Lean.trustCompiler, Lean.ofReduceBool, Lean.ofReduceNat"⟩]
