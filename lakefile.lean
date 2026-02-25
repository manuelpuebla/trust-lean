import Lake
open Lake DSL

package «TrustLean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

@[default_target]
lean_lib «TrustLean» where
  roots := #[`TrustLean]
