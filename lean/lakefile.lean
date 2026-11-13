import Lake
open Lake DSL

package sigma2lean where
  moreLeanArgs := #["-j1", "-M8192"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`maxRecDepth, .ofNat 10000⟩, ⟨`maxHeartbeats, .ofNat 4000000⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib Sigma2 where
  globs := #[`Sigma2.+]
