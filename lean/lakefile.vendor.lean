import Lake
open Lake DSL
package sigma2lean where
  moreLeanArgs := #["-j1", "-M8192"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`maxRecDepth, .ofNat 10000⟩, ⟨`maxHeartbeats, .ofNat 4000000⟩]
require plausible from "vendor/plausible"
require LeanSearchClient from "vendor/LeanSearchClient"
require importGraph from "vendor/importGraph"
require proofwidgets from "vendor/proofwidgets"
require aesop from "vendor/aesop"
require Qq from "vendor/Qq"
require batteries from "vendor/batteries"
require Cli from "vendor/Cli"
require mathlib from "vendor/mathlib"

@[default_target]
lean_lib Sigma2 where
  globs := #[`Sigma2.+]
