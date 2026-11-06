import Lake
open Lake DSL
package sigma2lean where
  moreLeanArgs := #["-j1", "-M6144"]
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
lean_lib Sigma2 where
  globs := #[`Sigma2.+]

-- These targets use the same serial, memory-capped source replay as the default build.
target Challenge pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-B", (pkg.dir / ".." / "work" / "build-core.py").toString, "--resume", "--read-only-source"]
           cwd := some pkg.dir }

target Solution pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-B", (pkg.dir / ".." / "work" / "build-core.py").toString, "--resume", "--read-only-source"]
           cwd := some pkg.dir }

/-- Replay the final-root audit with the bundled checked-cache dependencies. -/
@[default_target]
target core pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-B", (pkg.dir / ".." / "work" / "build-core.py").toString]
           cwd := some pkg.dir }
