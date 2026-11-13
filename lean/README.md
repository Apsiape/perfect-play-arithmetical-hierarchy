# Lean verification sources

This directory proves Theorem A of *A trace costs one quantifier* in Lean 4, with no hypotheses and no axioms beyond Lean's three standard axioms. A thin core checks selected local steps of the other written proofs.

## What is checked

The comparator challenge `Challenge.lean` states Theorem A as

```lean
theorem theoremA_paper : TheoremAStatement
```

with `TheoremAStatement` as defined in `Sigma2/Statements.lean`:

```lean
def TheoremAStatement : Prop :=
  SigmaTwoComplete SpatialPerfect ∧ SigmaTwoComplete EntropyPerfect ∧
  PromiseHard SpatialPerfect PromisedGame ∧ PromiseHard EntropyPerfect PromisedGame
```

In words: for natural-number codes of finite rational Boolean two-player games, with invalid codes in neither language, the existence of a perfect normal spatial strategy (perfection is attained, not merely value one) and the existence of such a strategy with finite entropy of both reduced density operators are Sigma^0_2-complete under total computable many-one reductions, and each hardness reduction can be chosen so that every output has finite-dimensional value one and no output has a perfect finite-dimensional strategy. Section 2 of the paper explains why the one-marginal entropy convention gives the same language.

The Sigma^0_2 upper bounds use no decision procedure for real arithmetic. Each finite stage of Section 3 is a conjunction of polynomial equations and non-strict inequalities with rational coefficients, and every satisfiable stage has a solution with all coordinates in [-1, 1] (`Sigma2.UpperBoxStages.stage_boxTruth`, `Sigma2.UpperBoxStages.entropy_boxTruth`): amplitudes and probabilities lie in [0, 1], and a Gram factor of an effect in a POVM has entries of modulus at most one. For such bounded sentences, `Sigma2.UpperGridCertificate.boxTruth_iff_cert` proves that truth fails exactly when, at some grid resolution, an exact rational computation certifies that at every grid point some constraint is violated by more than its Lipschitz bound times the grid spacing. Soundness is the Lipschitz estimate and completeness is compactness of the box, so each stage is uniformly Pi^0_1 (`Sigma2.Upper.finite_stage_piOne`, `Sigma2.Upper.entropy_relaxation_piOne`). Version 1.1.0 instead assumed, as the explicit hypothesis `TarskiDecision`, that existential real arithmetic is decidable (a special case of Tarski's decision theorem); that hypothesis and its definition are removed.

The same statement is proved as `Sigma2.theoremA` in `Sigma2/Main.lean` and as `Sigma2.theoremA_paper`, through the printed admissibility predicate, in `Sigma2/MainPaper.lean`. `Sigma2.theoremA_shared_family` in `Sigma2/SharedFamily.lean` proves that a single total computable map is a promised reduction for both languages, which is the family of Theorem A.

| Printed result | Lean name | Checked form |
|---|---|---|
| Theorem A | `Sigma2.theoremA`, `Sigma2.theoremA_paper`, `Sigma2.theoremA_shared_family` | Full, with no hypotheses: both completeness clauses, both promised-hardness clauses, and one computable hardness family for both languages. |
| Lemma 4.5, n = 4 | `Sigma2.CompilerContract.lemma_4_4_strong_of_obligations`, `Sigma2.CompilerSpecification.strong_compiler`, `Sigma2.CompilerSpecification.four_bridge_compiler`, `Sigma2.CompilerObligations.obligations_all` | Partial: four-bridge exact compilation, with all seven compiler obligations proved; not general n or commuting hosts. |
| Theorem 3.1 (membership clauses); Lemma 3.2 | `Sigma2.Upper.uniform_strata_piOne`, `Sigma2.Upper.spatial_union`, `Sigma2.Upper.spatial_sigmaTwo`, `Sigma2.Upper.lemma_3_1_compact_sandwiches` | Partial: the first two clauses of Theorem 3.1 (the strata are uniformly Pi^0_1 and spatial perfection is Sigma^0_2); Lemma 3.2. |
| Section 3.2, the effective finite predicate | `Sigma2.UpperGridCertificate.boxTruth_iff_cert`, `Sigma2.UpperGridCertificate.boxTruth_piOne`, `Sigma2.UpperBoxStages.stage_boxTruth`, `Sigma2.UpperBoxStages.entropy_boxTruth`, `Sigma2.Upper.finite_stage_piOne` | The finite stages and the finite entropy relaxations are uniformly Pi^0_1, by exact rational grid certificates on the unit box; the text's real quantifier elimination is not used. |
| Proposition 3.3; Corollary 3.4; equation (5) | `Sigma2.UpperEntropyAssembly.perfect_of_sequence`, `Sigma2.Upper.entropy_tail`, `Sigma2.Upper.entropy_stage_slack`, `Sigma2.Upper.entropy_scheduled_iff`, `Sigma2.Upper.entropy_relaxation_piOne`, `Sigma2.Upper.entropy_sigmaTwo` | Partial: perfect-game compactness and effective finite-entropy membership; not prescribed-table compactness, entropy infima or optimal entropy. |
| Sections 2 and 4, normal toolkit | `Sigma2.Preliminaries.normal_pure_perfect_equivalence` | Partial: the normal/pure perfection equivalence, not all of (N1)-(N8). |
| Lemma 4.1 | `Sigma2.Compiler.lemma_4_1_normal_bridge`, `Sigma2.Compiler.calibrated_bridge_vector` | Partial: the spatial support interface and component identity; not commuting hosts. |
| Lemma 4.2 | `Sigma2.Compiler.lemma_4_2_label_refinement`, `Sigma2.Compiler.joint_refinement_iff` | Coarse-sign identification and the converse commuting refinement. |
| Lemma 4.3; equation (19) | `Sigma2.Compiler.lemma_4_3_boolean_rows`, `Sigma2.Compiler.row_loss_formula` | Conditional: perfect games, with the `RowsHold` and `NamedBinaryProjections` premises; (19) only as a trace identity under a slot-sum hypothesis, not an event probability. |
| Definition 4.4 | `Sigma2.Presentation`, `Sigma2.Presentation.admissible`, `Sigma2.NormalRealization`, `Sigma2.Compiler.Compiled`, `Sigma2.Compiler.ApproxCompiled`, `Sigma2.PaperAdmissible`, `Sigma2.PaperAdmissibility.application_paper_admissible`, `Sigma2.PaperAdmissibility.saturation_bridge` | `Presentation.admissible`, the domain of the compiler theorems, omits two transport conditions of the printed definition. `PaperAdmissible` is the printed definition; it holds for the Theorem A input tables, and every admissible presentation saturates to a `PaperAdmissible` one with equivalent normal realizations and the same compiled game. |
| Section 4.7, equations (28)-(29) | `Sigma2.CompilerSpecification.approximate_compilation`, `Sigma2.CompilerApproxBase.approxCompiled_of_base15` | Partial: an existential dimension-independent loss bound under exact structural hypotheses; not the explicit coefficient (29), robust extraction, or preservation of an input witness or its finite dimension. |
| Section 5.1, equations (30)-(33) | `Sigma2.Tree.fock_decomposition`, `Sigma2.Tree.fock_density`, `Sigma2.Tree.fock_entropy`, `Sigma2.Tree.no_finite_realization` | Rooted Fock structure, weights, entropy and finite-dimensional obstruction. |
| Lemma 5.1 | `Sigma2.Tree.lemma_5_1_definite_computation`, `Sigma2.ReductionSoundBridge.nonreject_of_data` | Classical tableau on a root-clock sector, with its concrete data from the row-extraction modules. |
| Section 6, equations (40)-(46); Lemma 6.1 | `Sigma2.Clock.finite_phase_sector`, `Sigma2.Clock.coordinate_clock`, `Sigma2.Clock.exact_return`, `Sigma2.Clock.lemma_6_1_good_primitive_phase`, `Sigma2.Clock.bounded_reader` | Conditional: `finite_phase_sector`, `coordinate_clock` and `exact_return` take `hP : P.admissible` and `D : Clock.Data R`; the last two also take a root vector, and exact return a primitive-phase eigenvector. `bounded_reader` assumes a primitive phase and its separation bound; Lemma 6.1 supplies a suitable phase and bound for every prime. `Reduction.realization_sound` supplies the clock data for Theorem A. |
| Section 7; Theorem 7.1 | `Sigma2.Reduction.effective_program`, `Sigma2.Reduction.application_admissible`, `Sigma2.Reduction.presentation_codes_computable`, `Sigma2.Reduction.realization_sound`, `Sigma2.Reduction.realization_complete`, `Sigma2.CompiledReduction.theorem_7_1_reduction` | Effective input construction, both perfection equivalences and absence of any finite-dimensional perfect output. |
| Section 7.1, equations (50)-(54) | `Sigma2.CompiledFockApproximation.normal_approximation`, `Sigma2.CompiledFockApproximation.finite_approximation`, `Sigma2.CompiledValue.four_defect_approximation`, `Sigma2.CompiledValue.value_one`, `Sigma2.CompiledValue.reduction_promised` | Partial: geometric approximation and the promise on every input; the Q, L, d of `four_defect_approximation` are existential, not the actual row counts or denominators. |
| Other local results | thin core: `THIN-CORE.md`, `theorem-map.json` | Local statements only, each marked WHOLE (the stated local assertion) or STEP (one step of the cited result). |

The first column uses the paper's numbering; `lemma_4_4_strong_of_obligations` refers to Lemma 4.5 at n = 4 and `lemma_3_1_compact_sandwiches` to Lemma 3.2. Several theorems in the table take a compiler specification `hC : CompilerSpecification.Specification f` as an argument. The final theorems supply it from the proved obligations `CompilerObligations.obligations_all`, so it is not a hypothesis of any final theorem. The final theorems take no arguments; `Sigma2/FinalProofAudit.lean` checks this.

**Not formalized:** Theorems B-D beyond their thin-core lemmas, including the general semifinite and type classification and the communication classification; Theorem 8.1 beyond its winning-functional identities, and the last two clauses of Theorem 3.1; the general n-bridge and commuting-host compiler; the economical ten-label schedule, its size counts and equation (54) with actual row denominators (the formal compiler transports all typed labels); the reduction of strategies on arbitrary Hilbert spaces to l2(N) by compression.

**Conventions:** both local spaces are l2(N), and normal states are countable ensembles of unit vectors in l2(N x N), their completed tensor product. A finite-dimensional strategy is a unit vector supported on finitely many basis vectors, with POVMs on l2(N). Every game has at least one question and one answer for each party.

## Trust base

- Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The Lean pin is in `lean-toolchain`; Git package pins are in `lake-manifest.json` and `pins/`.
- Every declaration of the `Sigma2` library, including private declarations and every theorem in the table, uses no axioms beyond Lean's three standard axioms, `propext`, `Classical.choice` and `Quot.sound`.
- The proof of Theorem A passes two independent kernel checkers, `leanchecker` and `nanoda`.
- The comparator challenge `Challenge.lean` imports only Mathlib and defines the statement vocabulary transparently. It states Theorem A as displayed above, the shared hardness family `Sigma2.theoremA_shared_family` and the printed admissibility definition `Sigma2.paper_admissible_iff`. `Solution.lean` imports the proofs, and `comparator.json` permits only the three standard axioms. The recorded comparator run used the original replay layout on Linux with bubblewrap and the command `lake comparator --config comparator.json`. The standard library build below does not repeat that comparator run or the independent kernel replays. The two theorem holes in `Challenge.lean` are the only `sorry` tokens in the project.
- Records of the comparator run and the kernel checks are in `evidence/`.

## Reproduce

Install the toolchain specified in `lean-toolchain` (Lean 4.35.0), and have Git and the tools required by Mathlib's cache available. Run these commands from `lean/`:

```sh
lake exe cache get
lake build
lake env lean -j1 -M8192 Audit.lean
```

The first command fetches the pinned Git dependencies and Mathlib's build cache. The second builds the entire `Sigma2` library from the shipped source files, including `Sigma2.AllAxioms` and `Sigma2.FinalProofAudit`; these reject project axioms and any axiom, including `sorryAx`, beyond the three permitted standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The last command prints the axiom dependencies of the 650 recorded audit roots; compare its axiom lines with `AXIOMS.txt`. Plain `lake build` does not run the old custom Python replay or rewrite `AXIOMS.txt`.

Allow at least 8 GiB of available physical memory, and run one Lean compiler process on the machine at a time. Set `LEAN_NUM_THREADS=1` (`export LEAN_NUM_THREADS=1` in a POSIX shell; `$env:LEAN_NUM_THREADS = '1'` in PowerShell). The package also passes `-j1 -M8192` to Lean. The 8192 MiB memory cap is a resource adjustment: the unchanged `Sigma2.RowCompleteness.global_axis` exceeds the old 6144 MiB cap during kernel checking with this pinned toolchain; the same file passes at 8192 MiB with identical proof source and elaboration options. Compiler thread limits alone are not a machine-wide process lock: on a machine with this restriction, serialize compiler launches with an external lock and check available memory before each build. Lake 5.0.0 at this toolchain has no `lake build -j1` option.

`lakefile.lean` requires Mathlib at commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Lake's generated `lake-manifest.json` fixes all eight transitive dependencies to the versions recorded in `pins/THIN-DEPENDENCIES.json`. No project proof imports those packages directly, so no additional direct requirements are needed. Do not run `lake update` as part of ordinary reproduction.

`Solution.lean`, `Audit.lean`, and `PaperNames.lean` remain ordinary files, checked with `lake env lean -j1 -M8192 FILE.lean`. `Challenge.lean` is the unchanged comparator statement template and deliberately contains two `sorry` holes. `lake env lean -j1 -M8192 Challenge.lean` accepts that template with two admission warnings; it is excluded from the default library build. The library and final proofs must have no admission warnings. The comparator and independent kernel checks are additional checks described above; `lake build` does not perform those external kernel replays.

### Optional: manually prepared pinned dependency sources

For the original checked-source preparation route, work in a separate copy of this directory. Clone all nine packages listed in `pins/THIN-DEPENDENCIES.json`, using each recorded URL and exact `rev`, into sibling directories named by package name. Disable Git line-ending conversion, for example:

```sh
git -c core.autocrlf=false clone https://github.com/leanprover-community/mathlib4.git mathlib
git -c core.autocrlf=false -C mathlib checkout 56a005855ea17e0b0958f73ec801ae140b0a1679
```

Repeat for `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli`, at their recorded revisions. From the separate package copy:

```sh
python -I -B prepare_dependencies.py --source-dir DIRECTORY_OF_THE_CLONES
lake -f lakefile.vendor.lean update
lake -f lakefile.vendor.lean exe cache get
lake -f lakefile.vendor.lean build
lake -f lakefile.vendor.lean env lean -j1 -M8192 Audit.lean
```

`prepare_dependencies.py` verifies the per-file hashes in `pins/DEPENDENCY-SOURCES.json` and copies only the listed dependency sources into `vendor/`; it also applies the bundled cache-tool override. The optional `lakefile.vendor.lean` uses those path packages and makes `Sigma2` the default target. Its update generates a path manifest in that separate copy, so keep the standard Git manifest in the main copy. On Windows always invoke Python with `-I`. This optional route is retained for source verification and was not part of the standard clean-build test.

`cache-tool/Requests.lean` is retained solely for that optional legacy path workflow. The standard Git workflow uses Mathlib's unmodified cache tool: a real Git checkout supplies repository identity and revision, and its inherited Git manifest agrees with the downstream manifest. There is no need to bypass Git discovery or the cache tool's manifest-consistency checks.

## License

Authored Lean sources and scripts: MIT or Apache 2.0, at your option. Documentation: CC BY 4.0. See `../RIGHTS.md`, `../NOTICE` and the root license files. Third-party rights are unchanged.
