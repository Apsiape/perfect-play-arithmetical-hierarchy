# Sigma2 thin checked core — 4 November 2026

Lean kernel-checks the 601 listed proof roots for the concrete row-game construction, selected actual-support and matrix-unit arguments, bridge/refinement and row-algebra steps, fixed-n=4 application syntax, word-coordinate and scalar Fock-entropy calculations, local clock/reader implications, elementary winning-functional identities, and the good-primitive-phase lemma for every prime. Only `propext`, `Classical.choice` and `Quot.sound` occur as solution axioms. Theorem A and the complete compiler, extraction and reduction are not Lean-checked.

## Exact scope

This package certifies the listed finite constructions and proof steps in the spatial l2 model of countable normal ensembles: purification and support/matching facts; actual flagged magic-square matrix units, calibration and component bridge identities; label-refinement soundness and its algebraic joint-product criterion; projection graph/triangle identities and centralizer contraction encoding; the concrete Boolean rational-row game, rational slot identities, old-game restriction and finite regressions; Pauli relations for the actual four measured scalar axes derived from perfection; one common full matrix-unit system and its algebraic marginal-density blocks on Alice’s original support; sharp new effects, Alice global-bit identification and spectral action, and the exact positive-weight component-mirror clause of RowsHold; creation-word covariance and coordinate actions, the normalized Fock-word entropy series and the fixed-ratio finite-dimensional obstruction; the finite Weyl determinant identity, the reader-kernel implication under an injective-counter premise, word-level clock/counter recurrences and the scalar bounded-reader formula under its explicit good-phase premise; and the two elementary winning-functional identities. It additionally proves syntactic admissibility of the actual fixed n=4 application row table, including all generated transition and endpoint rows, and the good-primitive-phase lemma for every prime: a primitive qth root ζ exists with (1/2)^(t+1) ≤ ‖ζ^t-1‖ for every positive t not divisible by q. No complete Hilbert-space tensor-coordinate realization is certified by the algebraic matrix-unit conclusions. The release does not prove the full Boolean-row soundness or completeness theorem, the n-bridge compiler, Fock decomposition/exhaustiveness, a finite clock phase sector, support-wide counter injectivity, exact-return extraction, effective program construction, the end-to-end reduction, compactness/upper bounds, or any main undecidability/completeness theorem, including Theorem A. All own-paper results used as proofs in this package are proved; no named own-paper theorem is installed as a hypothesis or axiom. There are no separately supplied published-theorem hypotheses. Only propext, Classical.choice and Quot.sound are permitted as logical axioms.

`Presentation.admissible` checks a partial fixed-n=4 syntax contract. In addition, paper admissibility requires transport of the root and of every label used to the left of a creation symbol in a linear endpoint sum. The actual `applicationPresentation` satisfies both additional requirements: its root is transported and its linear-endpoint-sum list is empty. No generic compiler theorem is certified.

`RowsHold` records component mirrors and row equations on the actual marginal supports. The paper's synchronized-projection premise is represented by `NamedBinaryProjections R S` in addition to `RowsHold R S`; `RowsHold` alone permits nonprojective effects. The certified row-mirror result proves only the mirror clause for the old-strategy restriction of the concrete extended game.

## Pins and prerequisites

- Lean `leanprover/lean4:v4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Mathlib's 8,624 mathematical library Lean sources match official commit `56a005855ea17e0b0958f73ec801ae140b0a1679` byte for byte. The supplied vendor tree has three local changes in `Cache/Requests.lean` that disable repository detection, automatic Git-head cache scoping, and a manifest-mismatch check. That cache-tool module is outside the proof source import closure. This verification reuses dependency oleans and does not rebuild Mathlib from zero. All transitive pins are in `lake-manifest.json`.
- Python 3; the pinned toolchain supplies `lean`, `leanexport`, `lake` and its kernel comparator. Linux sandboxed comparison requires bubblewrap. Windows additionally needs the normal Git-for-Windows Unix lookup helpers on PATH; the verifier only resolves executable paths and runs no git commands.
- Install the pinned dependencies and matching Mathlib cache before verification. Dependency acquisition is a separate setup step. The source-only archive contains no toolchain, vendor packages, cached oleans, NDJSON exports or admitted blueprint.

From this directory, after setup:

```sh
python -B verify.py
```

An existing offline dependency cache may instead be selected explicitly:

```powershell
python -B verify.py --dependency-dir /path/to/pinned/vendor --lean-bin /path/to/pinned/lean/bin
```

The default verifier freshly rebuilds every copied project module, then both comparator modules and `Audit.lean`; it reuses pinned dependency cache artifacts. A later local `--incremental` run can reuse only this verifier’s matching source-hash and dependency-timestamp records. All compilers run serially with `LEAN_NUM_THREADS=1`, `-j1 -M6144`, and the Windows process tree is capped at 10,000,000,000 committed bytes. The direct worker honors Mathlib’s pinned `-DmaxSynthPendingDepth=3`. This is not a from-zero rebuild of all Mathlib.

## What is checked

`Audit.lean` prints axioms for every listed proof, including all eight ordinary-`decide` regressions. `AXIOMS.txt` freezes the successful compiler output. `theorem-map.json` gives all 601 named checked theorem roots and their supporting authored declarations, its source, stable merged-paper labels and its whole-statement/step status. It separately identifies supporting definitions. Generated constructor/recursor/equation artifacts and private implementation helpers are covered transitively by the proof-root audits. Module names and source comments retain some precursor numbers; the theorem-map labels control attribution. Printed PDF references are observations from the recorded PDF hash and are marked **to re-sync**. Precursor `thm:B` is merged-paper `lem:rows`; the broader merged-paper bridge and compiler statements are not credited merely from an algebraic step.

`Challenge.lean` contains one intentional `sorry` placeholder per proposition; `Solution.lean` proves the exact same proposition with the corresponding checked theorem. `type_of% (@declaration)` copies its kernel type exactly without pretty-printer abbreviation or truncation. It does not import a proof as a new axiom. The common proof modules and solution contain no admissions. `comparator.json` uses the leanprover/comparator schema, with only the three permitted logical axioms. The bundled exporter and comparator check the closed solution proof terms and type equality in the Lean kernel.

On Linux, the normal sandboxed invocation is:

```sh
lake comparator --config comparator.json
```

For trusted local Windows sources, `verify.py` supplies exports and passes `--inadvisably-no-sandbox` because the pinned CLI’s adversarial sandbox is unavailable on Windows. A successful local run verifies proof terms, types and permitted axioms; it does not test adversarial process isolation. The comparator’s sandbox warning is retained verbatim in the verification record.

Unproved blueprint declarations and proof-dependent wrappers are omitted from this source-only release. The archive and its historical verification records are identified by their checksums; no build artifacts or dependencies are bundled.

## License

The authors' Lean sources and verification scripts are licensed under MIT or Apache 2.0, at your option; documentation and recorded outputs are CC BY 4.0. See `../RIGHTS.md`, the three root license files and `../NOTICE`. These grants do not alter rights in third-party material.

Machine-local dependency-cache and executable paths in the historical `verification-summary.json` are replaced by portable placeholders. Its results, timings and exit records are unchanged.
