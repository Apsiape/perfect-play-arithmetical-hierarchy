# A trace costs one quantifier: the exact complexity of perfect play in nonlocal games

Seth Douglas and Nidhal Mghirbi. Version 1.1.0, November 2026. Concept DOI (all versions): [10.5281/zenodo.23962889](https://doi.org/10.5281/zenodo.23962889).

**This is a preprint. It has not been peer reviewed.**

## Abstract

Given a finite nonlocal game, can the players win with certainty? We prove that the existence of a perfect normal spatial strategy is $\Sigma^0_2$-complete, even when restricted to games of value one, so it cannot be decided even with an oracle for the halting problem. This is strictly harder than perfect play in the finite-dimensional and commuting-operator models, which are $\Sigma^0_1$-complete and $\Pi^0_1$-complete. Within the commuting model, the existence of a perfect normal strategy with a finite or semifinite von Neumann host is $\Sigma^0_2$-complete, whereas for every fixed type $\mathrm{III}_\lambda$ subtype it has the same $\Pi^0_1$-complete language as unrestricted commuting play. A trace thus costs one existential number quantifier: the hardness constructions force every perfect strategy to choose a finite clock period or a finite tree depth. The spatial classification persists when finite entanglement entropy is required, and it is formally verified in Lean, assuming only a special case of Tarski's decision theorem. We also prove $\Sigma^0_2$-completeness for one-shot zero-error communication with normal entanglement, and construct a finite channel with zero-error codes of a given size every one of which needs infinite entanglement entropy.

## Precursor disclosure

This paper consolidates and supersedes our preprints Perfect play with spatial quantum strategies is Sigma^0_2-complete (doi:10.5281/zenodo.23910986), Perfect play has different arithmetical complexity in semifinite and type III algebras (doi:10.5281/zenodo.23925091), and One-shot zero-error communication with normal entanglement is Sigma^0_2-complete (doi:10.5281/zenodo.23924868). Theorem D and the completion of the semifinite-but-not-spatial difference classification are new here. The Π⁰₁-completeness of commuting perfection is known from Slofstra, JAMS 33 (2020), doi:10.1090/jams/929, and Mousavi-Nezhadi-Yuen, arXiv:2110.04651; Theorem B identifies its language with that of every fixed type-III subtype.

## Contents and reproduction

- `paper/main.pdf`: manuscript.
- `SHA256SUMS`: SHA-256 hashes for every shipped repository file except this root manifest; paths are relative and the manifest uses LF line endings.
- `paper/`: LaTeX source, bibliography, plain-text abstract and strict build driver. Run `python -B build.py` there with pdflatex and BibTeX installed. Its default creates a new system temporary directory; `--build-dir` selects a new or empty directory. The build disables shell escape, uses pdflatex, BibTeX and three further pdflatex passes and rejects warnings, unresolved references and box defects.
- `verification/`: finite checks in eight suites, generators, count/hash records and a runner. Start with `verification/README.md`. Run `python -B run_all.py --output-dir NEW_OR_EMPTY_DIRECTORY` there.
- `verification/SHA256SUMS`: SHA-256 hashes for every file in `verification/` except the checksum file itself, with relative paths; the manifest uses LF line endings; `python -B check_hashes.py` verifies them.
- `lean/`: Lean 4 sources. Theorem A is proved end to end in Lean, conditional only on a special case of Tarski's 1951 decision theorem for real arithmetic; the proof uses only Lean's three standard axioms, passes the kernel checkers leanchecker and nanoda, and is checked by a comparator challenge that imports only Mathlib. Theorems B-D are not checked beyond listed local lemmas; `lean/README.md` gives the exact scope and the build commands.

Finite computations support the written proofs. They do not establish infinite-dimensional extraction, compactness, group embedding theorems, type-III classification or any hardness reduction.

## Related work

- *Perfect play in a finite nonlocal game requires infinite entanglement entropy*, whose compiler toolkit this paper extends: https://doi.org/10.5281/zenodo.23902656
- *Finite games that read the type of a von Neumann algebra*: https://doi.org/10.5281/zenodo.23787124
- Precursor preprints consolidated and superseded by this paper: https://doi.org/10.5281/zenodo.23910986, https://doi.org/10.5281/zenodo.23925091, https://doi.org/10.5281/zenodo.23924868

## Citation and rights

See `CITATION.cff` for citation metadata.
Paper and documentation: CC BY 4.0. Lean sources and scripts: MIT or Apache 2.0, at your option. See `RIGHTS.md`, the license files and `NOTICE`.

## Changes in v1.1.0

Theorem A is now checked in Lean; see lean/README.md and Appendix F.

The correction doubles the one-orientation coefficient in equation (29) so that it covers games that test both ordered question pairs. See RELEASE-NOTES-v1.1.0.md.
