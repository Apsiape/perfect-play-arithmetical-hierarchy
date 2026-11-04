# A trace costs one quantifier: the exact complexity of perfect play in nonlocal games

Seth Douglas and Nidhal Mghirbi. Preprint, November 2026.

**This is a preprint. It has not been peer reviewed.**

## Abstract

Given a finite nonlocal game, can the players win with certainty? We find the exact level of the arithmetical hierarchy at which this is decided, for each standard model of quantum strategy. With normal states on tensor products of Hilbert spaces, perfect play is $\Sigma^0_2$-complete, also when the strategy must have finite entanglement entropy, so it cannot be decided even with an oracle for the halting problem. This completes a table in which finite-dimensional perfection is $\Sigma^0_1$-complete, commuting perfection is $\Pi^0_1$-complete and value one is $\Pi^0_2$-complete. Inside the commuting model the answer depends on the von Neumann type of the players' algebra: perfect play in a type $\mathrm{II}_1$ algebra, or in any semifinite algebra, is $\Sigma^0_2$-complete, while in a type $\mathrm{III}_\lambda$ factor, for each fixed $\lambda\in[0,1]$, it is equivalent to commuting perfection. In this sense a trace costs one existential quantifier. Commuting perfect play without semifinite perfect play is $\Pi^0_2$-complete; the remaining semifinite-without-spatial differences are $D_2(\Sigma^0_2)$-complete. In the hardness proofs the existential witness is a finite object that every perfect strategy must choose: the order of a clock phase in the spatial model, or the depth of a critical binary tree in semifinite algebras. The same level governs communication: deciding whether a finite classical channel can send a given number of messages in one use with zero error, helped by normal entanglement, is $\Sigma^0_2$-complete, and some channel's zero-error codes all need infinite entanglement entropy. Positive computable moment orders below one form a strict $\Sigma^0_2$-complete resource ladder; the infimal critical indices of spatially perfect games (attained by the realizing games) are exactly the right-c.e.-in-$0'$ reals in $[0,1]$.

## Precursor disclosure

Earlier versions of Theorems A, B and C, of Theorems 3.1 and 8.1, of the trace-class correspondence, of the summability threshold, of the commuting row and of the I-only and infinite-entropy-only classifications appeared in our preprints Perfect play with spatial quantum strategies is Sigma^0_2-complete (doi:10.5281/zenodo.23910986), Perfect play has different arithmetical complexity in semifinite and type III algebras (doi:10.5281/zenodo.23925091), and One-shot zero-error communication with normal entanglement is Sigma^0_2-complete (doi:10.5281/zenodo.23924868), which this paper consolidates and supersedes. Apart from those preprints we know of no prior statement of these results; Theorem D and the completion of the semifinite-but-not-spatial cells are new here. The Π⁰₁-completeness of commuting perfection is known from Slofstra, Tsirelson's problem and an embedding theorem for groups arising from non-local games, JAMS 33 (2020), doi:10.1090/jams/929, and Mousavi-Nezhadi-Yuen, Nonlocal Games, Compression Theorems, and the Arithmetical Hierarchy, arXiv:2110.04651; what is new in Theorem B is that every fixed type-III subtype has exactly that language.

## Contents and reproduction

- `paper/main.pdf`: manuscript.
- `SHA256SUMS`: SHA-256 hashes for every shipped repository file except this root manifest; paths are relative and the manifest uses LF line endings.
- `paper/`: LaTeX source, bibliography, plain-text abstract and strict build driver. Run `python -B build.py` there with pdflatex and BibTeX installed. Its default creates a new system temporary directory; `--build-dir` selects a new or empty directory. The build disables shell escape, uses pdflatex, BibTeX and three further pdflatex passes and rejects warnings, unresolved references and box defects.
- `verification/`: finite checks in eight suites, generators, count/hash records and a runner. Start with `verification/README.md`. Run `python -B run_all.py --output-dir NEW_OR_EMPTY_DIRECTORY` there.
- `verification/SHA256SUMS`: SHA-256 hashes for every file in `verification/` except the checksum file itself, with relative paths; the manifest uses LF line endings; `python -B check_hashes.py` verifies them.

- `lean/`: the source-only thin core, its exact scope, theorem-to-paper map, pins, verifier and checksums. Lean kernel-checks 601 listed proof roots for the specified local constructions and implications. Theorem A and the complete compiler, extraction and reduction are not Lean-checked. See `lean/README.md` for the two interface qualifications and the dependency-cache qualification.

Finite computations support the written proofs. They do not establish infinite-dimensional extraction, compactness, group embedding theorems, type-III classification or any hardness reduction.

## Related work

- *Perfect play in a finite nonlocal game requires infinite entanglement entropy*, whose compiler toolkit this paper extends: https://doi.org/10.5281/zenodo.23902656
- *Finite games that read the type of a von Neumann algebra*: https://doi.org/10.5281/zenodo.23787124
- Precursor preprints consolidated and superseded by this paper: https://doi.org/10.5281/zenodo.23910986, https://doi.org/10.5281/zenodo.23925091, https://doi.org/10.5281/zenodo.23924868

## Citation and rights

See `CITATION.cff` for citation metadata.
Paper and documentation: CC BY 4.0. Lean sources and scripts: MIT or Apache 2.0, at your option. See `RIGHTS.md`, the license files and `NOTICE`.
