# Finite checks

This directory accompanies *A trace costs one quantifier: the exact complexity of perfect play in nonlocal games*. It contains eight suites, a fresh-directory runner, small reference records and generators. Large nested compiler cores are regenerated in the chosen output directory and are never shipped in this tree.

| Folder | Scope |
|---|---|
| `spatial/` | rooted tree, clock, primitive phases, exact boundary audit, minimal Boolean compiler and serialized structural audit |
| `types/` | finite selectors, group stand-ins, shift/chain scaffolds, exact golden-mean certificate, Boolean profiles |
| `zero-error/` | magic-square correspondence, flagged magic square, negative control, exact bridge and Catalan constants |
| `ii-only/` | sixteen-ary selector, separate Gram systems, equality reader, front, shared-family coordinates and three-star reduction |
| `renyi/` | weighted spectra, compact-tail formulas, Fibonacci reader bounds, comb arithmetic and nested identities |
| `capacity/` | saturation slicing, rate identity, exact parity graph certificates and common-sum extension stress models |
| `nested/` | generator, independent row/semantic/scaffold/history audits, count/hash records and synthetic degree-two input |
| `full-compile/` | literal and shared-circuit dry-count generators, independent SQLite counters and exact small boundary audit |

## Running from a relocated copy

Python 3.10 or later. Copy this entire directory to a new location, then run from any current directory:

    python -B PATH_TO_COPY/run_all.py --output-dir NEW_DIRECTORY

The output directory is required, must be new or empty and must be outside the source tree. The runner copies writable generators into the result directory. All generated cores, databases, logs and JSON certificates stay there; suite source folders are unchanged. Every child runs with isolated Python mode and bytecode writes disabled. The base suite runner is retained as `run_base.py`.

To repeat both large full-game dry counts as well:

    python -B PATH_TO_COPY/run_all.py --output-dir NEW_DIRECTORY --full-counts

To rerun the factored count while omitting only the expanded count, add `--full-counts --skip-expanded-count`.

Without `--full-counts`, the exact small audit still checks the shipped count records and the rational boundary/layout formulas. The option regenerates both word streams and independent SQLite prefix sets. It does not materialize a Boolean game. The expanded run uses several GB of memory and the full collection takes substantially longer than the base three small suites.

Dependencies: NumPy, NetworkX, SymPy, mpmath, psutil and CVXPY with CLARABEL. Numerical SDP regressions are separate from the exact parity certificate. The runner fixes BLAS thread counts to one for reproducibility. Windows memory caps use a native job object; Linux/macOS use a resource limit. Telemetry is not mathematical evidence.

The runner rejects a nonzero child exit or a real failure line. A report line `FAILURES: none` is a success summary. Small or sampled negative controls must produce precisely their expected defect. They are not failed checks.

## Regenerating the nested lists

Copy `nested/` to a fresh writable result directory and run these commands there:

    python -I -B generate_nested.py
    python -I -B check_instances.py
    python -I -B check_far_history.py
    python -I -B check_fibonacci_models.py
    python -I -B check_scaffold.py
    python -I -B check_hostile.py
    python -I -B check_programs.py
    python -I -B check_encoding_density.py
    python -I -B generate_nested.py --presentation schema-validation-input.json --output-stem schema-validation
    python -I -B check_schema.py

Do not use `--resume` for the instance audit. `expected-core-records.json` contains all five reference core byte hashes, lengths and count records. `compiler-schemas.json` states the parametric schemas. The full runner checks exact regeneration against these records. The five instances have 458,126 rational rows in total; the separate synthetic regression has 518,601. No Boolean question/predicate table is materialized. The fixed common ratio is one half for these instances; the written theorem states the dyadic variants.

For a supplied general presentation, use `generate_nested.py --presentation INPUT.json --output-stem INSTANCE`; the output stem must be a filename. This compiles the specified finite presentation, not an arbitrary verifier program merely mentioned in prose.

## Exact parity certificate

    python -I -B capacity/parity_certificates.py

This enumerates all 16,384 vertex subsets, verifies the theta Gram witness on all 39 edges, all 153 pairs of the eighteen-word code, all 48 signed coordinate permutations, the complete 14-dimensional symbolic Fourier decomposition, and the exact algebraic Schrijver optimizer. It also checks the free-word telescoping identity and the coefficient 1/18. The strong-square Schrijver number is not asserted.

`common_sum_certificates.py` checks 80 numerical common-sum extensions and the exact compression/keyed-code obstructions. These finite calculations support, and do not replace, the dimension-free proofs.

## Integrity

`SHA256SUMS` lists every shipped verification file except itself, using relative paths; the manifest uses LF line endings. Run `python -B check_hashes.py`. `results/` retains the reference outputs of the reference suites; fresh merged output is explicitly selected with `--output-dir`. The source-local records are not presented as a new run.

## Scope

Finite computations support the written proofs. They do not prove infinite-dimensional existence or extraction, compactness, the general compiler, the Higman and HNN embedding theorems, the classification of type-III factors, or any hardness reduction.

**Spatial suite.** The good-root checker tests every prime below 4000 (minimum good fraction 0.8738); its chord-bound subtest covers primes below 400. Its trigonometry is floating point; the good-phase lemma of the paper is the proof for all primes. The numerical tree checker uses (m, q, k) = (3,3,1), (3,5,2), (3,11,1), (4,3,1); all structural residuals agree to floating-point precision, and the four diagonal isometry defects are −P_m with mass 3/(4^(m+1) − 1). Its automaton is a small front-and-mark model, not the general decoder. `exact_audit.py` checks 10 models (depths 0–4, clock orders 2 and 3) with 2000 exact checks in Q(ζ₃); exactly the four top-depth source isometry rows fail. `minimal_compile.py` builds a four-bridge instance with one modular isometry and no extra transported labels: 7 input polynomials, 34 words, 887 projection variables, 748 projection rows, 27 991 questions per party and at most 256 answers. `minimal_structural.py` checks exact FMS probabilities in Q(√2), 2472 old forbidden events and 40 FMS PVMs, and its serialized audit checks 77 750 bindings, 11 652 column-graph rules, 748 row expansions and 333 scalar pair contexts. The minimal producer reuses the row compiler in `spatial/compiler/toolkit/` and the structural verifier reuses the serialized checker in `spatial/compiler/toolkit/`; this is not a second independent full-game producer, and it does not instantiate the full ten-label computation compiler. No dense full-game matrix is allocated. The runner compares the fresh compiler results with the shipped ones, ignoring timing and memory telemetry, and compares the regenerated toy tableau with the paper's worked tableau (the paper sets the automaton symbols in typewriter, so only the column specification differs).

**Type suite.** Exact rational identities cover finite binary trees through depth 7, reader stand-ins through depth 4, an actual source-lifted graph residual with the scaffold and qutrit density, finite shift truncations with their top boundary defect, and chain scaffold masses through five bridges. Group identities use 20 fixed-seed good sets, 2000 associativity, inverse and shift trials, and 240 word checks. Entropy partial sums are checked against the exact geometric-series formula. The rotation certificate encloses y = 1 and y = 2 exactly, checks the y = 3 tail base and the affine denominator inequality; the paper's induction supplies the all-integer conclusion, and the floating sweep over 1 ≤ y < 4000 (minimum log₂ margin 2.898452049757) is supplementary. The Boolean checker leaves the Weyl-clock family's finite-host coordinate unknown in every reduction and enumerates all 7581 monotone five-input functions. The finite stand-in is not a representation of an arbitrary finitely presented group or its HNN extension. `verify_margin_failure.py` supplies exact-series helpers and provides supplementary comparisons with a strict threshold of 2.9; it is not part of the main runner.

**Communication suite.** `thm1_fms.py` checks the trace-class correspondence in finite dimension on the magic square (classical independence number 5, a 6-message entangled code) and the flagged magic square (50 vertices, classical independence number 9, a 10-message entangled code), including the reverse map after a noncommutative scrambling. These reproduce finite results of Mančinska and are regression checks, not novelty claims. `l2_pitfall.py` shows that the naive marginal D² breaks zero-error orthogonality. `exact_constants.py` and `fock_catalan_numbers.py` check 4n+1, 6n+1, Ω_n, the scaffold weights, source/far ratios, convergence and criticality of the amplitude series, the five- and eight-bridge constants, the five-bridge code entropy, the squared Catalan entropy and the Catalan identities. The infinite-entropy conclusion uses Catalan asymptotics in the paper, not a finite partial sum.

## Labels inside the programs

Some program outputs use internal relation labels. In the paper's terms:

- `spatial/review/check_tree_clock.py`: (2)–(4) are the creation, range and modular relations of the Fock tree (Section 5.1); (8)–(11) the coordinate shifts and boundary projections U_x, U_y, P_x, P_y (Section 5.2); (12) the last-row and last-column projections; (13) the initial tableau conditions; (20) the Weyl relations (Section 6.1); (22)–(23) the clock W and counter C_ctr; (25)–(26) the two reader equations (Section 6.2); (31) the tableau update rule (Section 5.3); (34) the top-depth mass (Section 7.1). In the code R0 is P_∘, U and V are U_x and U_y, X and Y are P_x and P_y, E is P_ret, D is T_inv, C is C_ctr, and J, K, Z are J_W, K_W, Z_clk.
- `types/check_type_ladder.py`: "(19)–(21)" are the level-reader equations, the terminal equation and the level identity of Section 11.3.
- `zero-error/thm1_fms.py`: "Theorem 1" is the trace-class correspondence, Theorem 15.3; its question sets U, V are the paper's Q_A, Q_B.
- `types/difference_profiles.py`: "companion paper Theorem 7.1" is Theorem 7.1 here (the Weyl-clock family).

## Hashes

`SHA256SUMS` lists every file in this directory except itself, with relative paths; the manifest uses LF line endings. `python -B check_hashes.py` verifies it. Regenerate it only after intentionally changing a shipped file.
