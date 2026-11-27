# Erdős Problem #36 · Minimum Overlap

[![Archived v1.0.0 witness-only release DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24575270.svg)](https://doi.org/10.5281/zenodo.24575270) Archived v1.0.0 witness-only artifact (8 core Lean modules)

Manuscript *Certified Minimum Overlap in Lean with Packed Convolution and Discrete Convergence* — [PDF](paper/main.pdf) · [LaTeX](paper/main.tex) · [Verification archive (ZIP)](paper/reviewer-supplement.zip) · [Reproduction guide](paper/REPRODUCE.md)

In Erdős's minimum overlap problem, one partitions {1, …, 2n} into two n-element sets A and B and counts, for each integer shift k, the overlapping pairs (a, b) ∈ A × B satisfying a − b = k. Let M(n) denote the minimum, over all such partitions, of the maximum overlap across all k ∈ ℤ. The limiting constant c = lim M(n)/n (as n → ∞) exists, while its exact value remains open. [Erdős Problem #36](https://www.erdosproblems.com/36)

Lean 4 verifies both the exact continuous overlap of a 9,408-cell rational step function and the unconditional discrete-to-continuous convergence theorem `Overlap.whiteBridge`, establishing

$$
c = \lim_{n \to \infty} \frac{M(n)}{n} \le U = \frac{2462273619527794579322422405079}{6465103708838880000000000000000}
< 0.38085601258978320592.
$$

The witness refines the November 25, 2026 Compute Substrate construction in the EinsteinArena Blob lineage. That 4,704-cell construction achieves the exact bound 123113681346619 / 323255185441944. This refinement lowers the bound by 2468195140225859198307 / 2155034569612960000000000000000 > 1.14531579911 × 10⁻⁹. Both Python verifiers recompute the parent bound directly from its original integer heights. [Parent proposal](https://explorer.computesubstrate.org/proposal.html?id=0x61ac9b0230694a2da6c369e7518c7ad186d2613659f85b1ae9c2b6f1f8f13b7e) · [Parent data on ArDrive](https://ardrive.net/IYS-L1CFuiB-2krt6PDvWIvQoztzBqE-9AvvLyfNBdY)

As a public upper bound on the minimum overlap constant, our 9,408-cell bound U was superseded on November 27, 2026 by an 18,816-cell step function posted by `willk30` in open PR #419 to `teorth/optimizationproblems` with published exact rational value 270730612195671389820648367 / 710848381933401954727231488 (< 0.3808556355), which AI-assisted verification scripts in this session also recomputed with exact packed integers from its 18,816-height dataset. The Erdős Problem a Day review (`44a4n7`) independently recomputed both our 9,408-cell witness bound U (confirming the exact score, unique maximizing shift s = −571/1176, side conditions, parent gain, and Lean-to-data equality for v1.0.0) and the superseding #419 bound, and read the Lean sources for `sorry`, `native_decide`, and custom axioms. That independent review covered witness verification and source inspection for v1.0.0, while local Lean compilation and replay of v1.0.0 and commit `31ded31` remained outside that review. [Erdős Problem a Day article](https://erdosproblemaday.com/day/36-minimum-overlap-reader-bound-checked-and-the-record-race) · [Review 44a4n7](https://erdosproblemaday.com/submission/44a4n7)

## What Lean proves

Let h be the witness density on [0, 2) and set g = 1 − h on [0, 2), extending both functions by zero outside [0, 2). Under the overlap convention

$$
H(s) = \int_{\mathbb{R}} h(x)\,g(x - s)\,dx,
$$

the function H vanishes outside [−2, 2] and is affine between consecutive grid vertices. Its supremum is attained at the shift s = −571/1176 (−2284 cells). Lean proves both attainment at this shift and that the global supremum over all real shifts equals U. Uniqueness of the maximizing shift is verified externally by the independent Python direct-sum audit across all 18,817 grid vertices (runner-up integer coefficient 4924547239052075910263140700146 at lag −3052), which together with affine interpolation implies global uniqueness over all real shifts.

| Lean declaration | Statement |
| --- | --- |
| `Overlap.witness_supremum_exact` | Unconditional. The supremum of H(s) over all s ∈ ℝ equals U. |
| `Overlap.continuous_upper_bound` | Unconditional. `continuousConstant ≤ U`. |
| `Overlap.discrete_limsup_le_continuous` | Unconditional. `limsup (M(n) / n) ≤ continuousConstant`. |
| `Overlap.discrete_upper_bound` | Unconditional. `limsup (M(n) / n) ≤ U`. |
| `Overlap.whiteBridge` | Unconditional. Proves `WhiteBridge`, namely `M(n) / n → continuousConstant` as `n → ∞`. |
| `Overlap.discrete_upper_bound_of_white` | Cleaned up in `Overlap/Main.lean`. Takes `(white : WhiteBridge)` only (no `hc` premise) and bounds `limsup (M(n) / n) ≤ U`, alongside the unconditional alternative `Overlap.discrete_upper_bound` from `31ded31`. |
| `Overlap.minimumOverlap_eq_erdos36` | Unconditional. For every `n : ℕ`, proves `minimumOverlap n = Erdos36.M n`, equating our `Fin (2 * n)` definition to the verbatim Formal Conjectures `{1, …, 2n}` definition in `ℤ`. |
| `Overlap.erdos36_discrete_upper_bound` | Unconditional. Proves `limsup Erdos36.MinOverlapQuotient ≤ U` directly in the Formal Conjectures definitions. |
| `Overlap.PackedConvolution.certified` | Unconditional. Carry-free packed-product soundness for ordinary convolution of two `List ℕ` inputs, with tree wrapper `tree_certified` and 8-by-5 example `Overlap.ConvolutionExample.rectangular_convolution`. |

In the Lean kernel, the integer convolution is verified by packing the height sequence and reversed complement sequence into two base 2¹²⁸ integers and multiplying them directly (Kronecker substitution). A coefficient bound rules out carries between base 2¹²⁸ limbs, so a single integer product certifies every grid overlap simultaneously.

For discrete-to-continuous convergence, Lean formalizes Swinnerton-Dyer's theorem, proved in Haugland (1996), which identifies the discrete limit `lim M(n) / n` with the continuous infimum. Equation (1.1) of White's 2022 preprint gives the continuous variational formulation. White attributes its equivalence with the discrete limit to Swinnerton-Dyer in the introduction. Arbitrary admissible densities are approximated by cell averages on a uniform mesh that preserve the total mass (`Overlap/CellApprox.lean`), rounded simultaneously across mass and all signed-lag constraints via a quartic potential (`Overlap/QuarticRounding.lean`), and rebalanced to exact cardinality (`Overlap/LagRounding.lean`). Embedding balanced partitions as indicator step functions yields the matching lower inequality (`Overlap/GridLower.lean`). Combining both directions in `Overlap/DiscreteUpper.lean` proves `Overlap.discrete_limsup_le_continuous`, `Overlap.discrete_upper_bound`, and `Overlap.whiteBridge` unconditionally. `Overlap/FormalConjecturesDefs.lean` extracts the four `Erdos36` definitions (`Overlap`, `MaxOverlap`, `M`, `MinOverlapQuotient`) verbatim from `google-deepmind/formal-conjectures` commit `ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8` (upstream pins Lean 4.33.1 vs our Lean 4.36.0, so only the import list is adapted and `scripts/check_formal_conjectures.sh` checks the four declaration texts byte-for-byte against upstream in CI), and `Overlap/FormalConjecturesBridge.lean` proves `Overlap.minimumOverlap_eq_erdos36` and `Overlap.erdos36_discrete_upper_bound`. The Lean proof contains no `sorry`, no `native_decide`, and no custom axioms. Further derivation details and the independent direct-sum verification appear in [PROOF.md](PROOF.md). [Haugland (1996)](https://doi.org/10.1006/jnth.1996.0064) · [White (2022/2023), eq. (1.1)](https://arxiv.org/html/2201.05704#S1)

## Comparison with archived v1.0.0 release

The Zenodo DOI [10.5281/zenodo.24575270](https://doi.org/10.5281/zenodo.24575270) points to the immutable v1.0.0 release of the earlier witness-only artifact. That release contained the 9,408-cell witness, Python verifiers, and eight core Lean modules (`Tree`, `Data`, `Numerical`, `Algebra`, `AffineBridge`, `Profile`, `Spec`, `Main`) plus `Bench`. It proved `Overlap.witness_supremum_exact` and `Overlap.continuous_upper_bound` unconditionally and took `WhiteBridge` as an explicit premise in `Overlap.discrete_upper_bound_of_white`.

The regular-paper upgrade keeps the 9,408-cell witness, exact rational bound U, overlap convention, and v1.0.0 witness theorems intact. Commit `31ded31` extracted the generic packed-convolution library (`PackedConvolution`, `ConvolutionExample`) and added five modules (`CellApprox`, `QuarticRounding`, `LagRounding`, `GridLower`, `DiscreteUpper`) proving `Overlap.whiteBridge`, `Overlap.discrete_limsup_le_continuous`, and `Overlap.discrete_upper_bound` unconditionally. Following the `44a4n7` review, the workspace further adds `Overlap/FormalConjecturesDefs.lean` and `Overlap/FormalConjecturesBridge.lean` (`Overlap.minimumOverlap_eq_erdos36` and `Overlap.erdos36_discrete_upper_bound`) and cleans up `Overlap.discrete_upper_bound_of_white` in `Overlap/Main.lean` to take `(white : WhiteBridge)` only (with no separate `hc` premise) and bound `limsup (M(n) / n) ≤ U`.

## Manuscript and benchmarks

The upgraded manuscript covers the generic carry-free packed convolution certificate, exact real-shift integration, the unconditional quartic-rounding convergence proof, and kernel replay evaluation.

Clean builds and fresh-process named-module replays (matching [paper/figures/platforms.tex](paper/figures/platforms.tex)) compare the same v1.0.0 sources across two hosts alongside the commit `31ded31` 15-proof-module snapshot (prior to adding `FormalConjecturesDefs` and `FormalConjecturesBridge`).

| Source | Host | Clean build (s) | Peak RSS (GiB) | Proof modules | Proof-only replay (s) |
| --- | --- | ---: | ---: | ---: | ---: |
| v1.0.0 | Apple M3 Pro | 29.24 | 3.53 | 8 | 91.54 |
| v1.0.0 | AMD EPYC 7513 | 52.24 | 4.08 | 8 | 68.29 |
| `31ded31` | AMD EPYC 7513 | 62.80 | 4.08 | 15 | 111.25 |

Including the supplementary 64-cell benchmark module `Overlap.Bench`, all 16 named per-module replays passed on Linux with a summed wall time of 116.21 s. The measured rows are in [`linux-authoritative-gate-pre-stack-failure-20261127T070950Z/measurements.tsv`](benchmarks/results/linux-authoritative-gate-pre-stack-failure-20261127T070950Z/measurements.tsv), while [`linux-authoritative-final-20261127T070950Z/SUMMARY.tsv`](benchmarks/results/linux-authoritative-final-20261127T070950Z/SUMMARY.tsv) is an explicitly derived normalized handoff, not a second timing run. A corrected independent rerun in [`linux-confirmed-module-gate/measurements.tsv`](benchmarks/results/linux-confirmed-module-gate/measurements.tsv) exited 0 with a 66.03 s clean build, 16/16 named replays in 98.89 s total, and a passing 2.29 s axiom probe. That rerun provides completion evidence under different shared-host background conditions and does not replace the primary 62.80 s measurement. In addition, a stock full import-closure replay `lake env leanchecker --fresh Overlap` replayed every transitive constant into an empty kernel environment and passed with exit status 0 and silent stdout in 528.84 s wall time (511.78 s user, 13.83 s system, 4,041,076 KiB peak RSS, archived in [`benchmarks/results/linux-fresh-root/time.log`](benchmarks/results/linux-fresh-root/time.log), [`status.txt`](benchmarks/results/linux-fresh-root/status.txt), and [`output.log`](benchmarks/results/linux-fresh-root/output.log)). The historical Apple M3 Pro timings in [docs/benchmarks.md](docs/benchmarks.md) apply only to the earlier v1.0.0 eight-core-module witness artifact, including the five-trial standalone packed product check over prebuilt `Overlap.Data` (median 8.14 s vs 0.49 s import control).

On the paired Linux scaling ladder ([paper/figures/linux-scaling.tex](paper/figures/linux-scaling.tex) and [docs/benchmarks.md](docs/benchmarks.md#linux-verification-and-scaling), 600-second wall and 16 GiB memory caps with swap disabled, `benchmarks/results/linux-canonical-scaling-combined-20261127T070821Z`), direct-sum elaboration grew from 25.30 s (128 cells) to 106.49 s (256 cells) and 511.66 s (512 cells, 11,907,896 KiB peak RSS) before reaching the 600-second wall cap at 1,024 cells (600.03 s, exit 124, censored). Packed elaboration completed all tested sizes up to 2,048 cells in 0.93 s to 4.39 s, with fresh-process packed replay in 4.33 s to 5.17 s.

## Reproduction

From the repository root, with `elan` and Python 3 installed, run `lake build` to build the root module `Overlap` and the 17 proof modules it imports. Build the separate `Overlap.Bench` module before the replay loop below. CI checks the verbatim Formal Conjectures four-definition extraction (`scripts/check_formal_conjectures.sh`), enforces that `Overlap.lean` contains only imports (four imports and no authored declarations), and replays every named module under `Overlap/` in its own fresh process. The over-broad collective-prefix command `lake env leanchecker Overlap` is omitted because Lean 4.36.0 exits 139 (segmentation fault) while matching the `Overlap` namespace prefix on both v1.0.0 and upgraded sources even after raising the stack limit with `ulimit -s unlimited` ([paper/validation/root-aggregate-139.txt](paper/validation/root-aggregate-139.txt)).

```sh
lake exe cache get
bash scripts/check_formal_conjectures.sh
lake build
lake build Overlap.Bench
ulimit -s unlimited
export LEAN_NUM_THREADS=1
for module in \
  Tree PackedConvolution ConvolutionExample Data Numerical Algebra \
  AffineBridge Profile Spec Main QuarticRounding CellApprox GridLower \
  LagRounding DiscreteUpper FormalConjecturesDefs FormalConjecturesBridge Bench; do
  lake env leanchecker "Overlap.$module" || exit 1
done
lake env lean scripts/paper_axioms.lean
python3 verify.py
python3 audit_verify.py
```

For an optional full import-closure replay of all transitive constants into an empty kernel environment (separate from the faster per-module CI workflow), run

```sh
export LEAN_NUM_THREADS=1; ulimit -s 131072; lake env leanchecker --fresh Overlap
```

Lean and Mathlib are pinned to v4.36.0, with `lake-manifest.json` locking Mathlib at commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Both Python verifiers rely exclusively on the standard library and run offline. To verify that the generated Lean literals match a fresh export from the JSON data byte for byte, run

```sh
python3 scripts/generate.py
git diff --exit-code -- Overlap/Data.lean Overlap/Bench.lean
```

## Kernel audit

`scripts/paper_axioms.lean` audits the actual declarations across the project, including `Overlap.minimumOverlap_eq_erdos36` and `Overlap.erdos36_discrete_upper_bound`. The following lines reproduce the axiom audit for proof commit `cac4247`. [Full output](paper/validation/axioms.txt)

```text
'Overlap.height_count' does not depend on any axioms
'Overlap.height_box' does not depend on any axioms
'Overlap.height_mass' does not depend on any axioms
'Overlap.event_count' does not depend on any axioms
'Overlap.event_peak' does not depend on any axioms
'Overlap.packed_certificate' does not depend on any axioms
'Overlap.peak_digit' depends on axioms: [propext]
'Overlap.digits_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.grid_supremum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.witness_supremum_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.continuous_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.discrete_upper_bound_of_white' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.PackedConvolution.certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.ConvolutionExample.rectangular_convolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.exists_cellApprox' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.round_cube_fourth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.exists_balanced_lag_rounding' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.continuousConstant_le_minimumOverlap_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.discrete_limsup_le_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.discrete_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.whiteBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.minimumOverlap_eq_erdos36' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.erdos36_discrete_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In the archived v1.0.0 release, `leanchecker` replayed all eight core proof modules against installed dependencies and exited with status 0. Three distinct `leanchecker` modes were run on commit `31ded31` on Linux. First, all 15 named proof modules (111.25 s) and the supplementary `Overlap.Bench` (16 modules total, 116.21 s) passed individual fresh-process `leanchecker` replays against installed imports with exit status 0. Second, the stock full import-closure check `lake env leanchecker --fresh Overlap` replayed all transitive constants (including Lean and Mathlib dependencies) into an empty kernel environment and passed with exit status 0 and silent stdout in 528.84 s wall time (511.78 s user, 13.83 s system, 4,041,076 KiB peak RSS) under `LEAN_NUM_THREADS=1`, `ulimit -s 131072`, a 16 GiB memory cap with swap disabled, and a 600-second wall limit ([time.log](benchmarks/results/linux-fresh-root/time.log), [status.txt](benchmarks/results/linux-fresh-root/status.txt), and [output.log](benchmarks/results/linux-fresh-root/output.log)). Third, the plain non-`--fresh` collective-prefix invocation `lake env leanchecker Overlap` exited 139 (segmentation fault) on both v1.0.0 and commit `31ded31` even with an unlimited stack ([paper/validation/root-aggregate-139.txt](paper/validation/root-aggregate-139.txt) and [docs/benchmarks.md](docs/benchmarks.md#aggregate-prefix-diagnostic)).

## Repository layout

| Path | Contents |
| --- | --- |
| `construction.json`, `certificate.json` | Rational heights, scale, attaining shift, exact scores, decimal enclosures, and SHA-256 digests. |
| `sources/frontier_parent.txt`, `small_cases.json` | Original parent integer heights and exhaustive small-instance data used by the verifiers. |
| `verify.py`, `audit_verify.py` | Carry-free integer-multiplication verifier and an independent direct integer-convolution audit. |
| `Overlap/Tree.lean`, `PackedConvolution.lean`, `ConvolutionExample.lean` | Packed coefficient trees, generic carry-free list-convolution theorem, and an 8-by-5 rectangular example. |
| `Overlap/Data.lean`, `Numerical.lean`, `Algebra.lean` | Exact witness data, kernel arithmetic checks, and overlap-specific digit-recovery proofs. |
| `Overlap/AffineBridge.lean`, `Profile.lean`, `Spec.lean`, `Main.lean` | Real-shift affine interpolation, step-function integrals, problem definitions, and main witness theorems. |
| `Overlap/CellApprox.lean`, `QuarticRounding.lean`, `LagRounding.lean`, `GridLower.lean`, `DiscreteUpper.lean` | Exact-mass cell approximation, quartic-potential rounding, cardinality balancing, grid lower bound, and unconditional discrete convergence (`whiteBridge`, `discrete_limsup_le_continuous`, `discrete_upper_bound`). |
| `Overlap/FormalConjecturesDefs.lean`, `FormalConjecturesBridge.lean` | Verbatim four-definition extraction from `google-deepmind/formal-conjectures` (`ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8`) and equivalence/upper-bound theorems (`minimumOverlap_eq_erdos36`, `erdos36_discrete_upper_bound`). |
| `Overlap/Bench.lean`, `scripts/generate.py`, `scripts/paper_axioms.lean`, `scripts/check_digit_guards.py`, `scripts/check_formal_conjectures.sh`, `scripts/package_supplement.sh` | Small-scale kernel benchmark, deterministic Lean data exporter, project axiom audit, digit-guard falsification checks, upstream Formal Conjectures extraction check, and reviewer-archive packager. |
| `benchmarks/linux/`, `benchmarks/results/linux-confirmed-module-gate/`, `benchmarks/results/linux-fresh-root/`, `docs/benchmarks.md`, `paper/validation/` | Linux evaluation runner and plot generator, the independent exit-0 gate, raw `--fresh Overlap` replay logs (`time.log`, `status.txt`, `output.log`), cross-platform benchmark audit, verified axiom stdout (`axioms.txt`), and separate aggregate-prefix diagnostic (`root-aggregate-139.txt`). |
| `Overlap.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Import-only library entry point (four imports, no authored declarations) and pinned toolchain/build configuration. |
| `.github/workflows/verify.yml` | CI workflow checking the upstream Formal Conjectures extraction, running the build, import-only root check, per-module named `leanchecker` replays across all 18 files under `Overlap/` with completeness check, axiom diff against `paper/validation/axioms.txt`, metrics check, data-regeneration check, and both Python verifiers. |

## Attribution and license

The human researcher selected the problem, coordinated the agents, and set the verification criteria and trusted computing base (excluding `sorry`, `native_decide`, and custom global axioms). For the original v1.0.0 continuous-certificate artifact, the researcher personally reviewed `Overlap/Spec.lean` and `Overlap/Main.lean` line by line to check the mathematical specification and the explicit `WhiteBridge` premise, and personally ran the full local Lean build and separate `leanchecker` replay.

Under those same constraints, GPT-6.2 Astra and GPT-6.2 Sol generated the 9,408-cell witness and Lean 4 proof scripts, including the regular-paper upgrade modules for generic packed convolution (`PackedConvolution`, `ConvolutionExample`), unconditional discrete-to-continuous convergence (`CellApprox`, `QuarticRounding`, `LagRounding`, `GridLower`, `DiscreteUpper`), and the Formal Conjectures bridge (`FormalConjecturesDefs`, `FormalConjecturesBridge`). AI agents also compared the extracted upstream definitions byte for byte, recomputed `willk30`'s 18,816-cell PR #419 dataset with exact packed integers in response to review `44a4n7`, drafted the manuscript, and assisted with experiments, benchmarking scripts, typesetting, and consistency checks. Luna contributed to benchmarking, DeepSeek to engineering, Terra to internal quality assurance, and Gemini edited this README. The linked parent data retain their original attribution. This project is released under the [Apache License 2.0](LICENSE).
