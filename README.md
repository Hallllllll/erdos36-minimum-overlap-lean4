# Erdős Problem #36 · Minimum Overlap

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24575270.svg)](https://doi.org/10.5281/zenodo.24575270)

In Erdős's minimum overlap problem, one partitions $\{1,\ldots,2n\}$ into two $n$-element sets $A$ and $B$ and counts, for each integer shift $k$, the overlapping pairs $(a,b)\in A\times B$ satisfying $a-b=k$. Let $M(n)$ denote the minimum, over all such partitions, of the maximum overlap across all $k\in\mathbb{Z}$. The limiting constant $c=\lim_{n\to\infty} M(n)/n$ is known to exist, while its exact value remains open. [Erdős Problem #36](https://www.erdosproblems.com/36)

Lean 4 verifies the exact continuous overlap of a 9,408-cell rational step function. Applying White’s published discrete-to-continuous characterization gives

$$
c \le U = \frac{2462273619527794579322422405079}{6465103708838880000000000000000}
< 0.38085601258978320592.
$$

The witness refines the November 25, 2026 Compute Substrate construction in the EinsteinArena Blob lineage. That 4,704-cell construction achieves the exact bound $123113681346619/323255185441944$. This refinement lowers the bound by $2468195140225859198307/2155034569612960000000000000000 > 1.14531579911\times10^{-9}$. Both Python verifiers recompute the parent bound directly from its original integer heights. [Parent proposal](https://explorer.computesubstrate.org/proposal.html?id=0x61ac9b0230694a2da6c369e7518c7ad186d2613659f85b1ae9c2b6f1f8f13b7e) · [Parent data on ArDrive](https://ardrive.net/IYS-L1CFuiB-2krt6PDvWIvQoztzBqE-9AvvLyfNBdY)

## What Lean proves

Let $h$ be the witness density on $[0,2)$ and set $g=1-h$, extending both functions by zero outside $[0,2)$. Under the overlap convention $H(s)=\int_{\mathbb R} h(x)g(x-s)\,dx$, the function $H$ vanishes outside $[-2,2]$ and is affine between consecutive grid vertices. Its supremum is attained at the shift $s=-571/1176$ ($-2284$ cells). Lean proves both attainment at this shift and that the global supremum over all real shifts equals $U$, while the independent Python audit verifies uniqueness by evaluating all 18,817 grid vertices directly.

| Lean declaration | Statement |
| --- | --- |
| `Overlap.witness_supremum_exact` | The supremum of $H(s)$ over all $s\in\mathbb R$ equals $U$. |
| `Overlap.continuous_upper_bound` | The infimum of the overlap supremum over admissible densities is at most $U$. |
| `Overlap.discrete_upper_bound_of_white` | Assuming $M(n)/n \to c$ and `WhiteBridge`, we have $c\le U$. |

The first two theorems are unconditional. The third takes `WhiteBridge`—the identification of the limit of $M(n)/n$ with the continuous infimum—as an explicit hypothesis, reflecting the published characterization of the discrete limit in [White (2022), introduction and equation (1.1)](https://arxiv.org/html/2201.05704).

In the Lean kernel, the integer convolution is verified by packing the sequences into two base-$2^{128}$ integers and multiplying them directly (Kronecker substitution). A coefficient bound rules out carries between base-$2^{128}$ limbs, so a single integer product certifies every grid overlap simultaneously. The Lean proof contains no `sorry`, no `native_decide`, and no custom axioms. Further derivation details and the independent direct-sum verification appear in [PROOF.md](PROOF.md).

## Reproduction

From the repository root, with `elan` and Python 3 installed, run

```sh
lake exe cache get && lake build
for module in Tree Data Numerical Algebra AffineBridge Profile Spec Main; do
  lake env leanchecker "Overlap.$module" || exit 1
done
python3 verify.py
python3 audit_verify.py
```

Lean and Mathlib are pinned to v4.36.0, with `lake-manifest.json` locking Mathlib at commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Both Python verifiers rely exclusively on the standard library and run offline. To verify that the generated Lean literals match a fresh export from the JSON data byte for byte, run

```sh
python3 scripts/generate.py
git diff --exit-code -- Overlap/Data.lean Overlap/Bench.lean
```

## Kernel audit

Verbatim `#print axioms` output from the proof modules:

```text
info: Overlap/Numerical.lean:20:0: 'Overlap.packed_certificate' does not depend on any axioms
info: Overlap/Main.lean:133:0: 'Overlap.admissible_h' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Overlap/Main.lean:134:0: 'Overlap.grid_supremum' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Overlap/Main.lean:135:0: 'Overlap.witness_supremum_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Overlap/Main.lean:136:0: 'Overlap.continuous_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Overlap/Main.lean:137:0: 'Overlap.discrete_upper_bound_of_white' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Running `leanchecker` on all eight listed modules replayed their declarations against installed dependencies and exited with status 0.

## Repository layout

| Path | Contents |
| --- | --- |
| `construction.json`, `certificate.json` | Rational heights, scale, attaining shift, exact scores, decimal enclosures, and SHA-256 digests. |
| `sources/frontier_parent.txt`, `small_cases.json` | Original parent integer heights and exhaustive small-instance data used by the verifiers. |
| `verify.py`, `audit_verify.py` | Carry-free integer-multiplication verifier and an independent direct integer-convolution audit. |
| `Overlap/Tree.lean`, `Data.lean`, `Numerical.lean`, `Algebra.lean` | Height and coefficient trees, exact witness data, kernel arithmetic, and digit-recovery proofs. |
| `Overlap/AffineBridge.lean`, `Profile.lean`, `Spec.lean`, `Main.lean` | Real-shift affine interpolation, step-function integrals, problem definitions, and main theorems. |
| `Overlap/Bench.lean`, `scripts/generate.py` | Small-scale kernel benchmark and deterministic Lean data exporter. |
| `Overlap.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Library entry point and pinned toolchain/build configuration. |
| `.github/workflows/verify.yml` | CI workflow running the build, kernel replay, data-regeneration check, and both Python verifiers on pushes and pull requests. |

## Attribution and license

GPT-6.2 Astra and GPT-6.2 Sol assisted with the construction, formalization, and verification in Codex, and Gemini assisted with editing this README. The linked parent data retain their original attribution. This project is released under the [Apache License 2.0](LICENSE).
