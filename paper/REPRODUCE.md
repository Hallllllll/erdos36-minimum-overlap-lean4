# Reproducing the paper

The regular-paper manuscript *Certified Minimum Overlap in Lean with Packed Convolution and Discrete Convergence* uses the ACM SIGPLAN two-column review format. It presents the generic carry-free packed convolution certificate, exact real-shift integration for the 9,408-cell witness, and the unconditional Lean proof of discrete-to-continuous convergence (`Overlap.whiteBridge`, `Overlap.discrete_limsup_le_continuous`, and `Overlap.discrete_upper_bound`). The Lean sources in the proof artifact remain the authoritative statements.

This workspace extends the immutable v1.0.0 archive ([DOI 10.5281/zenodo.24575270](https://doi.org/10.5281/zenodo.24575270)), which covered only the eight core witness modules and treated `WhiteBridge` as an explicit premise. The exact 9,408-cell witness, rational bound `U = 2462273619527794579322422405079 / 6465103708838880000000000000000`, overlap convention, and v1.0.0 declarations remain unchanged in substance.

## Check the proof

From the repository root, fetch the pinned Mathlib cache, build the default proof target and the supplementary benchmark, then replay every named module. The root file contains imports only. CI checks the upstream declaration texts, the module inventory and the printed axiom dependencies.

```sh
lake exe cache get
lake build
# Required by the replay loop below; the default root does not import Bench.
lake build Overlap.Bench
ulimit -s unlimited
export LEAN_NUM_THREADS=1
for part in \
  Tree PackedConvolution ConvolutionExample Data Numerical Algebra \
  AffineBridge Profile Spec Main QuarticRounding CellApprox GridLower \
  LagRounding DiscreteUpper FormalConjecturesDefs FormalConjecturesBridge Bench; do
  lake env leanchecker "Overlap.$part" || exit 1
done
lake env lean scripts/paper_axioms.lean
bash scripts/check_formal_conjectures.sh
python3 -I -S -B verify.py
python3 -I -S -B audit_verify.py
python3 scripts/check_digit_guards.py
lake env lean scripts/PearlExample.lean
```

`scripts/paper_axioms.lean` audits the actual declarations across both the witness certificate and the convergence modules (`Overlap.PackedConvolution.certified`, `Overlap.ConvolutionExample.rectangular_convolution`, `Overlap.exists_cellApprox`, `Overlap.round_cube_fourth`, `Overlap.exists_balanced_lag_rounding`, `Overlap.continuousConstant_le_minimumOverlap_div`, `Overlap.discrete_limsup_le_continuous`, `Overlap.discrete_upper_bound`, and `Overlap.whiteBridge`, together with the v1.0.0 numerical and analytic declarations). Its verified stdout is archived verbatim in `paper/validation/axioms.txt`.

The Formal Conjectures source is pinned at `ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8` (Lean 4.33.1). This project uses Lean 4.36.0 and includes the four definitions with their original names in `Overlap/FormalConjecturesDefs.lean`. The bridge uses those definitions without importing the upstream problem's conjectural answer declarations. To compare the two sources directly, download the pinned problem file and pass it to the checker, as in CI.

```sh
curl -fsSL -o /tmp/erdos36-upstream.lean \
  https://raw.githubusercontent.com/google-deepmind/formal-conjectures/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/ErdosProblems/36.lean
bash scripts/check_formal_conjectures.sh /tmp/erdos36-upstream.lean
```

The review replays have separate manifests and logs for [commit `31ded31`](../docs/validation/review-44a4n7/baseline) and [the Formal Conjectures bridge](../docs/validation/review-44a4n7/final). The supplement includes the historical versions of edited input files so that the benchmark hashes for `31ded31` can still be checked offline.

`scripts/check_digit_guards.py` builds temporary diagnostic declarations against `Overlap.Numerical`. A positive control checks the original product, and changing one proposed coefficient must make that product check fail. Appending a high zero preserves the encoded integer while failing the length guard. The two lists of base B digits [B, 0] and [0, 1] have the same length and value, and [B, 0] must fail the digit range check. Rejection due to a missing tool or import counts as a test failure.

`scripts/PearlExample.lean` checks a 3-cell example (`PearlExample.toy_digits` and `PearlExample.toy_plateau`) against `Overlap.Algebra` and `Overlap.AffineBridge` and prints its axiom dependencies.

To verify that the generated Lean literals match a fresh export from the JSON witness data byte for byte, run

```sh
python3 scripts/generate.py
git diff --exit-code -- Overlap/Data.lean Overlap/Bench.lean
```

At commit `31ded31`, all 16 individual per-module `leanchecker` replays (15 proof modules totaling 111.25 s, plus `Overlap.Bench` for 116.21 s total after a 62.80 s clean build) and the then-current axiom audit passed against those frozen sources. Lean proves attainment at shift −571/1176 and global supremum U, while `audit_verify.py` verifies uniqueness across all 18,817 grid vertices directly.

For an optional full import-closure replay of all transitive Lean and Mathlib constants into an empty kernel environment (separate from the faster per-module CI workflow), run

```sh
export LEAN_NUM_THREADS=1; ulimit -s 131072; lake env leanchecker --fresh Overlap
```

On the same Linux host under a 16 GiB memory cap with swap disabled and a 600-second wall limit, that stock `--fresh Overlap` command passed with exit status 0 and silent stdout in 528.84 s wall time (511.78 s user, 13.83 s system, 4,041,076 KiB peak RSS). Raw files are archived in `benchmarks/results/linux-fresh-root/time.log`, `status.txt`, and `output.log`. Both this full import-closure check and the 16 individual per-module replays are distinct from the plain non-`--fresh` collective-prefix invocation `lake env leanchecker Overlap`, which exits 139 on both v1.0.0 and current sources even with an unlimited stack (`paper/validation/root-aggregate-139.txt`).

## Benchmarks and measurements

Table `tab:platforms` (`paper/figures/platforms.tex`) compares the historical macOS witness measurements with a Linux replay of the corresponding release and reports the upgraded Linux run separately. The archived macOS run did not record proof-source hashes.

- v1.0.0 on Apple M3 Pro (`benchmarks/results/20261127T033045Z`, `docs/benchmarks.md`), 29.24 s clean build (3.53 GiB peak RSS) and 91.54 s summed fresh replay across the 8 core proof modules, plus the five-trial standalone packed product check over prebuilt `Overlap.Data` (`lake env python3 scripts/time_product.py`, `paper/validation/product-only.jsonl`, median 8.14 s vs 0.49 s import control).
- v1.0.0 on AMD EPYC 7513 (`benchmarks/results/linux-matched-v100-045d628`), 52.24 s clean build (4.08 GiB peak RSS) and 68.29 s summed fresh replay across the same 8 core proof modules.
- Commit `31ded31` on AMD EPYC 7513 (`benchmarks/results/linux-authoritative-final-20261127T070950Z`), 62.80 s clean build (4.08 GiB peak RSS) and 111.25 s summed fresh replay across the 15 named proof modules (116.21 s across all 16 named modules including `Overlap.Bench`).
- Optional stock `--fresh Overlap` full import-closure replay on AMD EPYC 7513 (`benchmarks/results/linux-fresh-root/time.log`, `status.txt`, `output.log`), exit status 0 with silent stdout in 528.84 s wall time (511.78 s user, 13.83 s system, 4,041,076 KiB peak RSS) under `LEAN_NUM_THREADS=1`, `ulimit -s 131072`, a 16 GiB memory cap with swap disabled, and a 600-second wall limit.

To rerun the full Linux kernel suite and paired direct-sum versus packed-product scaling ladder (128, 256, 512, 1024, and 2048 cells starting at index 3136) on Linux with `systemd-run` cgroup support and `/usr/bin/time` after fetching the Mathlib cache, run

```sh
bash benchmarks/linux/run.sh
```

Use `--kernel-only` or `--scaling-only` to run one suite. The PGFPlots figure `paper/figures/linux-scaling.tex` and its data tables (`paper/validation/linux-*.dat`, `paper/validation/linux-scaling.tsv`) are generated from `benchmarks/results/linux-canonical-scaling-combined-20261127T070821Z` with `bash benchmarks/linux/render_plot.sh benchmarks/results/linux-canonical-scaling-combined-20261127T070821Z`. See `benchmarks/linux/README.md` and `docs/benchmarks.md` for options, resource caps (600 seconds and 16 GiB per process with swap disabled), timeout accounting, and the separate aggregate-prefix diagnostic (`paper/validation/root-aggregate-139.txt`).

## Venue and authorship

The manuscript follows the format of the [CPP 2027 call](https://popl27.sigplan.org/home/CPP-2027). Its paper deadline was September 10, 2026. Check the call of the intended future edition before submitting.

The human contributor selected the problem, orchestrated the agents, and set the verification standard and trusted computing boundary (excluding `sorry`, `native_decide`, and custom global axioms). For the original v1.0.0 continuous-certificate artifact, the contributor personally reviewed `Overlap/Spec.lean` and `Overlap/Main.lean` line by line to check the mathematical specification and the explicit `WhiteBridge` premise, and personally ran the full local build and separate `leanchecker` replay. Under those same constraints, AI agents generated the 9,408-cell witness, the original proof scripts, and the subsequent regular-paper upgrade modules (`Overlap/PackedConvolution.lean`, `Overlap/ConvolutionExample.lean`, `Overlap/CellApprox.lean`, `Overlap/QuarticRounding.lean`, `Overlap/LagRounding.lean`, `Overlap/GridLower.lean`, and `Overlap/DiscreteUpper.lean`), along with the expanded manuscript draft and Linux benchmarking scripts. The manuscript discloses this drafting and proof-generation assistance separately. The submitting author must review the final upgraded Lean modules, the final paper, and the target edition’s authorship requirements before submitting.

[ITP 2027's rules](https://itp-conference-2027.github.io/call-for/papers.html) preclude substantial AI-generated passages. An ITP version would require human authors to write the substantive text and to use the specified LIPIcs template. No conference submission has been made.

## Build the manuscript

Use TeX Live with `acmart`, its fonts, TikZ, `pgfplots`, `pbalance`, BibTeX, and `latexmk`. Run from the repository root.

```sh
python3 paper/metrics.py --check
bash paper/build.sh
```

The build writes `paper/main.pdf`. The paper was prepared with pdfTeX from TeX Live 2026 and acmart 2.21. The vector witness graph is included. To regenerate that graph, use Python with Matplotlib (tested with 3.11.2) and run `python3 paper/witness_figure.py`. The script checks all grid values against the exact certificate digest before mapping them to drawing coordinates.

## Package the review artifact

```sh
bash scripts/package_supplement.sh paper/reviewer-supplement.zip
```

The archive contains the pinned Lean sources, exact witnesses, both Python verifiers, adversarial controls, measurements, and scripts. Each member is listed in the included `SHA256SUMS`. It can be unpacked independently of this Git checkout.
