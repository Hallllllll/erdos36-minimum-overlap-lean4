# Reproducing the paper

The anonymous manuscript uses the ACM SIGPLAN two-column review format. Its focus is the interface between a finite certificate and an analytic theorem. The Lean sources in the proof artifact remain the authoritative statements.

## Check the proof

From the repository root, fetch the pinned Mathlib cache and build the default library.

```sh
lake exe cache get
lake build
for part in Tree Data Numerical Algebra AffineBridge Profile Spec Main; do
  lake env leanchecker "Overlap.$part" || exit 1
done
python3 -I -S -B verify.py
python3 -I -S -B audit_verify.py
python3 scripts/check_digit_guards.py
lake env lean scripts/paper_axioms.lean
lake env lean scripts/PearlExample.lean
```

The last command builds temporary diagnostic declarations against the installed project modules. A positive control checks the original product; changing one proposed coefficient must make the same product test fail. Appending a high zero preserves the encoded integer, while the length guard must fail. The two lists of base-$B$ digits $[B,0]$ and $[0,1]$ have the same length and value. The former must fail the digit range check. Rejection due to a missing tool or import is a test failure.

## Venue and authorship

The manuscript follows the format of the [CPP 2027 call](https://popl27.sigplan.org/home/CPP-2027). Its paper deadline was September 10, 2026. Check the call of the intended future edition before submitting. The contributor reports selecting the problem, orchestrating the agents, setting the verification standard and trusted computing boundary, reviewing the mathematical specification and WhiteBridge premise line by line in Overlap/Spec.lean and Overlap/Main.lean, and personally running the full build and separate leanchecker replay. The agents generated the witness and proof scripts under those constraints. The manuscript discloses the drafting assistance separately. The submitting author must review the final paper and the target edition’s authorship requirements.

[ITP 2027's rules](https://itp-conference-2027.github.io/call-for/papers.html) preclude substantial AI-generated passages. An ITP version would require human authors to write the substantive text and to use the specified LIPIcs template. No conference submission has been made.

## Build the manuscript

Use TeX Live with `acmart`, its fonts, TikZ, BibTeX and `latexmk`. Run from the repository root.

```sh
python3 paper/metrics.py --check
bash paper/build.sh
```

The build writes `paper/main.pdf`. The paper was prepared with pdfTeX from TeX Live 2026 and acmart 2.21. The vector witness graph is included. To regenerate that graph, use Python with Matplotlib (tested with 3.11.2) and run `python3 paper/witness_figure.py`. The script checks all grid values against the exact certificate digest before mapping them to drawing coordinates.

## Package the review artifact

```sh
python3 scripts/package_supplement.py paper/reviewer-supplement.zip
```

The archive contains the pinned Lean sources, exact witnesses, both Python verifiers, adversarial controls, measurements and scripts. Each member is listed in the included `SHA256SUMS`. It can be unpacked independently of this Git checkout.

For the five paired process measurements, use `lake env python3 scripts/time_product.py` after building the project. The import control and the full ground equality use prebuilt data. The JSON lines on standard output contain each Lean result, elapsed nanoseconds, CPU time and per-process maximum resident set size in bytes. The archived measurements are in `paper/validation/product-only.jsonl`.
