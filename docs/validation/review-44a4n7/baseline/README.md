# Baseline clean gate

This is the measured remote Linux baseline for commit `31ded31`.

- Archive-format source commit: `31ded31`
- Git archive SHA-256:
  `29afc26fcdd7fd5d7806185e6aa6e4d97f347488e8693059251c07d90ee619e6`
- Start: `2026-11-27T10:00:21Z`
- Finish: `2026-11-27T10:03:48Z`
- Whole-run elapsed time: 207 s
- Runner exit status: 0
- Source scope: 16 named `Overlap/*.lean` modules plus the import-only root
- Lean: 4.36.0
- Mathlib: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
- Package cache: all 10 manifest pins matched
- Runner command: `bash benchmarks/linux/run.sh --kernel-only`

The runner acquired the host-wide heavy-operation lock, removed only project
build output with `lake clean overlap`, ran the literal default `lake build`,
built every named module including `Overlap.Bench`, and replayed every named
module in a separate fresh `leanchecker` process. It did not run scaling.

## Results

| Scope | Result |
| --- | ---: |
| Clean command | 1.830 s, pass |
| Literal default `lake build` | 61.470 s, 4,270,936 KiB peak RSS, pass |
| Named-module builds | 16/16 pass |
| Named-module fresh replays | 16/16 pass, 103.660 s sum |
| Headline axiom script | 2.260 s, pass |
| Aggregate namespace-prefix diagnostic | exit 139, separate tool error |

All 22 declarations printed by `scripts/paper_axioms.lean` are retained in
`headline-axioms.txt`. The principal theorem dependencies are exactly
`[propext, Classical.choice, Quot.sound]`. Low-level checked literals either
depend on no axioms or, for `Overlap.peak_digit`, only `propext`.

The import-only root check passed. A text scan across all archived Lean sources
found no matches for `sorry`, `admit`, `native_decide`, `unsafe`,
`implemented_by`, `extern`, an authored `axiom`, or a debug-kernel bypass. This
is a source-text scan, not a semantic independence proof.

## Frozen inputs

`input.sha256` contains all 22 frozen inputs using repository-relative paths,
including all 16 `Overlap/*.lean` files, `Overlap.lean`, and
`scripts/paper_axioms.lean`. The hash set was captured before and after the gate
and compared byte for byte. The stability check passed.

## Raw evidence

- [`input.sha256`](input.sha256)
- [`headline-axioms.txt`](headline-axioms.txt)
- [`raw/measurements.tsv`](raw/measurements.tsv)
- [`raw/overall_status.tsv`](raw/overall_status.tsv)
- [`raw/aggregate_prefix_status.tsv`](raw/aggregate_prefix_status.tsv)
- [`protocol/bypass-scan.txt`](protocol/bypass-scan.txt)
- [`protocol/pins.tsv`](protocol/pins.tsv)
- [`protocol/input-hash-stability.tsv`](protocol/input-hash-stability.tsv)
