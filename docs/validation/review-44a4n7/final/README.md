# Final clean gate

This is the measured remote Linux final gate for immutable proof commit
`cac42475e5ed0c79d85670eb2d327720f424c5d4` (`cac4247`) on branch
`review/44a4n7-formal-conjectures`. Its measured proof inputs match the commit
byte for byte.

- Proof commit:
  `cac42475e5ed0c79d85670eb2d327720f424c5d4`
- Frozen manifest SHA-256:
  `9cbf847a791f52508ebbc844081cc9136abc7b9f73d6ca778a821ec178c8ebc2`
- Start: `2026-11-27T10:06:39Z`
- Finish: `2026-11-27T10:10:38Z`
- Whole-run elapsed time: 239 s
- Runner exit status: 0
- Source scope: 18 named `Overlap/*.lean` modules plus the import-only root
- Lean: 4.36.0
- Mathlib: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
- Package cache: all 10 manifest pins matched
- Runner command: `bash benchmarks/linux/run.sh --kernel-only`

The 24-entry `input.sha256` binds the measured proof inputs by hash, and those
paths now resolve to immutable commit `cac4247`. For paper packaging, use the
full commit hash above. The runner acquired the host-wide heavy-operation lock,
removed only project build output with `lake clean overlap`, ran the literal
default `lake build`, built every named module including `Overlap.Bench` and
the two FormalConjectures modules, and replayed every named module in a
separate fresh `leanchecker` process. It did not run scaling.

## Results

| Scope | Result |
| --- | ---: |
| Clean command | 1.780 s, pass |
| Literal default `lake build` | 66.190 s, 4,272,388 KiB peak RSS, pass |
| Named-module builds | 18/18 pass |
| Named-module fresh replays | 18/18 pass, 113.880 s sum |
| Headline axiom script | 2.390 s, pass |
| Aggregate namespace-prefix diagnostic | exit 139, separate tool error |

All 24 declarations printed by `scripts/paper_axioms.lean` are retained in
`headline-axioms.txt`. The principal theorem dependencies are exactly
`[propext, Classical.choice, Quot.sound]`. Low-level checked literals either
depend on no axioms or, for `Overlap.peak_digit`, only `propext`.

The two bridge headlines are present and passed:

- `Overlap.minimumOverlap_eq_erdos36`
- `Overlap.erdos36_discrete_upper_bound`

The definitions extraction check passed against the pinned declaration digest
`3df752ddea196a20cf9d86f3258f071d10dea158bdb1852fce460dda8e43273d`.
The remote gate did not fetch the upstream source. CI performs the byte-level
comparison against the pinned upstream file. The reviewed upstream source pins
Lean 4.33.1 while this project uses Lean 4.36.0. The referenced upstream change
was open when checked, so this record covers local compatibility and theorem
exports without claiming an upstream merge.

The import-only root check passed. A source-text scan across the minimal
transferred Lean tree found no matches for `sorry`, `admit`, `native_decide`,
`unsafe`, `implemented_by`, `extern`, an authored `axiom`, or a debug-kernel
bypass. This is a source-text scan, not a semantic independence proof.

## Frozen inputs

`input.sha256` contains all 24 frozen inputs using repository-relative paths,
including all 18 `Overlap/*.lean` files, `Overlap.lean`, and
`scripts/paper_axioms.lean`. The local source was checked after transfer and
again after the gate. The remote source was checked before and after the gate.
All four comparisons passed.

The frozen logs, time reports, cgroup counters, status files, and manifests
were retained unchanged when the immutable commit identity was added to this
documentation.

## Raw evidence

- [`input.sha256`](input.sha256)
- [`headline-axioms.txt`](headline-axioms.txt)
- [`raw/measurements.tsv`](raw/measurements.tsv)
- [`raw/overall_status.tsv`](raw/overall_status.tsv)
- [`raw/aggregate_prefix_status.tsv`](raw/aggregate_prefix_status.tsv)
- [`protocol/source-state.tsv`](protocol/source-state.tsv)
- [`protocol/extraction-check.txt`](protocol/extraction-check.txt)
- [`protocol/bypass-scan.txt`](protocol/bypass-scan.txt)
- [`protocol/pins.tsv`](protocol/pins.tsv)
- [`protocol/input-hash-stability.tsv`](protocol/input-hash-stability.tsv)
- [`protocol/local-post-gate-stability.tsv`](protocol/local-post-gate-stability.tsv)
