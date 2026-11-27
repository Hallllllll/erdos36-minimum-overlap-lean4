# Review 44a4n7 gate records

This directory contains the sanitized remote Linux gate records for review
challenge `44a4n7`. The baseline is frozen at commit `31ded31`. The final gate
records the exact measured final snapshot now identified by immutable proof
commit `cac42475e5ed0c79d85670eb2d327720f424c5d4` (`cac4247`).

## Layout

- `baseline/input.sha256` binds the baseline proof inputs using paths relative
  to the repository root.
- `baseline/raw/` contains the complete 114-file gate result, including all
  command logs, GNU time reports, cgroup counters, TSV rows, and status files.
- `baseline/protocol/` contains the commit, archive digest, package pins,
  import-only result, module inventory, bypass scan, timestamps, and pre/post
  hash stability result.
- `final/input.sha256` uses the same relative-path format and covers every
  current `Overlap/*.lean` file, `Overlap.lean`, and
  `scripts/paper_axioms.lean`.
- `final/raw/` contains the complete 126-file final gate result.
- `final/protocol/` contains the current source state, package pins, extraction
  check, import-only result, module inventory, bypass scan, timestamps, and
  pre/post hash comparisons.

The final-gate scope includes
`Overlap/FormalConjecturesDefs.lean` and
`Overlap/FormalConjecturesBridge.lean`. The bridge exports
`Overlap.minimumOverlap_eq_erdos36` and
`Overlap.erdos36_discrete_upper_bound`. The definitions module is a
four-definition extraction whose CI check verifies extraction identity against
the pinned upstream source. The reviewed upstream source pins Lean 4.33.1 while
this project uses Lean 4.36.0. The referenced upstream change was open when
checked, so these records describe compatibility work and local theorem
exports without claiming an upstream merge.

For paper packaging, cite `cac42475e5ed0c79d85670eb2d327720f424c5d4` as the
immutable final proof commit. The 18/18 clean build and 113.880 s replay total
were measured from the exact proof inputs whose hashes match this commit. The
frozen raw evidence was retained without modification when the commit identity
was added.

No endpoint, account, credential, control-socket, or private home-directory
string is retained in this directory.
