This directory is a derived presentation of the first raw gate. That raw gate
passed the clean build and all 16 named modules, then exited 1 when the extra
aggregate-prefix diagnostic exited 139. This directory combines those unchanged
timing rows with the independent frozen-hash axiom run and marks the aggregate
row diagnostic-only. A later corrected `--kernel-only` run can supersede this
derived summary without changing the measured values here.

Required checks cover every authored Lean declaration through the 16 named
module replays. Overlap.lean is import-only. Aggregate `leanchecker Overlap`
exited 139 under both default and unlimited stack limits.

A separate stronger check, `leanchecker --fresh Overlap`, completed with status
0 in 528.84 s. Its raw `/usr/bin/time -v` report is under `fresh-overlap/`.
