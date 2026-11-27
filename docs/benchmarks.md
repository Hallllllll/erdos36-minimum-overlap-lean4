# Lean build and kernel replay benchmarks

## Run conditions

Canonical run: `20261127T033045Z` (UTC), on macOS 27.2 build 26B123, Apple M3 Pro, arm64, 11 logical CPUs, 19,327,352,832 bytes RAM. Lean 4.36.0 (`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`), Lake 5.0.0, Python 3.13.2. Mathlib is locked to commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (v4.36.0). See [`environment.json`](../benchmarks/results/20261127T033045Z/environment.json) and the individual raw command logs.

The harness first ran `lake clean overlap`, which removes the root package's build outputs while retaining `.lake/packages` and their compiled dependencies. It then invoked one `lake build Overlap.<Module>` command at a time in dependency order: `Tree`, `Data`, `Numerical`, `Algebra`, `AffineBridge`, `Profile`, `Spec`, `Main`, and `Bench`. No two Lake commands from this harness overlapped. Lake's normal scheduler remained enabled within each invocation. Each row is the wall time and process peak RSS for that Lake invocation, including Lake startup, dependency checks, and any work needed for that target. Previously completed project targets were reused by later module commands; these are ordered per-target build times, not nine independent clean builds.

The standalone project build is a separate clean measurement: after the module sequence, the harness ran `lake clean overlap` and timed the default `lake build` command. It completed successfully. Since that clean removes the standalone Bench artifact, `lake build Overlap.Bench` was then run explicitly before the Bench replay.

Every replay is a separate fresh `lake env leanchecker <Module>` process. The eight primary modules are `Overlap.Tree`, `Overlap.Data`, `Overlap.Numerical`, `Overlap.Algebra`, `Overlap.AffineBridge`, `Overlap.Profile`, `Overlap.Spec`, and `Overlap.Main`. Bench is reported separately. Replay time covers Lake environment startup and leanchecker checking the named compiled module against its imports; it is not an isolated timing for one theorem. Lean's elaboration/build time and leanchecker replay time are separate measurements. No per-theorem kernel timings are claimed.

Wall seconds use the parent monotonic clock around `/usr/bin/time -l` and include that wrapper's small overhead. Peak RSS is Darwin `/usr/bin/time -l`'s `maximum resident set size`, stored in bytes. Raw logs preserve the complete stdout, stderr, and Darwin time report. Paths are scrubbed from logs. `GIT_CONFIG_COUNT` is removed from child environments.

## Results

Per-target serialized build sequence:

| Module target | Wall (s) | Peak RSS (bytes) | Exit |
| --- | ---: | ---: | ---: |
| Tree | 1.573821 | 707756032 | 0 |
| Data | 11.650346 | 1303724032 | 0 |
| Numerical | 11.605416 | 1045020672 | 0 |
| Algebra | 23.324014 | 2965356544 | 0 |
| AffineBridge | 8.533626 | 3151872000 | 0 |
| Profile | 5.543433 | 3177857024 | 0 |
| Spec | 10.216921 | 3059597312 | 0 |
| Main | 16.051525 | 3733700608 | 0 |
| Bench | 1.786841 | 709148672 | 0 |

Standalone clean default `lake build`: **29.241202 s**, peak RSS **3785310208 bytes**, exit 0. Explicit post-clean Bench rebuild: **1.772497 s**, peak RSS **708116480 bytes**, exit 0.

Fresh-process `leanchecker` replays:

| Module | Wall (s) | Peak RSS (bytes) | Exit |
| --- | ---: | ---: | ---: |
| Tree | 8.345961 | 706592768 | 0 |
| Data | 6.720291 | 706543616 | 0 |
| Numerical | 13.105423 | 1039548416 | 0 |
| Algebra | 14.814267 | 2520317952 | 0 |
| AffineBridge | 8.667233 | 2681831424 | 0 |
| Profile | 7.459754 | 2678358016 | 0 |
| Spec | 7.283710 | 2677800960 | 0 |
| Main | 25.139319 | 2941075456 | 0 |
| Bench (supplementary) | 6.576502 | 706412544 | 0 |

## Paired direct and packed prefixes

`prefix_scaling.py` generates 16-, 32-, and 64-cell nested prefixes from the same 64-cell sample used in `Overlap.Bench`. For each size, it creates two Lean modules over the same input coefficients and expected event coefficients. The direct module states every signed-lag coefficient as an explicit finite sum of products and proves list equality to the shared expected event data with `decide +kernel`. The packed module proves the corresponding base-`2^128` integer product equals the packed shared event data, also with `decide +kernel`. The direct terms are quadratic in prefix length; this experiment stops at 64 cells and does not run a full-size quadratic check.

Each generated module is elaborated and written to OLean in one fresh Lean process, then replayed in a separate fresh `leanchecker` process. The table reports both phases separately; these are whole-process measurements, not per-theorem timings.

| Cells | Direct elaboration (s / bytes) | Direct replay (s / bytes) | Packed elaboration (s / bytes) | Packed replay (s / bytes) |
| ---: | ---: | ---: | ---: | ---: |
| 16 | 2.088098 / 706641920 | 7.292481 / 706641920 | 1.679122 / 706560000 | 8.838542 / 706822144 |
| 32 | 3.975780 / 703954944 | 10.969141 / 701317120 | 4.825991 / 699006976 | 7.527125 / 706756608 |
| 64 | 7.164908 / 704970752 | 11.412471 / 705593344 | 6.646754 / 699138048 | 9.698377 / 703430656 |

No extrapolation from these three prefixes is made. The paired modules, exact generated source, JSONL rows, and raw logs are retained in the run archive.

## Linux verification and scaling

The Linux worker is an AMD EPYC 7513 system with 32 physical cores, 64 logical
CPUs, 101,175,894,016 bytes of hardware memory, Ubuntu 24.04.4 LTS, kernel
`7.0.0-42-generic`, and 366,777,634,816 bytes free on `/` at measurement time.
The host cgroup exposes the full `0-63` CPU set with `cpu.max=max 100000` and
`memory.max=max`. Every benchmark child instead ran in a transient
`systemd-run` scope with a 16 GiB memory maximum, swap disabled, and a 600-second
wall timeout. `LEAN_NUM_THREADS=1` restricted each named replay to one Lean
worker. See [`environment.tsv`](../benchmarks/results/linux-canonical-scaling-combined-20261127T070821Z/environment.tsv).

The host was shared. Background activity was not CPU-isolated or comprehensively
recorded, and unrelated Lean builds ran during
the upgraded gate. Linux wall times are therefore operational observations, not
a controlled hardware ranking. They use GNU `/usr/bin/time -v`; the archived
Apple observations use Darwin `/usr/bin/time -l`. The table compares the archived witness-only Apple run with a Linux checkout of v1.0.0. The Apple log identifies its modules and software versions. Repository history identifies its source revision. The Apple run directory has no contemporaneous proof-source hash manifest.

### Matched clean witness build

The source hash and pins were fixed at the v1.0.0 witness-only revision. Each
row below is one whole-process command. "Eight replays" excludes the separate
64-cell `Bench` module.

| Platform | Clean default build | Peak RSS | Eight fresh core replays |
| --- | ---: | ---: | ---: |
| Apple M3 Pro, archived run | 29.241202 s | 3,785,310,208 bytes (3,610.9 MiB) | 91.54 s total |
| AMD EPYC 7513, matched Linux run | 52.240 s | 4,275,684 KiB (4,174.5 MiB) | 68.29 s total |

The Linux `Bench` replay took 5.400 s versus 6.576502 s in the Apple archive.
The matched raw Linux directory is
[`linux-matched-v100-045d628`](../benchmarks/results/linux-matched-v100-045d628).
Names in that runner's final status file include an optional aggregate-prefix
attempt that exited 139. The eight named proof modules and `Bench` all passed
separately.

### Upgraded clean gate

The frozen upgraded sources contain 16 named modules under `Overlap/`: the
original eight proof modules, seven new convolution, rounding, and discrete
convergence modules, plus the separate `Bench` module. The first clean-module
row was exactly `lake build` immediately after `lake clean overlap`. All 16
named `leanchecker` processes passed separately, with a summed fresh-process
wall time of 116.21 s.

| Scope | Wall (s) | Peak RSS (KiB) | Result |
| --- | ---: | ---: | --- |
| Clean literal `lake build` | 62.800 | 4,273,232 | pass |
| 16 named-module replays, summed | 116.210 | 3,847,844 maximum | pass |
| `lake env lean scripts/paper_axioms.lean` | independent signoff | not timed | pass |

The measured rows from the first gate are retained in
[`linux-authoritative-gate-pre-stack-failure-20261127T070950Z/measurements.tsv`](../benchmarks/results/linux-authoritative-gate-pre-stack-failure-20261127T070950Z/measurements.tsv).
The
[`linux-authoritative-final-20261127T070950Z/SUMMARY.tsv`](../benchmarks/results/linux-authoritative-final-20261127T070950Z/SUMMARY.tsv)
is a derived normalized handoff, not a second timing run. Its aggregate-prefix
row records a toolchain failure, not a named-module failure. The expanded
[axiom output](../benchmarks/results/linux-authoritative-final-20261127T070950Z/independent-signoff/axioms.txt)
and its frozen-source hash manifest are stored beside the timing rows. The
compact manuscript input is
[`linux-upgraded-gate.tsv`](../paper/validation/linux-upgraded-gate.tsv).

A later full rerun of the corrected runner,
[`linux-confirmed-module-gate`](../benchmarks/results/linux-confirmed-module-gate/measurements.tsv),
completed with process exit 0. It recorded a 66.03 s clean build, 16/16 named
replays passing in 98.89 s total, the expanded axiom probe passing in 2.29 s,
and the aggregate prefix still exiting 139 separately. The canonical manuscript
timing table keeps the earlier 62.80 s build and 116.21 s all-named replay totals
as requested. The later rerun is completion/status evidence under different
shared-host background conditions, not a replacement timing sample.

### Review 44a4n7 baseline and final gates

The review baseline is the exact `git archive` of commit `31ded31`, with
archive SHA-256
`29afc26fcdd7fd5d7806185e6aa6e4d97f347488e8693059251c07d90ee619e6`.
It was extracted into an isolated remote directory that reused the matching
compiled dependency cache. All 10 package pins matched. The baseline contains
the 16 named modules present at that commit and does not include the later
FormalConjectures bridge modules.

| Scope | Result |
| --- | ---: |
| Literal default `lake build` | 61.470 s, 4,270,936 KiB |
| Named-module builds | 16/16 pass |
| Named-module fresh replays | 16/16 pass, 103.660 s total |
| Headline axiom script | 2.260 s, pass |
| Aggregate namespace-prefix diagnostic | exit 139, separate |

The gate ran from `2026-11-27T10:00:21Z` through
`2026-11-27T10:03:48Z` and exited 0. The clean project build ran immediately
after `lake clean overlap`. Every named module was built in a separate capped
process before replay. The 22-entry
[`input.sha256`](validation/review-44a4n7/baseline/input.sha256) uses
repository-relative paths, covers `Overlap.lean`, every `Overlap/*.lean` file,
and `scripts/paper_axioms.lean`, and matched the source before and after the
gate. The source scan found no proof-bypass tokens.

The sanitized raw result and protocol record are under
[`docs/validation/review-44a4n7/baseline`](validation/review-44a4n7/baseline).

The confirmed final gate used the exact proof snapshot identified by immutable
commit `cac42475e5ed0c79d85670eb2d327720f424c5d4` (`cac4247`), including both
FormalConjectures modules. Its 24-entry manifest has SHA-256
`9cbf847a791f52508ebbc844081cc9136abc7b9f73d6ca778a821ec178c8ebc2`. The
proof paths in the measured snapshot match this commit byte for byte.

| Scope | Final result |
| --- | ---: |
| Literal default `lake build` | 66.190 s, 4,272,388 KiB |
| Named-module builds | 18/18 pass |
| Named-module fresh replays | 18/18 pass, 113.880 s total |
| Headline axiom script | 2.390 s, pass |
| Aggregate namespace-prefix diagnostic | exit 139, separate |

The final gate ran from `2026-11-27T10:06:39Z` through
`2026-11-27T10:10:38Z` and exited 0. The 24 headline outputs include
`Overlap.minimumOverlap_eq_erdos36` and
`Overlap.erdos36_discrete_upper_bound`, both with standard Lean axioms. The
four-definition extraction digest passed against the pinned expected digest.
The import-only root and zero-match bypass scan both passed. Local and remote
pre/post manifest checks all passed. The expanded sanitized record is under
[`docs/validation/review-44a4n7/final`](validation/review-44a4n7/final).

### Aggregate prefix diagnostic

Lean 4.36.0's `leanchecker Overlap` interprets `Overlap` as a namespace prefix,
not as a request to replay only the import-only root file. It matches every
`Overlap.*` module. The historical CI failure and the new capped Linux run both
exited 139. Raising the soft stack limit to unlimited, setting
`LEAN_NUM_THREADS=1`, and using the current pinned toolchain did not change that
exit. The new witness-only source produced the same failure after all of its
named modules passed. This is therefore not evidence of a broken theorem or a
regression introduced by the upgrade.

The stronger mode `lake env leanchecker --fresh Overlap` did complete under the
same cap: exit 0 after 528.84 s wall, with 4,041,076 KiB peak RSS. It is retained
as an additional cross-module replay, but it changes the replay mode across the
installed dependency environment and is too expensive for the routine CI gate.
It is also a namespace-prefix request, not a root-only declaration replay.
The raw files are
[`linux-fresh-root/time.log`](../benchmarks/results/linux-fresh-root/time.log)
and [`status.txt`](../benchmarks/results/linux-fresh-root/status.txt). The
optional command was:

```sh
export LEAN_NUM_THREADS=1
ulimit -s 131072
lake env leanchecker --fresh Overlap
```

`Overlap.lean` contains three imports and no authored declarations. CI therefore
enforces an import-only root module and performs a fresh named replay for every
`Overlap/*.lean` file. These named checks cover all authored declarations. The
aggregate-prefix crash remains a separately logged toolchain limitation and is
not used as a required theorem check. The diagnostic summary is
[`root-aggregate-139.txt`](../paper/validation/root-aggregate-139.txt).

### Paired direct and packed scaling

The five sizes use nested nondegenerate slices beginning at zero-based index
3136. Direct source enumerates every finite-sum product. Packed source checks
the equivalent base-`2^128` product. Each size/mode uses one fresh generation,
elaboration, and `leanchecker` process. Generation time is included in the
resource cap. After Direct 1024 reached the cap, Direct 2048 was not attempted;
Packed 2048 still ran.

| Cells | Direct gen | Direct elab | Direct replay | Direct result | Packed gen | Packed elab | Packed replay |
| ---: | ---: | ---: | ---: | --- | ---: | ---: | ---: |
| 128 | 1.520 | 25.300 | 4.540 | pass | 1.390 | 0.930 | 4.330 |
| 256 | 1.560 | 106.490 | 5.000 | pass | 1.460 | 1.110 | 4.390 |
| 512 | 1.890 | 511.660 | 7.310 | pass | 1.610 | 1.530 | 4.450 |
| 1024 | 3.290 | 600.030 | not run | timeout | 2.140 | 2.390 | 5.170 |
| 2048 | not attempted | not attempted | not attempted | not attempted | 4.310 | 4.390 | 4.990 |

All times are seconds. Direct 512 used 11,907,896 KiB peak RSS. The Direct 1024
wall cap is censored data. GNU time reported only the surviving wrapper
(0.20 s user, 0.37 s system, 852,376 KiB RSS), while live samples exceeded
13 GiB; that value is not a descendant peak and is blank in the normalized TSV.
The scope recorded no OOM kill and exit 124 proves the wall timeout. Cgroup
accounting in
[`020-systemd-accounting.json`](../benchmarks/results/linux-canonical-scaling-combined-20261127T070821Z/cgroups/020-systemd-accounting.json)
records 601,093,878,000 ns aggregate CPU. True killed-descendant RSS is
unavailable.

Across the completed scaling processes, summed process wall time was
1,313.180 s: 1,268.590 s on measured Direct paths and 44.590 s on Packed paths.
The 600-second censored endpoint is included. These sums include process
startup and do not imply a general algorithm ratio. The combined normalized
rows are
[`measurements.tsv`](../benchmarks/results/linux-canonical-scaling-combined-20261127T070821Z/measurements.tsv),
with per-size status in
[`pair_summary.tsv`](../benchmarks/results/linux-canonical-scaling-combined-20261127T070821Z/pair_summary.tsv).
The generated PGFPlots source is
[`linux-scaling.tex`](../paper/figures/linux-scaling.tex), and its plot data are
under [`paper/validation`](../paper/validation).

## Machine-readable results and rerun

[`measurements.jsonl`](../benchmarks/results/20261127T033045Z/measurements.jsonl) is the shared row schema for this work and can be consumed by the paper-metrics pass. One JSON object per process measurement has these fields:

| Field | Meaning |
| --- | --- |
| `run_id` | UTC run identifier |
| `phase` | Measurement phase, for example `clean`, `build`, `default_build`, `leanchecker`, `prefix_elaboration`, or `prefix_leanchecker`; additional phases can use the same row schema |
| `unit` | Module target or paired prefix/mode identifier |
| `command` | Exact relative command arguments |
| `wall_seconds` | Parent monotonic wall duration in seconds |
| `wall_source` | Timing boundary description |
| `peak_rss_bytes` | Darwin maximum resident set size in bytes |
| `peak_rss_source` | RSS source and unit |
| `exit_status` | Process result; successful rows are 0 |
| `raw_log` | Relative raw-log filename in the run directory |

To reproduce both the clean build/replays and prefix checks from the repository root, run:

```sh
python3 benchmarks/run.py
python3 benchmarks/prefix_scaling.py
```

The interrupted early attempts are isolated under `benchmarks/results/pilot-*`; their partial rows are not part of the canonical tables above. Existing proof files and Lake dependencies were left untouched.

## Checking one ground product in isolation

The [stand-alone theorem](../scripts/ProductOnly.lean) imports the already compiled height and event literals and proves the full packed equality using `decide +kernel`. The [control](../scripts/ImportOnly.lean) only imports the data. The two files were each run five times in a new Lean process, alternating which ran first. Lake set up the search path once, before measurement. Times include process startup, loading the imports, parsing and elaborating the file, checking declarations, and the product file's axiom query. They do not isolate an internal multiplication primitive. The machine was shared and its filesystem cache was not flushed. In particular, the slowest and fastest measurements both belong in the reported range.

| Process | Trial times, seconds | Median, seconds | Maximum resident size, MiB |
| --- | --- | ---: | ---: |
| Import control | 0.356, 0.270, 0.490, 0.787, 0.827 | 0.490 | 386.1 |
| Full product declaration | 4.303, 4.499, 8.695, 8.142, 8.324 | 8.142 | 954.3 |

All ten invocations returned 0. Each product invocation printed that the theorem depended on no axioms. With a built project, run `lake env python3 scripts/time_product.py` on macOS or Linux. The per-module benchmark above uses Darwin's time utility. [Isolated runner](../scripts/time_product.py) · [Raw observations](../paper/validation/product-only.jsonl)
