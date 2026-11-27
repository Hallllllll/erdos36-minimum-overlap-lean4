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
