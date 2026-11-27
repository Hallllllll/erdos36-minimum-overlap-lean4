# Linux benchmark runner

Run from a remote `tmux` session after fetching Lean and the Mathlib cache:

```sh
bash benchmarks/linux/run.sh
```

The runner holds `/run/lock/overlap-heavy.lock` for its entire lifetime, so
another checkout cannot begin a competing Lake build. Each child process is
launched in a transient systemd cgroup with a 16 GiB memory maximum, swap
disabled, and a 600-second wall-clock timeout. `/usr/bin/time -v` records the
full process statistics. Raw stdout, stderr, timeout messages, cgroup OOM
counters, and timing reports are retained in a new
`benchmarks/results/linux-<UTC>/` directory.

Use `--kernel-only` or `--scaling-only` to select a suite. The default scaling
ladder is 128, 256, 512, 1024, and 2048 cells. Each size uses a contiguous,
nondegenerate slice beginning at zero-based index 3136. Direct and packed
modules are generated separately by a Lean program using exact `Nat`
arithmetic. They are then elaborated and replayed in separate fresh processes.

Failures in `measurements.tsv` are classified as `timeout`, `oom`,
`recursion`, `lean_error`, or `tool_error`. A direct-side cap is recorded as a
benchmark result and does not prevent the paired packed path from running.
