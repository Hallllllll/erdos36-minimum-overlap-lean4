# Full import-closure replay

The pinned Lean 4.36.0 checker replayed the constants of the imported
environment for the exact root module into an empty kernel environment.
This is the `--fresh` mode of the stock executable. Its result is
complementary to the separate named-module replays. On the same Linux
host as the regular-paper measurements, the shell used one Lean worker,
a 128 MiB stack limit, a 16 GiB memory cgroup with swap disabled, and a
600-second wall limit. The process exited zero and emitted no output.

```bash
export LEAN_NUM_THREADS=1
ulimit -s 131072
/usr/bin/time -v timeout -k 10 600 lake env leanchecker --fresh Overlap
```

The command, elapsed time, CPU times and maximum resident set size are in
`time.log`. The exit code is also recorded in `status.txt`.
