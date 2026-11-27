#!/usr/bin/env python3
"""Paired direct-convolution vs packed-kernel checks on nested prefixes."""
from __future__ import annotations

import datetime as dt
import json
import os
import pathlib
import re
import subprocess
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path(os.environ.get("BENCH_OUT", ROOT / "benchmarks" / "results"))
RUN = sorted((p for p in OUT.iterdir() if p.is_dir() and not p.name.startswith("pilot-")))[-1]
SRC = RUN / "prefix_sources"
SRC.mkdir(exist_ok=True)
STAGE = ROOT / "benchmarks" / ".generated"
MODDIR = STAGE / "Benchmarks"
MODDIR.mkdir(parents=True, exist_ok=True)
ENV = os.environ.copy()
ENV.pop("GIT_CONFIG_COUNT", None)
data = json.loads((ROOT / "construction.json").read_text())
xs = data["numerators"][len(data["numerators"]) // 3:]
d = data["denominator"]
rows = []


def tree(vals: list[str]) -> str:
    if len(vals) == 1:
        return f"Overlap.Tree.leaf ({vals[0]})"
    mid = len(vals) // 2
    return f"Overlap.Tree.node ({tree(vals[:mid])}) ({tree(vals[mid:])})"


def run(phase: str, name: str, command: list[str]) -> None:
    start = time.perf_counter()
    proc = subprocess.run(["/usr/bin/time", "-l", *command], cwd=ROOT, env=ENV,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    elapsed = time.perf_counter() - start
    stderr, stdout = proc.stderr, proc.stdout
    for secret in (str(ROOT), str(pathlib.Path.home())):
        stderr, stdout = stderr.replace(secret, "<REPO>"), stdout.replace(secret, "<REPO>")
    log = RUN / f"prefix-{phase}-{name}.log"
    log.write_text(f"$ {' '.join(command)}\nexit_status={proc.returncode}\n--- stdout ---\n{stdout}\n--- stderr and Darwin /usr/bin/time -l ---\n{stderr}")
    rss = re.search(r"([0-9]+)\s+maximum resident set size", stderr)
    row = {"run_id": RUN.name, "phase": f"prefix_{phase}", "unit": name, "command": " ".join(command),
           "wall_seconds": round(elapsed, 6), "wall_source": "parent monotonic clock, includes /usr/bin/time wrapper",
           "peak_rss_bytes": int(rss.group(1)) if rss else None,
           "peak_rss_source": "Darwin /usr/bin/time -l maximum resident set size; bytes",
           "exit_status": proc.returncode, "raw_log": log.name}
    rows.append(row)
    with (RUN / "measurements.jsonl").open("a") as f:
        f.write(json.dumps(row, sort_keys=True) + "\n")
    print(json.dumps(row), flush=True)
    if proc.returncode:
        raise SystemExit(proc.returncode)


for n in (16, 32, 64):
    a = xs[:n]
    # Events are coefficients of A(z) * (d - reverse(A))(z), indexed
    # by signed lag -n+1,...,n-1, matching scripts/generate.py.
    ev = [sum(a[i] * (d - a[i-k]) for i in range(n) if 0 <= i-k < n)
          for k in range(-n+1, n)]
    a_tree, e_tree = tree([str(v) for v in a]), tree([str(v) for v in ev])
    direct_leaves = []
    for k in range(-n+1, n):
        terms = [f"({a[i]} * ({d} - {a[i-k]}))" for i in range(n) if 0 <= i-k < n]
        direct_leaves.append("(" + " + ".join(terms) + ")")
    direct_tree = tree(direct_leaves)
    common = f'''import Overlap.Tree
namespace Benchmarks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input{n} : Overlap.Tree := {a_tree}
def expected{n} : Overlap.Tree := {e_tree}
'''
    direct = common + f'''def direct{n} : Overlap.Tree := {direct_tree}
theorem direct_check{n} : direct{n}.items = expected{n}.items := by decide +kernel
end Benchmarks
'''
    packed = common + f'''theorem packed_check{n} :
  input{n}.pack (2^128) * input{n}.other (2^128) {d} = expected{n}.pack (2^128) := by decide +kernel
end Benchmarks
'''
    for mode, source in (("direct", direct), ("packed", packed)):
        name = f"{mode}{n}"
        src = SRC / f"{name}.lean"
        src.write_text(source)
        staged = MODDIR / f"{name}.lean"
        staged.write_text(source)
        olean = ROOT / ".lake" / "build" / "lib" / "lean" / "Benchmarks" / f"{name}.olean"
        olean.parent.mkdir(parents=True, exist_ok=True)
        run("elaboration", name, ["lake", "env", "lean", "--root", "benchmarks/.generated", "-o", str(olean.relative_to(ROOT)), str(staged.relative_to(ROOT))])
        run("leanchecker", name, ["lake", "env", "leanchecker", f"Benchmarks.{name}"])
for f in MODDIR.glob("*.lean"):
    f.unlink()
MODDIR.rmdir()
STAGE.rmdir()
