#!/usr/bin/env python3
"""Clean, serialized Lean build and fresh-process leanchecker replay."""
from __future__ import annotations

import datetime as dt
import json
import os
import pathlib
import platform
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path(os.environ.get("BENCH_OUT", ROOT / "benchmarks" / "results"))
OUT.mkdir(parents=True, exist_ok=True)
STAMP = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
RUN = OUT / STAMP
RUN.mkdir()
ENV = os.environ.copy()
ENV.pop("GIT_CONFIG_COUNT", None)
CORE_MODULES = ["Tree", "Data", "Numerical", "Algebra", "AffineBridge", "Profile", "Spec", "Main"]
MODULES = [*CORE_MODULES, "Bench"]
ROWS: list[dict] = []


def record(phase: str, unit: str, cmd: list[str]) -> None:
    start = time.perf_counter()
    proc = subprocess.run(["/usr/bin/time", "-l", *cmd], cwd=ROOT, env=ENV,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    elapsed = time.perf_counter() - start
    raw = proc.stderr
    stdout = proc.stdout
    for private in (str(ROOT), str(pathlib.Path.home())):
        raw = raw.replace(private, "<REPO>")
        stdout = stdout.replace(private, "<REPO>")
    log = RUN / f"{len(ROWS)+1:02d}-{phase}-{unit}.log"
    log.write_text(f"$ {' '.join(cmd)}\nexit_status={proc.returncode}\n\n--- stdout ---\n{stdout}\n--- stderr and Darwin /usr/bin/time -l ---\n{raw}")
    match = re.search(r"([0-9]+)\s+maximum resident set size", raw)
    row = {
        "run_id": STAMP, "phase": phase, "unit": unit,
        "command": " ".join(cmd), "wall_seconds": round(elapsed, 6),
        "wall_source": "parent monotonic clock, includes /usr/bin/time wrapper",
        "peak_rss_bytes": int(match.group(1)) if match else None,
        "peak_rss_source": "Darwin /usr/bin/time -l maximum resident set size; bytes",
        "exit_status": proc.returncode, "raw_log": log.name,
    }
    ROWS.append(row)
    with (RUN / "measurements.jsonl").open("a") as stream:
        stream.write(json.dumps(row, sort_keys=True) + "\n")
    print(json.dumps(row), flush=True)
    if proc.returncode:
        raise SystemExit(proc.returncode)


ENVIRONMENT = {
    "run_id": STAMP, "kind": "environment", "os": platform.platform(),
    "machine": platform.machine(), "python": platform.python_version(),
    "cpu": subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True, text=True).stdout.strip(),
    "logical_cpus": subprocess.run(["sysctl", "-n", "hw.ncpu"], capture_output=True, text=True).stdout.strip(),
    "memory_bytes": subprocess.run(["sysctl", "-n", "hw.memsize"], capture_output=True, text=True).stdout.strip(),
    "macos_version": subprocess.run(["sw_vers", "-productVersion"], capture_output=True, text=True).stdout.strip(),
    "macos_build": subprocess.run(["sw_vers", "-buildVersion"], capture_output=True, text=True).stdout.strip(),
    "lean_version": subprocess.run(["lean", "--version"], cwd=ROOT, env=ENV, capture_output=True, text=True).stdout.strip(),
    "lake_version": subprocess.run(["lake", "--version"], cwd=ROOT, env=ENV, capture_output=True, text=True).stdout.strip(),
    "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
    "modules": MODULES, "notes": "GIT_CONFIG_COUNT removed from child environment",
}
(RUN / "environment.json").write_text(json.dumps(ENVIRONMENT, indent=2, sort_keys=True) + "\n")
print(json.dumps(ENVIRONMENT), flush=True)
record("clean", "project", ["lake", "clean", "overlap"])
for module in MODULES:
    record("build", module, ["lake", "build", f"Overlap.{module}"])
record("clean", "project-before-default-build", ["lake", "clean", "overlap"])
record("default_build", "Overlap", ["lake", "build"])
record("build_after_default", "Bench", ["lake", "build", "Overlap.Bench"])
for module in CORE_MODULES:
    record("leanchecker", module, ["lake", "env", "leanchecker", f"Overlap.{module}"])
record("leanchecker", "Bench", ["lake", "env", "leanchecker", "Overlap.Bench"])
print(f"results_dir={RUN}", flush=True)
