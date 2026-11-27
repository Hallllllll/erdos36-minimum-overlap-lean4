"""Run with lake env python3 scripts/time_product.py, after lake build."""
import json
import os
from pathlib import Path
import platform
import shutil
import sys
import tempfile
import time

root = Path(__file__).resolve().parents[1]
os.chdir(root)
lean = shutil.which("lean")
if not lean or "LEAN_PATH" not in os.environ:
    sys.exit("Use lake env python3 scripts/time_product.py after building the proof.")
if sys.platform not in {"darwin", "linux"}:
    sys.exit("RSS conversion is defined for macOS and Linux.")
print(json.dumps({"platform": platform.system(), "machine": platform.machine(),
                  "toolchain": Path("lean-toolchain").read_text().strip(),
                  "timing": "fresh Lean process; imported oleans already built; wall from posix_spawn to wait4",
                  "rss": "ru_maxrss bytes on Darwin, KiB multiplied by 1024 on Linux"}), flush=True)
for trial in range(1, 6):
    order = ["ImportOnly", "ProductOnly"] if trial % 2 else ["ProductOnly", "ImportOnly"]
    for unit in order:
        source = "scripts/" + unit + ".lean"
        with tempfile.TemporaryFile() as output:
            actions = [(os.POSIX_SPAWN_DUP2, output.fileno(), i) for i in (1, 2)]
            start = time.perf_counter_ns()
            pid = os.posix_spawn(lean, ["lean", source], os.environ, file_actions=actions)
            _, status, usage = os.wait4(pid, 0)
            elapsed = time.perf_counter_ns() - start
            output.seek(0)
            stdout = output.read().decode().strip()
        row = {"trial": trial, "unit": unit, "source": source,
               "wall_ns": elapsed, "user_s": usage.ru_utime, "system_s": usage.ru_stime,
               "rss_bytes": usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024),
               "exit": os.waitstatus_to_exitcode(status), "output": stdout}
        print(json.dumps(row), flush=True)
        if row["exit"] or (unit == "ProductOnly" and stdout !=
                            "'Overlap.Benchmark.fullProduct' does not depend on any axioms"):
            sys.exit("Unexpected Lean result")
