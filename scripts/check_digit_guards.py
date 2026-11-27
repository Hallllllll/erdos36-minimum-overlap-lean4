"""Falsification tests for the exact checks used by the packed certificate."""
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PRELUDE = """import Overlap.Numerical
open Overlap
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000

-- Alter just the least significant leaf; keep the rest of the tree shared.
def bump : Tree → Tree
  | .leaf x => .leaf (x+1)
  | .node l r => .node (bump l) r

def padded := Tree.node events (Tree.leaf 0)

def uncarried := Tree.node (Tree.leaf B) (Tree.leaf 0)
def carried := Tree.node (Tree.leaf 0) (Tree.leaf 1)
"""
CASES = [
    ("original", "heights.pack B * heights.other B D = events.pack B", True),
    ("single coefficient changed", "heights.pack B * heights.other B D = (bump events).pack B", False),
    ("zero padding preserves value", "padded.pack B = events.pack B", True),
    ("zero padding violates length", "padded.size = 2*N-1", False),
    ("carry preserves value and length", "uncarried.size = carried.size ∧ uncarried.pack B = carried.pack B", True),
    ("uncarried digit violates range", "uncarried.high < B", False),
]


def main():
    with tempfile.TemporaryDirectory() as temp:
        source = Path(temp) / "Guards.lean"
        for label, statement, expected in CASES:
            source.write_text(PRELUDE + f"example : {statement} := by decide +kernel\n")
            result = subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=ROOT,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
            if expected:
                passed = result.returncode == 0
            else:
                passed = result.returncode != 0 and re.search(
                    r"decide.*(false|failed)|reduc(?:e[ds]?|ing).*false",
                    result.stdout, flags=re.IGNORECASE | re.DOTALL,
                )
            if not passed:
                raise SystemExit(f"{label}: unexpected checker outcome\n{result.stdout}")
            outcome = "accepted" if expected else "rejected"
            print(f"{label}: {outcome} (Lean exit {result.returncode})")


if __name__ == "__main__":
    main()
