"""Create a deterministic reviewer archive without a checkout or toolchain cache."""
import argparse
from hashlib import sha256
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

ROOT = Path(__file__).resolve().parents[1]
FILES = [
    "LICENSE", "Overlap.lean", "lean-toolchain", "lake-manifest.json", "lakefile.toml",
    "construction.json", "certificate.json", "small_cases.json", "sources/frontier_parent.txt",
    "verify.py", "audit_verify.py", "scripts/generate.py", "scripts/check_digit_guards.py",
    "scripts/paper_axioms.lean", "paper/validation/axioms.txt", "paper/validation/digit-guards.txt",
    "scripts/ProductOnly.lean", "scripts/ImportOnly.lean", "scripts/time_product.py",
    "scripts/PearlExample.lean", "paper/validation/toy-example.txt",
    "paper/validation/product-only.jsonl",
    "paper/main.tex", "paper/references.bib", "paper/related.tex", "paper/REPRODUCE.md",
    "paper/generated/witness-profile.pdf", "scripts/package_supplement.py",
    "paper/metrics.py", "paper/generated/metrics.json", "paper/generated/metrics.tex",
]
README = """# Minimum-overlap proof and measurements

Build with the pinned Lean and Mathlib versions. Run these commands in this directory.

    lake exe cache get
    lake build
    for m in Tree Data Numerical Algebra AffineBridge Profile Spec Main; do
      lake env leanchecker "Overlap.$m" || exit 1
    done
    python3 verify.py
    python3 audit_verify.py
    python3 scripts/check_digit_guards.py
    lake env lean scripts/paper_axioms.lean
    python3 paper/metrics.py --check

The principal declarations are in Overlap/Main.lean. The finite product is checked
in Overlap/Numerical.lean and decoded in Overlap/Algebra.lean. WhiteBridge is an
explicit premise in the discrete-limit result. The supplied measurements and
their commands are described in docs/benchmarks.md. Run bash paper/build.sh
with TeX Live and latexmk to reproduce the manuscript from its included sources.
See paper/REPRODUCE.md for details.
"""


def members():
    result = {name: (ROOT / name).read_bytes() for name in FILES}
    inputs = list((ROOT / "Overlap").glob("*.lean"))
    inputs += [ROOT / "docs/benchmarks.md"]
    for folder, suffixes in (
        ("benchmarks", {".py", ".sh", ".md", ".json", ".jsonl", ".log", ".tsv", ".csv", ".lean", ".txt"}),
        ("paper", {".py", ".tex", ".sh", ".json", ".tsv", ".csv"}),
    ):
        for path in (ROOT / folder).rglob("*"):
            if path.suffix.lower() not in suffixes or not path.is_file():
                continue
            if any(part.startswith(".") or part in {"build", "__pycache__"} for part in path.relative_to(ROOT).parts):
                continue
            inputs.append(path)
    for path in inputs:
        result[path.relative_to(ROOT).as_posix()] = path.read_bytes()
    result["README.md"] = README.encode()
    manifest = [f"{sha256(data).hexdigest()}  {name}" for name, data in sorted(result.items())]
    result["SHA256SUMS"] = ("\n".join(manifest) + "\n").encode()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    with ZipFile(args.output, "w") as archive:
        for name, data in sorted(members().items()):
            info = ZipInfo(name, (1980, 1, 1, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data, compress_type=ZIP_DEFLATED)
    print(f"{sha256(args.output.read_bytes()).hexdigest()}  {args.output.name}")


if __name__ == "__main__":
    main()
