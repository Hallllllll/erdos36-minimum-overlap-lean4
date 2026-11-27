#!/usr/bin/env bash
set -euo pipefail

PAPER_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
REPO_DIR="$(CDPATH= cd -- "$PAPER_DIR/.." && pwd)"
cd "$PAPER_DIR"

if [[ -n "${TEXBIN:-}" ]]; then
  export PATH="$TEXBIN:$PATH"
fi

PYTHON_BIN="${PYTHON:-python3}"
BUILD_DIR="${BUILD_DIR:-$PAPER_DIR/.build}"
BENCH_RUN="${BENCH_RUN:-$REPO_DIR/benchmarks/results/20261127T033045Z}"
if [[ "$BUILD_DIR" != /* ]]; then
  BUILD_DIR="$PAPER_DIR/$BUILD_DIR"
fi

if [[ ! -f main.tex ]]; then
  printf 'error: %s/main.tex is required\n' "$PAPER_DIR" >&2
  exit 1
fi

if ! command -v latexmk >/dev/null 2>&1; then
  printf '%s\n' \
    'error: latexmk is not on PATH.' \
    'Install latexmk with a TeX Live installation or set TEXBIN to its bin directory.' >&2
  exit 1
fi

"$PYTHON_BIN" metrics.py
"$PYTHON_BIN" generate_figures.py --run-dir "$BENCH_RUN"

mkdir -p "$BUILD_DIR"
latexmk \
  -pdf \
  -interaction=nonstopmode \
  -halt-on-error \
  -file-line-error \
  -outdir="$BUILD_DIR" \
  main.tex

install -m 0644 "$BUILD_DIR/main.pdf" "$PAPER_DIR/main.pdf"
printf 'built %s\n' "$PAPER_DIR/main.pdf"
