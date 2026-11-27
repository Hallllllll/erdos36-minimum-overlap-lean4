#!/usr/bin/env bash
set -euo pipefail

# Build one reproducible reviewer archive at the explicit output path.
if [[ $# -ne 1 ]]; then
  printf 'usage: bash scripts/package_supplement.sh OUTPUT.zip\n' >&2
  exit 2
fi

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
OUTPUT="$1"
case "$OUTPUT" in
  /*) ;;
  *) OUTPUT="$ROOT/$OUTPUT" ;;
esac
for tool in zip unzip shasum find sort touch; do
  command -v "$tool" >/dev/null 2>&1 || {
    printf 'missing required command: %s\n' "$tool" >&2
    exit 69
  }
done

TMP="$(mktemp -d "${TMPDIR:-/tmp}/overlap-supplement.XXXXXX")"
OUTPUT_PARENT="$(dirname "$OUTPUT")"
mkdir -p "$OUTPUT_PARENT"
OUTPUT_TMP_DIR="$(mktemp -d "$OUTPUT_PARENT/.supplement-package.XXXXXX")"
OUTPUT_TMP="$OUTPUT_TMP_DIR/$(basename "$OUTPUT")"
trap 'rm -rf "$TMP" "$OUTPUT_TMP_DIR"' EXIT
STAGE="$TMP/tree"
mkdir -p "$STAGE"

cd "$ROOT"
export TZ=UTC
export LC_ALL=C

# Core source, exact evidence, validation records, manuscript source, and
# reproducibility tooling. Dynamic source and generated figure inputs are added
# below so new proof modules and paper assets cannot silently fall out.
core_files=(
  LICENSE Overlap.lean lean-toolchain lake-manifest.json lakefile.toml
  construction.json certificate.json small_cases.json sources/frontier_parent.txt
  verify.py audit_verify.py README.md PROOF.md CITATION.cff
  scripts/generate.py scripts/check_digit_guards.py scripts/paper_axioms.lean
  scripts/ProductOnly.lean scripts/ImportOnly.lean scripts/PearlExample.lean
  scripts/time_product.py scripts/package_supplement.sh scripts/check_formal_conjectures.sh
  docs/benchmarks.md
  paper/main.tex paper/main.pdf paper/references.bib paper/related.tex paper/REPRODUCE.md
  paper/metrics.py paper/generate_figures.py paper/witness_figure.py paper/build.sh
  benchmarks/run.py benchmarks/prefix_scaling.py
  benchmarks/linux/README.md benchmarks/linux/Generator.lean
  benchmarks/linux/generate_pair.sh benchmarks/linux/render_plot.sh
  benchmarks/linux/run.sh
)
for path in "${core_files[@]}"; do
  [[ -f "$path" ]] || { printf 'required archive input missing: %s\n' "$path" >&2; exit 1; }
  mkdir -p "$STAGE/$(dirname "$path")"
  cp "$path" "$STAGE/$path"
done

# Include every top-level Lean module, including untracked modules. Keep the
# explicit parity check so additions cannot be silently omitted from release.
while IFS= read -r -d '' path; do
  rel="${path#./}"
  mkdir -p "$STAGE/Overlap"
  cp "$path" "$STAGE/$rel"
done < <(find Overlap -maxdepth 1 -type f -name '*.lean' -print0)
diff <(find Overlap -maxdepth 1 -type f -name '*.lean' -print | LC_ALL=C sort) \
  <(find "$STAGE/Overlap" -maxdepth 1 -type f -name '*.lean' -print | \
    sed "s#^$STAGE/##" | LC_ALL=C sort)

# Archive complete current paper assets: source figures, generated TeX/PDF,
# and machine-readable validation records. Ignore hidden/build scratch files.
for folder in paper/figures paper/generated paper/validation docs/validation/review-44a4n7; do
  while IFS= read -r -d '' path; do
    rel="${path#./}"
    [[ "$rel" == */.* || "$rel" == */.build/* || "$rel" == */__pycache__/* ]] && continue
    [[ "$(basename "$rel")" == *.tmp || "$(basename "$rel")" == *~ ]] && continue
    mkdir -p "$STAGE/$(dirname "$rel")"
    cp "$path" "$STAGE/$rel"
  done < <(find "$folder" -type f -print0)
done

# Retain the canonical macOS run and only named release Linux runs, including
# their raw logs, time reports, cgroup counters, and environment metadata.
# Exclude pilots, failed diagnostics, smoke checks, and regenerable dumps.
while IFS= read -r -d '' path; do
  rel="${path#./}"
  case "$rel" in
    benchmarks/results/20261127T033045Z/*|\
    benchmarks/results/linux-canonical-*/*|\
    benchmarks/results/linux-authoritative-final-*/*|\
    benchmarks/results/linux-confirmed-module-gate/*|\
    benchmarks/results/linux-fresh-root/*|\
    benchmarks/results/linux-matched-v100-045d628/*|\
    benchmarks/results/root-stack-20261127T071844Z/*) ;;
    *) continue ;;
  esac
  [[ "$rel" == */prefix_sources/* ]] && continue
  [[ "$rel" == */generated/*.lean ]] && continue
  case "${rel##*.}" in
    olean|ilean|ilean.hash|olean.hash|c|o|a) continue ;;
  esac
  [[ -f "$path" ]] || continue
  mkdir -p "$STAGE/$(dirname "$rel")"
  cp "$path" "$STAGE/$rel"
done < <(find benchmarks/results -type f -print0)

cat > "$STAGE/SUPPLEMENT-README.md" <<'README'
# Minimum-overlap reviewer supplement

This archive contains the Lean source and exact witness data, validation
outputs, manuscript source, benchmark commands, and retained measurement
records. The recorded timings are empirical observations, not proof premises.
The Lean development proves `Overlap.whiteBridge : WhiteBridge`; the paper's
main theorem does not take WhiteBridge as an assumption.

## Reproduction

From the archive root, install the pinned Lean toolchain and Mathlib cache,
then run `lake build`, the verifier and guard commands documented in
`paper/REPRODUCE.md`, and `python3 paper/metrics.py --check`. Build the paper
with `bash paper/build.sh` and TeX Live with `acmart`, TikZ, `pgfplots`,
`pbalance`, BibTeX, and `latexmk`. Reproduce the benchmark suites with `python3 benchmarks/run.py`,
`python3 benchmarks/prefix_scaling.py`, or the Linux runner documented in
`benchmarks/linux/README.md`.

The archive retains canonical raw logs, named Linux release runs, and the
root-stack clean-closure diagnostic.
Pilots, failed diagnostics, smoke runs, and generated paired-prefix Lean
source dumps are omitted; the sources can be regenerated by the included
tooling. All top-level Lean modules are included. `SHA256SUMS` contains a
SHA-256 digest for each archived file other than itself.
README

(cd "$STAGE" && find . -type f ! -name SHA256SUMS -print | LC_ALL=C sort |
  while IFS= read -r file; do
    shasum -a 256 "${file#./}"
  done > SHA256SUMS)

# Normalize timestamps and rely on sorted input order plus ZIP's no-extra-fields
# mode so identical inputs produce byte-identical archives.
find "$STAGE" -type f -exec touch -t 200001010000 {} +
(cd "$STAGE" && find . -type f -print | LC_ALL=C sort |
  while IFS= read -r file; do printf '%s\n' "${file#./}"; done |
  zip -X -q "$OUTPUT_TMP" -@)
unzip -tqq "$OUTPUT_TMP"
mkdir "$TMP/verify"
unzip -q "$OUTPUT_TMP" -d "$TMP/verify"
(cd "$TMP/verify" && shasum -a 256 -c SHA256SUMS >/dev/null)
mv -f "$OUTPUT_TMP" "$OUTPUT"
shasum -a 256 "$OUTPUT"
