#!/usr/bin/env bash
set -euo pipefail

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"
cd "$ROOT"

if [[ $# -ne 4 ]]; then
  printf 'usage: %s direct|packed CELLS OFFSET OUTPUT.lean\n' "$0" >&2
  exit 2
fi

MODE="$1"
CELLS="$2"
OFFSET="$3"
OUTPUT="$4"

case "$MODE" in
  direct|packed) ;;
  *)
    printf 'invalid mode: %s\n' "$MODE" >&2
    exit 2
    ;;
esac

if [[ ! "$CELLS" =~ ^[0-9]+$ || ! "$OFFSET" =~ ^[0-9]+$ ]]; then
  printf 'cells and offset must be non-negative integers\n' >&2
  exit 2
fi

DENOMINATOR="$(jq -er '.denominator' construction.json)"
AVAILABLE="$(jq -er '.numerators | length' construction.json)"
if (( CELLS < 2 || OFFSET + CELLS > AVAILABLE )); then
  printf 'invalid slice: offset=%s cells=%s available=%s\n' \
    "$OFFSET" "$CELLS" "$AVAILABLE" >&2
  exit 2
fi

OUTPUT_DIR="$(dirname -- "$OUTPUT")"
mkdir -p "$OUTPUT_DIR"
HEIGHTS_FILE="$(mktemp "$OUTPUT_DIR/.heights.XXXXXX")"
trap 'rm -f "$HEIGHTS_FILE"' EXIT

jq -er \
  --argjson offset "$OFFSET" \
  --argjson cells "$CELLS" \
  '.numerators[$offset:($offset + $cells)][]' \
  construction.json > "$HEIGHTS_FILE"

LAKE_BIN="${LAKE_BIN:-lake}"
printf 'generator: benchmarks/linux/Generator.lean mode=%s cells=%s offset=%s\n' \
  "$MODE" "$CELLS" "$OFFSET"
"$LAKE_BIN" env lean --run benchmarks/linux/Generator.lean \
  "$MODE" "$CELLS" "$OFFSET" "$DENOMINATOR" "$HEIGHTS_FILE" "$OUTPUT"
