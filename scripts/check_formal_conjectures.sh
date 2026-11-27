#!/usr/bin/env bash
# Compare the four declaration texts with the pinned upstream problem file.
set -euo pipefail
export LC_ALL=C
root="$(cd "$(dirname "$0")/.." && pwd)"
shim="$root/Overlap/FormalConjecturesDefs.lean"
extract() {
  awk '
    /^(noncomputable )?def (Overlap|MaxOverlap|M|MinOverlapQuotient) \(/ { block = 1; count++ }
    /^$/ { block = 0 }
    block { print }
    END { if (count != 4) exit 1 }
  ' "$1"
}
expected=3df752ddea196a20cf9d86f3258f071d10dea158bdb1852fce460dda8e43273d
actual=$(extract "$shim" | shasum -a 256)
[[ "${actual%% *}" == "$expected" ]] || { echo 'Erdos36 declaration digest mismatch' >&2; exit 1; }
if (( $# > 1 )); then echo 'usage: check_formal_conjectures.sh [upstream-36.lean]' >&2; exit 2; fi
if (( $# == 1 )); then
  upstream=$(shasum -a 256 "$1")
  [[ "${upstream%% *}" == ed010f8ba25a2efec1fa996bc7d69c0fd67cae8789e2215d419ed282b0ac4c81 ]] ||
    { echo 'unexpected upstream source revision' >&2; exit 1; }
  diff -u <(extract "$1") <(extract "$shim")
fi
echo "Four Erdos36 definitions match the pinned declaration digest: $expected"
