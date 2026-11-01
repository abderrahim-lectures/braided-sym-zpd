#!/usr/bin/env bash
# Check the Lean code of the paper against a built Mathlib on LEAN_PATH.
#
# Usage:  ./check.sh            (from this directory, with a built Mathlib on LEAN_PATH)
#
# Each module is elaborated to `.lake/build/lib/lean`, which is put in front of LEAN_PATH so
# that later modules import the freshly built earlier ones. The script fails on the first error.
set -euo pipefail
cd "$(dirname "$0")"

OUT=".lake/build/lib/lean"
mkdir -p "$OUT/ZpdCore" "$OUT/Research/BraidedSymZpd"
export LEAN_PATH="$OUT:${LEAN_PATH:-}"

lean -o "$OUT/ZpdCore/Zpd.olean" ZpdCore/Zpd.lean
lean -o "$OUT/Research/BraidedSymZpd/BraidedSymZpd.olean" Research/BraidedSymZpd/BraidedSymZpd.lean
lean -o "$OUT/Research/BraidedSymZpd/M2F3.olean" Research/BraidedSymZpd/M2F3.lean

echo "all Lean modules check"
