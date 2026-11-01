#!/usr/bin/env bash
# Check the Lean code of the paper against a built Mathlib on LEAN_PATH.
#
# Usage:  ./check.sh            (from this directory, with a built Mathlib on LEAN_PATH)
#
# Each module is elaborated to `.lake/build/lib/lean`, which is put in front of LEAN_PATH so
# that later modules import the freshly built earlier ones. The script fails on the first error.
# The last two modules are the paper's two previously missing pieces: `ZpdCore.Triangular`
# (`cor:triangular`) and `Research.BraidedSymZpd.M2F3Bridge` (the finrank bridge from the F_3 numbers).
set -euo pipefail
cd "$(dirname "$0")"

OUT=".lake/build/lib/lean"
mkdir -p "$OUT/ZpdCore" "$OUT/Research/BraidedSymZpd"
export LEAN_PATH="$OUT:${LEAN_PATH:-}"

lean -o "$OUT/ZpdCore/Zpd.olean" ZpdCore/Zpd.lean
lean -o "$OUT/ZpdCore/Triangular.olean" ZpdCore/Triangular.lean
lean -o "$OUT/Research/BraidedSymZpd/BraidedSymZpd.olean" Research/BraidedSymZpd/BraidedSymZpd.lean
lean -o "$OUT/Research/BraidedSymZpd/ZJpd.olean" Research/BraidedSymZpd/ZJpd.lean
lean -o "$OUT/Research/BraidedSymZpd/M2F3.olean" Research/BraidedSymZpd/M2F3.lean
lean -o "$OUT/Research/BraidedSymZpd/M2F3Bridge.olean" Research/BraidedSymZpd/M2F3Bridge.lean

echo "all Lean modules check"
