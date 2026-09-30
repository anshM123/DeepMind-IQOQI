#!/usr/bin/env bash
# Reproduce the Lean check of the A051903 solutions.
# Usage: bash check.sh /path/to/formal-conjectures
#   The formal-conjectures checkout should be at commit ab0addc45f699bdd0b7cc58efa5140a72f101a9e (tested;
#   FormalConjectures/OEIS/51903.lean is byte-identical at e04cc601840dd7a37f89b821a67f3a9e3c38d9c3).
#   Run `lake exe cache get` in the checkout first. Lean v4.33.1 (the checkout's lean-toolchain).
set -euo pipefail
FC="$(cd "$1" && pwd)"
HERE="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$FC/DMSolutions/OEIS_A051903"
cp "$HERE"/DMSolutions/OEIS_A051903/*.lean "$FC/DMSolutions/OEIS_A051903/"
cd "$FC"
O=.lake/build/lib/lean
mkdir -p "$O/DMSolutions/OEIS_A051903" "$O/FormalConjectures/OEIS"
echo "== formal-conjectures commit: $(git rev-parse HEAD)"
echo "== statement file sha256: $(sha256sum FormalConjectures/OEIS/51903.lean | cut -c1-64)"
# The repository's own leanOptions for the FormalConjectures library (lakefile.toml).
PKG="-Dpp.unicode.fun=true -DautoImplicit=false -DrelaxedAutoImplicit=false"
PKG="$PKG -Dweak.linter.style.copyright.formalConjectures=true -Dweak.linter.style.namespace=true"
PKG="$PKG -Dweak.linter.style.stubs=true -Dweak.linter.style.openClassical=true"
FCO="-Dwarn.sorry=false -Dweak.linter.style.ams_attribute=true -Dweak.linter.style.category_attribute=true"
FCO="$FCO -Dweak.linter.style.category_answer=true -Dweak.linter.style.conditional_formal_proof=true"
FCO="$FCO -Dweak.linter.style.moduleDocstring=true -Dweak.linter.style.latex_docstring=true"
FCO="$FCO -Dweak.linter.style.imports=true -Dweak.google.answer=always_true"
echo "== 1. Core.lean (Mathlib only)"
lake env lean -o "$O/DMSolutions/OEIS_A051903/Core.olean" DMSolutions/OEIS_A051903/Core.lean
echo "== 2. FormalConjectures/OEIS/51903.lean (unmodified repository statement, repository options)"
lake env lean $PKG $FCO -o "$O/FormalConjectures/OEIS/51903.olean" FormalConjectures/OEIS/51903.lean
echo "== 3. Solution.lean (imports the repository statement)"
lake env lean -o "$O/DMSolutions/OEIS_A051903/Solution.olean" DMSolutions/OEIS_A051903/Solution.lean
echo "== 4. CheckAnswer.lean (answer(False) = False, answer(True) = True; statements printed)"
lake env lean DMSolutions/OEIS_A051903/CheckAnswer.lean
echo "== 5. forbidden keywords (sorry/admit/native_decide/axiom):"
grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' DMSolutions/OEIS_A051903/*.lean || echo "none"
echo "== done"
