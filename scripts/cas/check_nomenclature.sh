#!/bin/sh
# Nomenclature gate for the adjacent-quadratic shift paper.
# Usage: sh scripts/check_nomenclature.sh   (run from the repository root)
# Prints "nomenclature OK" and exits 0 iff all checks pass; otherwise prints
# a diagnostic to stderr and exits 1.
set -u

PAPER_DIR="paper"

fail() {
  echo "nomenclature FAIL: $1" >&2
  exit 1
}

# 0. Required skeleton files exist.
for f in "$PAPER_DIR/main.tex" "$PAPER_DIR/00-intro.tex" "$PAPER_DIR/01-definitions.tex"; do
  [ -f "$f" ] || fail "missing required file $f"
done

TEX_FILES="$PAPER_DIR"/*.tex

# 1. Formal lowercase descriptive name is used.
grep -Fq 'adjacent-quadratic shift' $TEX_FILES \
  || fail "formal name 'adjacent-quadratic shift' not found"

# 2. No capitalized formal-name variants (the name stays lowercase).
if grep -Eq 'Adjacent-quadratic|Adjacent-Quadratic|ADJACENT-QUADRATIC' $TEX_FILES; then
  fail "capitalized formal-name variant found (use lowercase 'adjacent-quadratic shift')"
fi

# 3. Historical-name discipline: at most one capital-P 'Phantom' occurrence,
#    always with homotopy disambiguation, never in title/abstract/definitions.
PHANTOM_COUNT=$(grep -o 'Phantom' $TEX_FILES | wc -l | tr -d ' ')
[ "$PHANTOM_COUNT" -le 1 ] \
  || fail "'Phantom' appears $PHANTOM_COUNT times (at most once allowed)"
if [ "$PHANTOM_COUNT" -eq 1 ]; then
  grep -Eiq 'stable homotopy' $TEX_FILES \
    || fail "'Phantom' present without homotopy disambiguation ('stable homotopy')"
fi
if grep -q 'Phantom' "$PAPER_DIR/01-definitions.tex"; then
  fail "'Phantom' must never appear in the definitions file"
fi
if grep -q '^\\title.*Phantom' "$PAPER_DIR/main.tex"; then
  fail "'Phantom' must never appear in the title"
fi
if awk '/\\begin\{abstract\}/{inabs=1} inabs && /Phantom/{found=1} /\\end\{abstract\}/{inabs=0} END{exit !found}' \
    "$PAPER_DIR/main.tex"; then
  fail "'Phantom' must never appear in the abstract"
fi

# 4. Discrete map is a first-order update, never exp(lambda D_N);
#    the order-lambda^2 divergence must be stated.
if grep -Eq 'P_\{?\\lambda[^%]*=[^%]*\\exp' $TEX_FILES; then
  fail "discrete map equated with exp(lambda D_N)"
fi
if grep -Eq 'is +\\?exp\(\\?lambda *D' $TEX_FILES; then
  fail "discrete map described as exp(lambda D_N)"
fi
grep -Fq 'ne \exp' $TEX_FILES \
  || fail "missing 'P != exp(lambda D)' divergence statement"
if ! grep -Fq '\lambda^2' $TEX_FILES && ! grep -q 'λ²' $TEX_FILES; then
  fail "missing order-lambda^2 divergence term"
fi
grep -Eiq 'diverge' $TEX_FILES \
  || fail "missing divergence statement"

# 5. Forbidden claims must not appear.
for s in 'new integrable lattice' \
         'new class of automorphisms' \
         'new Hadamard' \
         'uniform quadratic syzygy' \
         'principal-ideal' \
         'binomial iterate' \
         'quadratic shear' \
         'coefficient cascade'; do
  if grep -Fq "$s" $TEX_FILES; then
    fail "forbidden claim present: '$s'"
  fi
done
if grep -Eiq 'Jonqui.*cascade' $TEX_FILES; then
  fail "forbidden claim present: 'Jonquieres cascade'"
fi

# 6. Honesty qualifiers: N=6 computation is evidence, never proof;
#    enumeration over tested fields never implies all-F_q.
if grep -Eiq 'N *= *6|through \$?N' $TEX_FILES; then
  grep -Fq 'evidence, not proof' $TEX_FILES \
    || fail "N=6 computation present without 'evidence, not proof' qualifier"
fi
if grep -Eq 'F_q|finite field|enumeration|Enumeration' $TEX_FILES; then
  grep -Eq 'tested fields|does not imply' $TEX_FILES \
    || fail "finite-field/enumeration present without tested-fields qualifier"
fi

# 7. Verbatim novelty box (until the literature protocol completes).
grep -Fq 'No prior anticipation is currently known, but nonexistence has not been established (MathSciNet/zbMATH/citation-chaining pending).' $TEX_FILES \
  || fail "verbatim novelty box missing"

# 8. Every theorem carries a status: Established, Conditional (on E), Open/Conjecture.
grep -Fq '[Established' $TEX_FILES \
  || fail "missing '[Established' theorem label"
grep -Fq 'Conditional' $TEX_FILES \
  || fail "missing 'Conditional' status label"
grep -Eq 'Open|Conjecture' $TEX_FILES \
  || fail "missing 'Open/Conjecture' status label"

# 9. Shift/derivation macros.
grep -Fq '\newcommand{\Pshift}' "$PAPER_DIR/main.tex" \
  || fail "missing \\Pshift macro in main.tex"
grep -Fq '\newcommand{\Dmap}' "$PAPER_DIR/main.tex" \
  || fail "missing \\Dmap macro in main.tex"

echo "nomenclature OK"
