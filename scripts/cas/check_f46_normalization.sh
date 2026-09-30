#!/bin/sh
# F46 normalization gate: every EXACT algebraic identity must use the
# cleared integral form F_{46}^{\mathrm{int}} (top 121550625 a0^4 a4^6 a5^8).
# Scale-invariant uses (tops, valuations, nonmembership, dimensions,
# F46-multiples) may use bare F46 and are NOT flagged here.
# Usage: sh scripts/cas/check_f46_normalization.sh  (repo root)
# Prints "f46-normalization OK" and exits 0 iff all checks pass.
set -u

fail() {
  echo "f46-normalization FAIL: $1" >&2
  exit 1
}

TEX_FILES="paper"/*.tex

# In trees without the (private) manuscript source — e.g. the public
# snapshot, which distributes paper/main.pdf only — there is nothing to
# gate; report SKIP rather than FAIL.
if ! ls paper/*.tex >/dev/null 2>&1; then
  echo "f46-normalization SKIP (no manuscript source in tree)"
  exit 0
fi

# 1. No bare closed-ring C_5[F_{46}]: always C_5[F_{46}^{\mathrm{int}}].
if grep -Fq 'C_5[F_{46}]' $TEX_FILES; then
  grep -Fn 'C_5[F_{46}]' $TEX_FILES | head -5 >&2
  fail "bare C_5[F_{46}] found (use C_5[F_{46}^{\\mathrm{int}}])"
fi

# 2. No bare p^2F_{46} relation: always p^2F_{46}^{\mathrm{int}} = E.
#    Matches p^2F_{46} NOT followed by ^{...} (ERE on the literal text).
if grep -Eq 'p\^2F_\{46\}([^^]|$)' $TEX_FILES; then
  grep -En 'p\^2F_\{46\}([^^]|$)' $TEX_FILES | head -5 >&2
  fail "bare p^2F_{46} relation found (use p^2F_{46}^{\\mathrm{int}})"
fi

# 3. No bare T \mapsto F_{46}: always T \mapsto F_{46}^{\mathrm{int}}.
if grep -Eq 'mapsto F_\{46\}([^^]|$)' $TEX_FILES; then
  grep -En 'mapsto F_\{46\}([^^]|$)' $TEX_FILES | head -5 >&2
  fail "bare T-mapsto-F_{46} found (use F_{46}^{\\mathrm{int}})"
fi

# 4. The int/rat split must be defined exactly once in thm:F46.
DEFN_COUNT=$(grep -Fc 'F_{46}^{\mathrm{rat}}=F_{46}^{\mathrm{int}}/26460' paper/14-second-witness.tex)
[ "$DEFN_COUNT" -ge 1 ] \
  || fail "int/rat split definition missing from thm:F46"

echo "f46-normalization OK"
