#!/bin/sh
# One-command reproduction of the decisive N=5 closure certificates.
# Usage: sh scripts/reproduce_closure.sh   (run from the repository root)
# Requires: SageMath 10.9 (exact QQ elimination), Python 3.14 with SymPy
#   1.14.0 for the SymPy checks (see ENVIRONMENT for the pinned stack).
# What it proves: NOTHING by itself. Each step re-runs a pinned script and
#   checks its pass marker; the mathematics (what the marker implies) is in
#   the cited theorem. Any failure aborts with a diagnostic; exit 0 means
#   every decisive marker reproduced.
# Expected runtimes on the reference machine are noted per step; the two
#   Sage eliminations dominate. Logs below are the recorded outputs
#   (data/*.log); this script regenerates them fresh into /tmp and compares
#   only the pass markers, not timings.
set -u

fail() {
  echo "reproduce_closure FAIL: $1" >&2
  exit 1
}

command -v sage >/dev/null 2>&1 \
  || fail "SageMath not found (ENVIRONMENT pins SageMath 10.9)"
command -v python3 >/dev/null 2>&1 || fail "python3 not found"
python3 -c "import sympy" 2>/dev/null \
  || fail "SymPy not found (ENVIRONMENT pins SymPy 1.14.0)"

OUT="/tmp/adjquad_repro"
mkdir -p "$OUT" || fail "cannot create $OUT"

# Step 1. q-elimination: J_q cap QQ[kept] = (S, p^2T-E, Q).
#   Certifies Lemma lem:q-elimination-cert (~1.3 s recorded).
#   Implies thm:q-saturation via the lift-and-cancel argument.
sage scripts/cas/eliminate_q.sage > "$OUT/eliminate_q.log" 2>&1 \
  || fail "eliminate_q.sage errored (see $OUT/eliminate_q.log)"
grep -q "EQUAL: True" "$OUT/eliminate_q.log" \
  || fail "q-elimination EQUAL marker missing"
echo "step 1 OK: q-elimination EQUAL: True"

# Step 2. p-elimination: J_p cap QQ[kept] = (S, cbar46).
#   Certifies Lemma lem:p-elimination-cert (~0.2 s recorded).
#   Implies thm:residual-presentation, then thm:p-saturation.
sage scripts/cas/eliminate_p.sage > "$OUT/eliminate_p.log" 2>&1 \
  || fail "eliminate_p.sage errored (see $OUT/eliminate_p.log)"
grep -q "EQUAL: True" "$OUT/eliminate_p.log" \
  || fail "p-elimination EQUAL marker missing"
echo "step 2 OK: p-elimination EQUAL: True"

# Step 3. Second chart: D5(NUM_b) = 0 for all projected coordinates,
#   NUM_a0 has 456 terms (~40 s recorded for the a0 check).
#   Certifies thm:chart-local (with thm:second-chart) via the slice
#   generation lemma.
python3 scripts/cas/chart_cert.py > "$OUT/chart_cert.log" 2>&1 \
  || fail "chart_cert.py errored (see $OUT/chart_cert.log)"
[ "$(grep -c 'D(NUM)==0: True' "$OUT/chart_cert.log")" -eq 4 ] \
  || fail "second-chart D(NUM)==0 markers missing (want 4)"
echo "step 3 OK: second chart, 4/4 D(NUM)==0"

# Step 4. Plinth element + transition: D5(g13) = f13, q ∤ f13,
#   s1 - s0 = F0/(q f13). Certifies thm:f13 and the chart transition.
python3 scripts/cas/check_plinth.py > "$OUT/plinth.log" 2>&1 \
  || fail "check_plinth.py errored (see $OUT/plinth.log)"
grep -q "^plinth OK" "$OUT/plinth.log" \
  || fail "plinth OK marker missing"
echo "step 4 OK: plinth element and transition"

# Step 5. Chart intersection certs: q ∤ J2,h and p ∤ J1,J2,h (item M5),
#   the machine input to lem:chart-intersection (A_pq ∩ A_f13 = A_p).
python3 scripts/cas/check_plinth_module.py > "$OUT/plinth_module.log" 2>&1 \
  || fail "check_plinth_module.py errored (see $OUT/plinth_module.log)"
grep -q "PASS M5" "$OUT/plinth_module.log" \
  || fail "chart-intersection M5 marker missing"
echo "step 5 OK: chart-intersection non-divisibility (M5)"

# Step 6. Source gates: F46 normalization (exact identities use int form;
# skipped with a marker in trees without the private manuscript source).
sh scripts/cas/check_f46_normalization.sh > "$OUT/f46_gate.log" 2>&1 \
  || fail "F46 normalization gate failed (see $OUT/f46_gate.log)"
GATE_MSG=$(cat "$OUT/f46_gate.log")
case "$GATE_MSG" in
  "f46-normalization OK"|"f46-normalization SKIP"*) ;;
  *) fail "F46 normalization gate failed (see $OUT/f46_gate.log)" ;;
esac
echo "step 6 OK: F46 normalization gate ($GATE_MSG)"

echo "reproduce_closure OK: all 6 closure markers reproduced"
