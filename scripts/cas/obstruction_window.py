"""Hidden-generator birth window from (weight, a0-degree) pairs.

Given known generators as (weight, a0deg) pairs and the a0 variable
weight, return (lo, hi) with lo = 2 * a0_var_weight (a0^2 monomially
possible only at w >= lo) and hi = 2 * wc - 1 where wc = min weight
with a0deg == 1 (R5-style safety forbids a0^2 below 2*wc).

N=5 inputs: p,q (1,0); J1 (6,0); J2 (4,0); F0 (14,1) [weights: GEN_WTS
in emit_witnesses.py:28 and CompLemmas weight facts; a0-degrees:
p_base..F0_base safety facts in Exclusion.lean and H_has_a0_sq in
Counterexample.lean:59]. N=6 row is OPEN-gated: add only after the
H20 (weight, a0deg) pair is confirmed against lem:n6-H20.
This script predicts the window; it proves nothing.

Run: python3 scripts/cas/obstruction_window.py
"""


def birth_window(pairs, a0_var_weight):
    carriers = [w for (w, d) in pairs if d == 1]
    if not carriers:
        raise ValueError("need at least one a0-carrying generator")
    wc = min(carriers)
    return (2 * a0_var_weight, 2 * wc - 1)


def main():
    n5 = [(1, 0), (1, 0), (6, 0), (4, 0), (14, 1)]
    lo, hi = birth_window(n5, 8)
    print("N5 birth window: [%d, %d]" % (lo, hi))
    print("H at w=24 inside: %s" % (lo <= 24 <= hi))
    print("obstruction_window OK")


if __name__ == "__main__":
    main()
