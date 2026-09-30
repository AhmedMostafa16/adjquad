"""Five- vs six-generator Fibonacci-weight monomial counts (pure integer DP).

Coins are the generator weights: s5 uses [1,1,6,4,14] (p,q,J1,J2,F0),
s6 adds 24 (H). Order of the two 1-coins matches check_s6.s6 (two
weight-1 types); coin order does not affect counts. This script proves
nothing about invariant rings: it is combinatorics for the paper's
s5/s6 remarks. Cross-checked against check_s6.s6 by the oracle test.

Run: python3 scripts/cas/s5_vs_s6_table.py
"""

S5_COINS = [1, 1, 6, 4, 14]
S6_COINS = [1, 1, 6, 4, 14, 24]


def coin_count(w, coins):
    if w < 0:
        return 0
    dp = [0] * (w + 1)
    dp[0] = 1
    for coin in coins:
        ndp = [0] * (w + 1)
        for s in range(w + 1):
            for e in range(s // coin + 1):
                ndp[s] += dp[s - e * coin]
        dp = ndp
    return dp[w]


def first_deviation(wmax=40):
    for w in range(wmax + 1):
        if coin_count(w, S5_COINS) != coin_count(w, S6_COINS):
            return w
    return -1


def main():
    print("w s5 s6 s6-s5")
    for w in range(41):
        a, b = coin_count(w, S5_COINS), coin_count(w, S6_COINS)
        print("%d %d %d %d" % (w, a, b, b - a))
    print("first deviation at w=%d" % first_deviation())
    print("s5_vs_s6_table OK")


if __name__ == "__main__":
    main()
