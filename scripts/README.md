CAS scripts
-----------

SymPy-only plus stdlib. Run from the repository root, e.g.
`python3 scripts/cas/check_s6.py`. Each `check_*.py` prints
`PASS`/`FAIL` lines and exits nonzero on failure.

Core checks:

    check_A.py          D_N harness (apply_D, verify_D); dependency of the rest
    check_s6.py         N=5 hypersurface identities, W-expansion bounds, Hilbert series
    check_kernel.py     five-variable kernel and descent B^D = K
    check_slice.py      slice s = x/(pq), D(s) = 1, and reconstruction
    check_plemma.py     p-lemma
    check_stage1.py     N<=4 base

N=6 (Fibonacci weights 8,5,3,2,1,1):

    check_N6_weighted_v2.py   per-weight kernel dims vs free/hypersurface count, to w=32
    check_N6_kernel.py        B6 kernel spot checks
    n6_kernel_sage.py         SageMath oracle (requires Sage; optional cross-check)

Witness emission:

    emit_witnesses.py   exact-QQ rank/nullity witnesses for D|V_w,
                        Lean input for formalize/AdjQuad/WitnessDataB*.lean

Probes and tables (`probe_*.py`, `s5_vs_s6_table.py`, `obstruction_window.py`,
`cert_predictor.py`) are diagnostic; they do not establish spanning.

Tests `test_*.py` are oracles for the corresponding checks.
`check_nomenclature.sh` gates paper naming conventions.
