# Invariant Rings of Adjacent-Quadratic Triangular Derivations

## Overview

This repository contains the manuscript, exact computational
certificates, and Lean 4 formalization for the invariant rings of the
adjacent-quadratic family of triangular derivations
`D_N(a_n) = a_{n+1} a_{n+2}` on `A_N = k[a_0..a_N]` over a
characteristic-zero field `k`.

## Main theorem

For `N = 5`, the invariant ring is finitely generated:

```text
A_5^{D_5} = C_5[F_{46}^{int}]
```

where `C_5 = k[p,q,J_1,J_2,F_0,H]` is a normal hypersurface and
`F_{46}^{int}` is an explicit weight-46 invariant outside `C_5`. Two
successive obstructions (`H` at weight 24, `F_{46}^{int}` at weight 46)
force the two extensions; a second slice chart plus exact `q`- and
`p`-saturation prove no further generator exists. The closed ring is a
codimension-two complete intersection with exact Hilbert series,
torsion filtration, singular locus, and normality.

## Paper

The manuscript is distributed as `paper/main.pdf`. (The LaTeX source
is maintained privately and is not part of the public release.)

## Repository structure

```text
paper/          manuscript source and bibliography
scripts/cas/    exact SymPy/Sage verification scripts
scripts/sage/   exact Sage rank/elimination sweeps
scripts/…       one-command closure reproduction (see below)
data/           recorded computation logs (checksummed)
formalize/      Lean 4 formalization (AdjQuad project)
ENVIRONMENT     pinned software versions
CHECKSUMS       SHA-256 hashes of scripts and logs
SUPPLEMENT_README.md  theorem → script → log → witness index
```

## Reproducibility

Exact claims use rational arithmetic over `Q` and transfer to any
characteristic-zero field by flat base change (proved in the paper);
finite-field runs are consistency checks only, never proofs. The
decisive closure certificates reproduce with one command (SageMath
10.9, SymPy 1.14.0; see `ENVIRONMENT`):

```text
sh scripts/reproduce_closure.sh
```

This re-runs both saturation eliminations, the second-chart
certificate, the plinth element and chart-transition checks, the
chart-intersection certificate, and the `F_46` normalization gate,
checking each pass marker. Expected markers and the theorem each step
certifies are listed in the script header and in
`SUPPLEMENT_README.md`.

## Formal verification

Selected identities, weights, tops, the `H`-exclusion predicate, and
per-weight spanning through weight 14 are checked in core Lean 4
(without Mathlib) by native evaluation; see
`paper/12-certification.tex` for the manifest and per-theorem axiom
footprints. Build with `cd formalize && lake build AdjQuad`. What is
formally checked versus paper-level is stated per theorem; "formally
verified" never means the whole paper.

## N = 6 status

The `B`-level (`a_0`-free) ring at `N = 6` is exact by transport. The
`A_6` denominator program is certified through total degree 13
(degree 14 computationally blocked, not claimed); the `A_6` invariant
ring itself remains open. See the `N = 6` appendix and
`paper/15-status-matrix.tex` for the precise boundary.

## Citation

```text
Adly, Ahmed M. Invariant Rings of Adjacent-Quadratic Triangular
Derivations. 2026.
```

See `CITATION.cff` for machine-readable metadata.

## License

The project (code, manuscript PDF, and documentation) is licensed
under the Apache License, Version 2.0. See `LICENSE`.
