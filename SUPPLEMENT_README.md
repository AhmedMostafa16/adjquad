# Supplement navigation index

Theorem → source → log → witness → Lean check. Every row is exact
characteristic-zero computation unless marked otherwise. Finite-field
runs are consistency checks only, never proofs. Paths below are
relative to the repository root; no path has been renamed.

Trust declarations: `exact QQ` = symbolic equality or QQ rank/nullity
over Q; `cross-check` = finite-field consistency only;
`diagnostic` = unresolved material, not theorem evidence.

## One-command reproduction (closure)

`sh scripts/reproduce_closure.sh` (repo root; SageMath 10.9 + SymPy
1.14.0 per ENVIRONMENT) re-runs the decisive closure chain and checks
each pass marker, aborting on the first failure:

| step | script | marker checked | certifies |
|---|---|---|---|
| 1 | scripts/cas/eliminate_q.sage | `EQUAL: True` | lem:q-elimination-cert |
| 2 | scripts/cas/eliminate_p.sage | `EQUAL: True` | lem:p-elimination-cert |
| 3 | scripts/cas/chart_cert.py | 4x `D(NUM)==0: True` | thm:chart-local |
| 4 | scripts/cas/check_plinth.py | `plinth OK` | thm:f13 + chart transition |
| 5 | scripts/cas/check_plinth_module.py | `PASS M5` | lem:chart-intersection input |
| 6 | scripts/cas/check_f46_normalization.sh | `f46-normalization OK` | int-form discipline |

## N=5 closure and presentation

| theorem | source script(s) | log(s) | witness | Lean check | trust |
|---|---|---|---|---|---|
| thm:closure (tower closure) | scripts/cas/eliminate_p.sage, scripts/cas/eliminate_q.sage | data/eliminate_p.log, data/eliminate_q.log | saturation equalities | partial (charts/descent pieces) | exact QQ |
| thm:relation-ideal | scripts/cas/relation_exact.sage | data/relation_exact.log | ker = (S, p²T−E) | — | exact QQ |
| thm:R-hilbert | scripts/cas/check_hilbert.py | data/hilbert.log | integer series cert | — | exact QQ |
| thm:fourth-family | scripts/cas/check_f46hf0.sage | data/f46hf0.log | rank/augmented split | — | exact QQ |
| thm:B-module | scripts/cas/check_hf0.sage | data/hf0.log | HF0 non-membership | — | exact QQ |
| thm:Sing-exact | scripts/cas/sing_fiber.sage | data/sing_fiber.log | certified primes | — | exact QQ |
| thm:R-normal | scripts/cas/sing_R.sage | data/sing_R.log | dim Sing = 3 | — | exact QQ + proof |
| thm:q-top, thm:p-envelope | scripts/cas/check_tops.py | data/tops.log | generator top-data | — | exact QQ + proof |
| prop:excess-zero/one | scripts/cas/check_excess1.py | data/excess1.log | eps-1 top values | — | exact QQ + proof |

## N=6 transport, B-level, denominator program

| theorem | source script(s) | log(s) | witness | Lean check | trust |
|---|---|---|---|---|---|
| thm:n6-B6ring | scripts/cas/check_n6_transport.py, scripts/cas/check_N6_transport_F.py | data/n6_transport.log, data/n6/transport_F.log | torsion identity, tops | H_B module (H_B.lean) | exact QQ |
| thm:n6-B6structure | (transport of above) | (transport logs) | generator table | — | exact QQ + proof |
| thm:n6-no-monomial-bound | scripts/cas/check_n6_G4.py | data/n6_G4.log | irreducibility + remainders | — | exact QQ |
| prop:n6-D2novel | scripts/cas/check_n6_D2novel.sage | data/n6_D2novel.log | rank/augmented split | H20 module (formal H20) | exact QQ |
| thm:n6-m7third | scripts/cas/check_n6_m7lift.sage | data/n6_m7lift.log | QQ (M3, N3) witness | — | exact QQ |
| thm:n6-denmod12 | scripts/cas/check_n6_denmod.py, scripts/cas/check_n6_m8wit.sage | data/n6_denmod.log, data/n6_m8wit.log | quotient table + witnesses | — | exact QQ |
| thm:n6-closure13 | scripts/cas/check_n6_m13.py | data/n6_m13.log | Q13 = 0 | — | exact QQ |

## Lean provenance

Core Lean without Mathlib; per-theorem axiom footprints in the
paper manifest (`paper/12-certification.tex`, formal-verification
manifest) and `docs/lean-axioms-battery-2026-09-27.log`. Source:
`formalize/AdjQuad/`. What is formally checked vs paper-level is
stated per theorem in the manifest; "formally verified" never means
the whole paper. This layer is a small theorem-specific
certification, not a general formalization.

## QUARANTINE: m=14 diagnostics (UNRESOLVED, not theorem evidence)

The following material is preserved for auditability only. It must
not appear in any theorem, abstract, introduction, conclusion, or
quantitative claim. Status: kernel counts stable across checks;
projection-dimension extraction unreconciled; no theorem use.

- scripts/cas/check_n6_m14.py — data/n6_m14.log (gate computation)
- scripts/cas/check_n6_m14audit.sage — data/n6_m14audit.log (rank tuple)
- scripts/cas/check_n6_m14audit2.sage — data/n6_m14audit2.log (second prime)
- scripts/cas/check_n6_m14diag.sage — data/n6_m14diag.log (kernel-basis counts)
- scripts/cas/check_n6_m14gen.sage — data/n6_m14gen.log (generated-span discriminant)
- scripts/cas/check_n6_m14probe.sage — data/n6_m14probe.log (transpose/engine probes)

## Environment

See ENVIRONMENT (versions) and CHECKSUMS (sha256 of scripts and logs).
