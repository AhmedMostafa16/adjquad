import AdjQuad.Hypersurface

/-
`H` in the hypersurface: the completed Lean certificate for the N=5
hypersurface theorem (`paper/06-global.tex`, Theorem
`thm:global-hypersurface`).

Assembles, from the ground-truth modules, the full formally verified
content of the hypersurface statement that is expressible as closed
polynomial identities over the core-only `Poly` API:
  * all SIX generators (p, q, J1, J2, F0, H) are D-invariant
    (`six_invariant`: two new trivial facts + CompLemmas trio +
    Counterexample);
  * their Fibonacci weights are exactly (1,1,6,4,14,24)
    (`six_weights`: two new trivial facts + CompLemmas +
    Counterexample);
  * H satisfies the weight-28 syzygy S = 0 alongside the five
    (`S_rel`, `S1_weight_28`--`S4_weight_28` in Hypersurface.lean);
  * H lies strictly outside the five-generator ring
    (`H_notin_K_F0`, `strict_superset_witness` in Exclusion.lean).

Non-vacuity is permanently guarded: `S_mut_nonzero` (Hypersurface.lean,
watched failing as `S_mut_is_zero` first) proves the relation check
rejects a one-coefficient mutant, and `H_ne_zero` below rules out the
degenerate reading. (A weight-25 claim for H was likewise watched
failing during development of this file.)

Explicitly OUT of scope (remain CAS-only, `check_s6.py`): that S
generates the FULL relation ideal (uniqueness), that the six generate
every invariant, and the Hilbert-series identity. Those need graded
linear algebra (kernel dimensions) and Groebner theory, neither of
which exists in the core-only API. The paper records this split
exactly: Lean-proven are the relation, the six-invariance, and the
strict superset; CAS-established are uniqueness and the series.

Standalone: `lake build AdjQuad.H_in_hypersurface`
(not imported by the root). Core-Lean only.
-/

------------------------------------------------------------
-- 1. The two trivial generator facts (closed computations)
------------------------------------------------------------

/-- `p = a4` is D-invariant (boundary rule). -/
theorem D_p_zero : D p = [] := by native_decide

/-- `q = a5` is D-invariant (boundary rule). -/
theorem D_q_zero : D q = [] := by native_decide

/-- Fibonacci weight of `p` is 1. -/
theorem p_weight_1 : weightedDegree p = 1 := by native_decide

/-- Fibonacci weight of `q` is 1. -/
theorem q_weight_1 : weightedDegree q = 1 := by native_decide

------------------------------------------------------------
-- 2. Nontriviality guard (the certificate is not about zeros)
------------------------------------------------------------

/-- `H` is a genuine (nonzero) polynomial. -/
theorem H_ne_zero : H ≠ [] := by native_decide

------------------------------------------------------------
-- 3. Assembled six-generator data
------------------------------------------------------------

/-- All six hypersurface generators are D-invariant. -/
theorem six_invariant :
    D p = [] ∧ D q = [] ∧ D J1 = [] ∧ D J2 = [] ∧ D F0 = [] ∧ D H = [] :=
  ⟨D_p_zero, D_q_zero, D_J1_zero, D_J2_zero, D_F0_zero, H_D_zero⟩

/-- Their Fibonacci weights are exactly (1,1,6,4,14,24). -/
theorem six_weights :
    weightedDegree p = 1 ∧ weightedDegree q = 1 ∧
    weightedDegree J1 = 6 ∧ weightedDegree J2 = 4 ∧
    weightedDegree F0 = 14 ∧ weightedDegree H = 24 :=
  ⟨p_weight_1, q_weight_1, weightedDegree_J1, weightedDegree_J2,
   weightedDegree_F0, weightedDegree_H⟩

------------------------------------------------------------
-- 4. The certificate
------------------------------------------------------------

/--
 * **Certificate.** H sits in the hypersurface alongside the five:
 * all six generators are invariant with weights (1,1,6,4,14,24),
 * they satisfy the weight-28 syzygy S = 0, and H lies strictly
 * outside the five-generator ring.
 -/
theorem H_in_hypersurface_certificate :
    (D p = [] ∧ D q = [] ∧ D J1 = [] ∧ D J2 = [] ∧ D F0 = [] ∧ D H = [])
    ∧ (weightedDegree p = 1 ∧ weightedDegree q = 1 ∧
       weightedDegree J1 = 6 ∧ weightedDegree J2 = 4 ∧
       weightedDegree F0 = 14 ∧ weightedDegree H = 24)
    ∧ S = [] ∧ ¬ inK_F0 H :=
  ⟨six_invariant, six_weights, S_rel, H_notin_K_F0⟩
