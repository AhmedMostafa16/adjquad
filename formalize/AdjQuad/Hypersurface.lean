import AdjQuad.CompLemmas
import AdjQuad.Exclusion

/-
Algebraic core of the N=5 hypersurface theorem
(`paper/06-global.tex`, Theorem `thm:global-hypersurface`).

Certifies the unique weight-28 relation
  S = q^4 * H - 11025 * F0^2 - 105 * q^2 * J2^5 * J1 - 9 * J2^7 = 0
in A = k[a0..a5], together with uniform weight 28 of each summand and
the assembled witness (invariance of H, exclusion H ∉ K[F0], the
relation). Invariance facts reused: `H_D_zero` (Counterexample.lean),
`D_F0_zero`, `D_J1_zero`, `D_J2_zero` (CompLemmas.lean); exclusion
reused: `H_notin_K_F0` (Exclusion.lean).

Explicitly OUT of scope for this module (remain CAS-only, `check_s6.py`):
uniqueness of S at weight 28 and the Hilbert-series identity; those need
graded linear algebra (kernel dims), not single polynomial identities.

Standalone: `lake build AdjQuad.Hypersurface`
(not imported by the root). Core-Lean only.
-/

/-- Scalar multiple `c * p` via the poly API. -/
def smul (c : Rat) (p : Poly) : Poly := polyMul [(c, zeroExp)] p

/-- The four summands of S (each uniform weight 28, certified below). -/
def S1 : Poly := polyMul (polyPow q 4) H
def S2 : Poly := smul 11025 (polyPow F0 2)
def S3 : Poly := polyMul (smul 105 (polyMul (polyPow q 2) (polyPow J2 5))) J1
def S4 : Poly := smul 9 (polyPow J2 7)

/-- The hypersurface relation `S = S1 - S2 - S3 - S4`. -/
def S : Poly := polySub (polySub (polySub S1 S2) S3) S4

/-- Mutated syzygy: 11026 instead of 11025 (FALSE identity; the kept
    regression test `S_mut_nonzero` proves the `S_rel` check below is
    non-vacuous — it was watched failing as `S_mut_is_zero` first). -/
def S_mut : Poly :=
  polySub (polySub (polySub S1 (smul 11026 (polyPow F0 2))) S3) S4

------------------------------------------------------------
-- The relation (main computation)
------------------------------------------------------------

/-- **Main result.** The weight-28 syzygy holds in A_5. -/
theorem S_rel : S = [] := by native_decide

/-- Regression: the one-coefficient mutant does NOT vanish. -/
theorem S_mut_nonzero : S_mut ≠ [] := by native_decide

------------------------------------------------------------
-- Uniform weight 28 of each summand
------------------------------------------------------------

theorem S1_weight_28 : weightedDegree S1 = 28 := by native_decide

theorem S2_weight_28 : weightedDegree S2 = 28 := by native_decide

theorem S3_weight_28 : weightedDegree S3 = 28 := by native_decide

theorem S4_weight_28 : weightedDegree S4 = 28 := by native_decide

------------------------------------------------------------
-- Assembled hypersurface witness
------------------------------------------------------------

/--
 * The Lean-certified core of `thm:global-hypersurface`: H is invariant,
 * H lies outside K[F0], and the six generators satisfy the weight-28
 * relation S = 0.
 -/
theorem hypersurface_witness : D H = [] ∧ ¬ inK_F0 H ∧ S = [] :=
  ⟨H_D_zero, H_notin_K_F0, S_rel⟩
