import AdjQuad.Exclusion
import AdjQuad.WeightData
import AdjQuad.Generation

/-- Every K[F0] monomial of a0-degree 1 weighs at least 14. -/
theorem a0deg1_ge14 {y : Poly} (h : inK_F0 y) {m : Mono} (hm : m ∈ y)
    (h1 : a0degMono m = 1) : 14 ≤ expWeight m.2 := by
  have hs := inK_F0_weight_ge_14_a0deg h m hm
  rw [h1] at hs
  simpa using hs

/-- Every K[F0] monomial of a0-degree ≥ 2 weighs at least 28. -/
theorem a0deg2_ge28 {y : Poly} (h : inK_F0 y) {m : Mono} (hm : m ∈ y)
    (h2 : 2 ≤ a0degMono m) : 28 ≤ expWeight m.2 := by
  have hs := inK_F0_weight_ge_14_a0deg h m hm
  omega

/-- Monomial-level lower bound: a0-exponent 2 forces weight ≥ 16. -/
theorem a0exp2_weight_ge16 {e : Exp} (h6 : e.length = 6) (h2 : a0deg e = 2) :
    16 ≤ expWeight e := by
  obtain ⟨a, b, c, d, e', f, rfl⟩ := expSix e h6
  have h2' : a = 2 := by simpa [a0deg] using h2
  have hw : expWeight [a, b, c, d, e', f]
      = 8 * a + 5 * b + 3 * c + 2 * d + e' + f := by
    simp [expWeight, weights]
  omega

/-- Homogeneous detector, degree 1: a homogeneous K[F0] element carrying
    an a0-degree-1 term weighs at least 14. -/
theorem homogeneous_a0deg1_ge14 {y : Poly} (h : inK_F0 y) {w : Nat}
    (hh : homogeneous y w) {m : Mono} (hm : m ∈ y)
    (h1 : a0degMono m = 1) : 14 ≤ w := by
  have hs := inK_F0_weight_ge_14_a0deg h m hm
  rw [h1] at hs
  have hw : expWeight m.2 = w := hh m hm
  omega

/-- Homogeneous detector, degree 2: a homogeneous K[F0] element carrying
    an a0-degree-2 term weighs at least 28. H (weight 24 with its a0^2
    term `11025 a0^2 a4^4 a5^4`) is the recorded instance falling outside
    K[F0] (`H_notin_K_F0`): the detector fires exactly on hidden content. -/
theorem homogeneous_a0deg2_ge28 {y : Poly} (h : inK_F0 y) {w : Nat}
    (hh : homogeneous y w) {m : Mono} (hm : m ∈ y)
    (h2 : a0degMono m = 2) : 28 ≤ w := by
  have hs := inK_F0_weight_ge_14_a0deg h m hm
  rw [h2] at hs
  have hw : expWeight m.2 = w := hh m hm
  omega

/-
Full W-valuation form (paper Theorem 13.2: H_j = h_j c^j with v_q/v_p
bounds) is OPEN in Lean: stating W-expansions needs the localized ring
K_pq, W itself, and the valuations v_p/v_q, none of which exist in the
core-only API (verified absent: no Frac/Localization/K_pq/rho/W
definitions anywhere under formalize/AdjQuad/). The homogeneous
corollaries above are the maximal fraction-free fragment; they already
decide H's case via `H_notin_K_F0`.
-/
