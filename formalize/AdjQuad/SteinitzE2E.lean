import AdjQuad.Witness

/- The corrected equal-size spanning theorem
    (`steinitz_span_eq`, existential data-dependent denominator `d'`)
    holds on the singleton instance that refuted the original fixed
    `d ^ U.length` contract (`SteinitzCounterexample.lean`) and on a
    non-degenerate 2-dimensional instance. -/

-- Instance 1: the refuting instance. The original contract demanded
-- `1 = 2*c` over `Int` (false); the corrected contract holds
-- (witness `d' = 2`: `2•[1] = 1•[2]`).
def U1 : IMat := [[1]]
def V1 : IMat := [[2]]

theorem steinitz_span_eq_singleton :
    ∀ u ∈ U1, ∃ d' coeffs, d' ≠ 0 ∧ coeffs.length = V1.length ∧
      vecSmul d' u = lincomb coeffs V1 :=
  steinitz_span_eq U1 V1 1 (by decide) 1
    (by intro u hu; simp only [U1, List.mem_singleton] at hu; subst u; rfl)
    (by intro v hv; simp only [V1, List.mem_singleton] at hv; subst v; rfl)
    (by decide)
    (by
      intro v hv
      simp only [V1, List.mem_singleton] at hv
      subst v
      exact ⟨[2], rfl, by decide⟩)
    (by
      intro c hc hz
      simp only [V1] at hc hz ⊢
      cases c with
      | nil => simp at hc
      | cons a rest =>
        have hr : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hc)
        subst rest
        simp [lincomb, zeroVec, List.range_succ] at hz ⊢
        omega)

-- Instance 2: 2-dimensional. `U` = standard basis, `V` = scaled basis;
-- the corrected contract gives `d' = 2` for `[1,0]` and `d' = 3` for
-- `[0,1]` (both are unit lincombs of `V` after scaling).
def U2 : IMat := [[1, 0], [0, 1]]
def V2 : IMat := [[2, 0], [0, 3]]

theorem steinitz_span_eq_2d :
    ∀ u ∈ U2, ∃ d' coeffs, d' ≠ 0 ∧ coeffs.length = V2.length ∧
      vecSmul d' u = lincomb coeffs V2 :=
  steinitz_span_eq U2 V2 1 (by decide) 2
    (by
      intro u hu
      dsimp only [U2] at hu
      rw [List.mem_cons] at hu
      cases hu with
      | inl => subst u; rfl
      | inr h =>
        rw [List.mem_cons] at h
        cases h with
        | inl => subst u; rfl
        | inr h2 => simp at h2)
    (by
      intro v hv
      dsimp only [V2] at hv
      rw [List.mem_cons] at hv
      cases hv with
      | inl => subst v; rfl
      | inr h =>
        rw [List.mem_cons] at h
        cases h with
        | inl => subst v; rfl
        | inr h2 => simp at h2)
    (by decide)
    (by
      intro v hv
      dsimp only [V2] at hv
      rw [List.mem_cons] at hv
      cases hv with
      | inl => subst v; exact ⟨[2, 0], rfl, by decide⟩
      | inr h =>
        rw [List.mem_cons] at h
        cases h with
        | inl => subst v; exact ⟨[0, 3], rfl, by decide⟩
        | inr h2 => simp at h2)
    (by
      intro c hc hz
      simp only [V2] at hc hz ⊢
      cases c with
      | nil => simp at hc
      | cons a rest =>
        cases rest with
        | nil => simp at hc
        | cons b r =>
          have hr : r = [] := List.eq_nil_of_length_eq_zero (by simpa using hc)
          subst r
          simp [lincomb, zeroVec, List.range_succ] at hz ⊢
          omega)