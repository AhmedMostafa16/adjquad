import AdjQuad.Witness

/- The fixed denominator is false even for singleton lists.
   The length premises below use the intended, well-typed head-row length. -/
theorem steinitz_fixed_denominator_counterexample :
    let U : IMat := [[1]]
    let V : IMat := [[2]]
    let d : Int := 1
    d ≠ 0 ∧
    (∀ v ∈ V, ∃ c : List Int, c.length = U.length ∧
      vecSmul d v = lincomb c U) ∧
    independent V ∧ U.length ≤ V.length ∧
    (∀ u ∈ U, u.length = ((V[0]?).getD []).length) ∧
    (∀ v ∈ V, v.length = ((V[0]?).getD []).length) ∧
    ¬ (∀ u ∈ U, ∃ c : List Int, c.length = V.length ∧
      vecSmul (d ^ U.length) u = lincomb c V) := by
  dsimp
  refine ⟨by decide, ?_, ?_, by decide, ?_, ?_, ?_⟩
  · intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact ⟨[2], rfl, by decide⟩
  · intro c hc hz
    cases c with
    | nil => simp at hc
    | cons a rest =>
      have hr : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst rest
      simp [lincomb, zeroVec, List.range_succ] at hz ⊢
      omega
  · simp
  · simp
  · intro h
    obtain ⟨c, hc, he⟩ := h [1] (by simp)
    cases c with
    | nil => simp at hc
    | cons a rest =>
      have hr : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst rest
      simp [vecSmul, lincomb, List.range_succ] at he
      omega

#print axioms steinitz_fixed_denominator_counterexample
