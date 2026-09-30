import AdjQuad.Generation

private theorem polyLincomb_insert_coeff (ps : List Poly) (as : List Int)
    (hlen : as.length = ps.length) (q : Poly) (hq : q ∈ ps) (c : Int) :
    ∃ bs : List Int, bs.length = ps.length ∧
      ∀ x, evalCoeff (polyLincomb bs ps) x =
        (c : Rat) * evalCoeff q x + evalCoeff (polyLincomb as ps) x := by
  induction ps generalizing as with
  | nil => simp at hq
  | cons p ps ih =>
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have ht : as.length = ps.length := by simpa using hlen
      rcases List.mem_cons.mp hq with he | hq
      · subst q
        refine ⟨(c + a) :: as, by simpa using hlen, ?_⟩
        intro x
        simp only [polyLincomb, evalCoeff_polyAdd, evalCoeff_polySmulInt,
          Rat.intCast_add, Rat.add_mul, Rat.add_assoc]
      · obtain ⟨bs, hb, he⟩ := ih as ht hq
        refine ⟨a :: bs, by simp [hb], ?_⟩
        intro x
        simp only [polyLincomb, evalCoeff_polyAdd, evalCoeff_polySmulInt, he]
        ac_rfl

/-- Scatter coefficients into any containing list, accumulating repeated entries. -/
theorem polyLincomb_scatter (ps qs : List Poly) (cs : List Int)
    (hlen : cs.length = qs.length) (hsub : ∀ q ∈ qs, q ∈ ps) :
    ∃ as : List Int, as.length = ps.length ∧ polyLincomb cs qs = polyLincomb as ps := by
  induction cs generalizing qs with
  | nil =>
    have hqs : qs = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst qs
    refine ⟨List.replicate ps.length 0, by simp, ?_⟩
    exact (polyLincomb_zeros _ ps (by simp) (by simp)).symm
  | cons c cs ih =>
    cases qs with
    | nil => simp at hlen
    | cons q qs =>
      have ht : cs.length = qs.length := by simpa using hlen
      obtain ⟨as, ha, he⟩ := ih qs ht
        (fun t ht => hsub t (List.mem_cons_of_mem q ht))
      obtain ⟨bs, hb, hev⟩ := polyLincomb_insert_coeff ps as ha q
        (hsub q List.mem_cons_self) c
      refine ⟨bs, hb, ?_⟩
      have hn1 := polyLincomb_normalized (c :: cs) (q :: qs)
      have hn2 := polyLincomb_normalized bs ps
      apply normalized_eq_of_same_eval _ _ hn1.1 hn2.1 hn1.2.1 hn2.2.1
        hn1.2.2 hn2.2.2
      intro x
      rw [hev, polyLincomb, evalCoeff_polyAdd, evalCoeff_polySmulInt, he]
