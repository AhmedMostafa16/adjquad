import AdjQuad.Generation

open scoped Rat

namespace GenerationClosure

/-- Construction weights are retained even when a generator product cancels. -/
def Generated (F : Poly) : Prop :=
  ∃ monos : List (Poly × Nat), (∀ q ∈ monos, q.1 ∈ genMonos q.2) ∧
    ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧ cs.length = monos.length ∧
      polySmulInt d F = polyLincomb cs (monos.map Prod.fst)

private theorem lc_append (as bs : List Int) (ps qs : List Poly)
    (hlen : as.length = ps.length) :
    polyLincomb (as ++ bs) (ps ++ qs) =
      polyAdd (polyLincomb as ps) (polyLincomb bs qs) := by
  induction as generalizing ps with
  | nil =>
    have hp : ps = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst ps
    simp only [List.nil_append, polyLincomb]
    exact (polyAdd_empty_left _ (polyLincomb_normalized bs qs).1
      (polyLincomb_normalized bs qs).2.1 (polyLincomb_normalized bs qs).2.2).symm
  | cons a as ih =>
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append, polyLincomb]
      rw [ih ps hlen, polyAdd_assoc]

private theorem eval_lc_scale (a : Int) (cs : List Int) (ps : List Poly)
    (x : Exp) :
    evalCoeff (polyLincomb (cs.map (a * ·)) ps) x =
      (a : Rat) * evalCoeff (polyLincomb cs ps) x := by
  induction cs generalizing ps with
  | nil => simp [polyLincomb, evalCoeff_nil, Rat.mul_zero]
  | cons c cs ih =>
    cases ps with
    | nil => simp [polyLincomb, evalCoeff_nil, Rat.mul_zero]
    | cons p ps =>
      simp only [List.map_cons, polyLincomb, evalCoeff_polyAdd,
        evalCoeff_polySmulInt, ih, Rat.intCast_mul, Rat.mul_add, Rat.mul_assoc]

/-- Two independent denominators combine by multiplication, including a
zero outer coefficient; no normalization of the generator monomials is needed. -/
theorem generated_add_smul (F Q : Poly) (c : Int)
    (hF : Generated F) (hQ : Generated Q) :
    Generated (polyAdd (polySmulInt c F) Q) := by
  obtain ⟨ms, hms, as, a, ha, hla, hea⟩ := hF
  obtain ⟨ns, hns, bs, b, hb, hlb, heb⟩ := hQ
  have hab : a * b ≠ 0 := Int.mul_ne_zero ha hb
  let cs := as.map ((b * c) * ·) ++ bs.map (a * ·)
  refine ⟨ms ++ ns, ?_, cs, a * b, hab, ?_, ?_⟩
  · intro q hq
    exact (List.mem_append.mp hq).elim (hms q) (hns q)
  · simp [cs, hla, hlb]
  · have hn := polyLincomb_normalized cs ((ms ++ ns).map Prod.fst)
    apply normalized_eq_of_same_eval _ _
      (smul_noZeros _ hab _ (normalize_noZeros _)) hn.1
      (smul_nodup _ _ (normalize_nodup _)) hn.2.1
      (smul_pairwise _ _ (sortPoly_pairwise _)) hn.2.2
    intro x
    have ea := congrArg (fun P => evalCoeff P x) hea
    have eb := congrArg (fun P => evalCoeff P x) heb
    simp only [evalCoeff_polySmulInt] at ea eb
    simp only [cs, List.map_append]
    rw [lc_append _ _ _ _ (by simp [hla])]
    simp only [evalCoeff_polyAdd, evalCoeff_normalize, evalCoeff_append,
      eval_lc_scale, ← ea, ← eb, evalCoeff_polySmulInt, Rat.intCast_mul, Rat.mul_add]
    congr 1
    · simp only [← Rat.mul_assoc]
      rw [Rat.mul_comm (a : Rat) (b : Rat), Rat.mul_assoc (b : Rat) (a : Rat),
        Rat.mul_comm (a : Rat) (c : Rat), ← Rat.mul_assoc]
    · exact Rat.mul_assoc _ _ _

theorem generated_zero : Generated [] := by
  exact ⟨[], by simp, [], 1, by decide, rfl, rfl⟩

/-- Substitute finitely many generated parts and clear all their denominators. -/
theorem generated_lincomb (cs : List Int) (parts : List Poly)
    (hparts : ∀ G ∈ parts, Generated G) : Generated (polyLincomb cs parts) := by
  induction cs generalizing parts with
  | nil => exact generated_zero
  | cons c cs ih =>
    cases parts with
    | nil => exact generated_zero
    | cons G parts =>
      exact generated_add_smul G (polyLincomb cs parts) c
        (hparts G (by simp)) (ih parts (fun P hP => hparts P (by simp [hP])))

/-- A scaled decomposition followed by generated parts gives a generated
polynomial; the outer and inner denominators are both retained. -/
theorem generated_of_decomposition (F : Poly) (parts : List Poly)
    (cs : List Int) (d : Int) (hd : d ≠ 0)
    (he : polySmulInt d F = polyLincomb cs parts)
    (hparts : ∀ G ∈ parts, Generated G) : Generated F := by
  obtain ⟨ms, hms, as, a, ha, hla, hea⟩ := generated_lincomb cs parts hparts
  refine ⟨ms, hms, as, a * d, Int.mul_ne_zero ha hd, hla, ?_⟩
  rw [← he] at hea
  have hmul : polySmulInt a (polySmulInt d F) = polySmulInt (a * d) F := by
    simp only [polySmulInt, List.map_map]
    apply List.map_congr_left
    intro m hm
    simp only [Function.comp_apply, Rat.intCast_mul, Rat.mul_assoc]
  rw [hmul] at hea
  exact hea

/-- Exact polynomial output expected from the checked per-weight span theorem. -/
def LocalSpan (Wmax : Nat) : Prop :=
  ∀ w, w ≤ Wmax → ∀ F : Poly,
    hasNoZeros F → hasNoDups F →
    List.Pairwise (fun a b => monoLE a b = true) F →
    supp6 F → homogeneous F w → D F = [] →
    ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧
      cs.length = (genMonos w).length ∧
      polySmulInt d F = polyLincomb cs (genMonos w)

private theorem eval_lc_ones (parts : List Poly) (x : Exp) :
    evalCoeff (polyLincomb (List.replicate parts.length 1) parts) x =
      (parts.map (fun P => evalCoeff P x)).sum := by
  induction parts with
  | nil => rfl
  | cons P parts ih =>
    simp only [List.length_cons, List.replicate_succ, polyLincomb,
      evalCoeff_polyAdd, evalCoeff_polySmulInt, Rat.intCast_ofNat,
      Rat.one_mul, List.map_cons, List.sum_cons, ih]

/-- Split a bounded invariant into exact-weight invariant parts, apply local
spanning to each, and combine their denominators. -/
theorem generated_bounded (Wmax : Nat) (hlocal : LocalSpan Wmax)
    (F : Poly) (h0 : hasNoZeros F) (hd : hasNoDups F)
    (hp : List.Pairwise (fun a b => monoLE a b = true) F)
    (hsupp : supp6 F) (hDF : D F = []) (hw : weightedDegree F ≤ Wmax) :
    Generated F := by
  let part := fun w => F.filter (fun m => decide (expWeight m.2 = w))
  let parts := (List.range (weightedDegree F + 1)).map part
  have hparts : ∀ G ∈ parts, Generated G := by
    intro G hG
    obtain ⟨w, hwmem, rfl⟩ := List.mem_map.mp hG
    have hwl : w ≤ Wmax := by
      have := List.mem_range.mp hwmem
      omega
    have hz : hasNoZeros (part w) :=
      fun m hm => h0 m (List.mem_filter.mp hm).1
    have hdup : hasNoDups (part w) :=
      List.Nodup.sublist (map_filter_sublist F _ Prod.snd) hd
    have hpair : List.Pairwise (fun a b => monoLE a b = true) (part w) :=
      hp.sublist List.filter_sublist
    have hs : supp6 (part w) :=
      fun m hm => hsupp m (List.mem_filter.mp hm).1
    have hh : homogeneous (part w) w :=
      fun m hm => of_decide_eq_true (List.mem_filter.mp hm).2
    obtain ⟨cs, d, hnz, hlen, he⟩ := hlocal w hwl (part w) hz hdup hpair hs hh
      (Dsplit F w hsupp hDF)
    refine ⟨(genMonos w).map (fun P => (P, w)), ?_, cs, d, hnz, ?_, ?_⟩
    · intro q hq
      obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hq
      exact hP
    · simpa only [List.length_map] using hlen
    · simpa [List.map_map, Function.comp_def] using he
  have he : polySmulInt 1 F = polyLincomb (List.replicate parts.length 1) parts := by
    rw [polySmulInt_one]
    have hn := polyLincomb_normalized (List.replicate parts.length 1) parts
    apply normalized_eq_of_same_eval _ _ h0 hn.1 hd hn.2.1 hp hn.2.2
    intro x
    rw [eval_lc_ones]
    simpa only [parts, List.map_map, Function.comp_def, part] using
      eval_partition F (weightedDegree F) (wdeg_mem F) x
  exact generated_of_decomposition F parts _ 1 (by decide) he hparts

/-- The bound premise refers only to smaller normalized 6-support invariants,
not to generator monomials or generation. Fuel induction supplies generation
of those smaller parts, and denominator multiplication substitutes them. -/
theorem generation_closed_of_local_span (B Wmax : Nat) (hle : B ≤ Wmax)
    (hlocal : LocalSpan Wmax)
    (h_bound : ∀ F : Poly, hasNoZeros F → hasNoDups F →
      List.Pairwise (fun a b => monoLE a b = true) F →
      supp6 F → D F = [] → B < weightedDegree F →
      ∃ parts : List Poly,
        (∀ G ∈ parts, hasNoZeros G ∧ hasNoDups G ∧
          List.Pairwise (fun a b => monoLE a b = true) G ∧
          supp6 G ∧ D G = [] ∧ weightedDegree G < weightedDegree F) ∧
        ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧
          polySmulInt d F = polyLincomb cs parts)
    (F : Poly) (h0 : hasNoZeros F) (hd : hasNoDups F)
    (hp : List.Pairwise (fun a b => monoLE a b = true) F)
    (hsupp : supp6 F) (hDF : D F = []) :
    ∃ monos : List (Poly × Nat), (∀ q ∈ monos, q.1 ∈ genMonos q.2) ∧
      ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧ cs.length = monos.length ∧
        polySmulInt d F = polyLincomb cs (monos.map Prod.fst) := by
  have aux : ∀ fuel : Nat, ∀ P : Poly, weightedDegree P < fuel →
      hasNoZeros P → hasNoDups P →
      List.Pairwise (fun a b => monoLE a b = true) P →
      supp6 P → D P = [] → Generated P := by
    intro fuel
    induction fuel with
    | zero => intro P hlt; omega
    | succ fuel ih =>
      intro P hlt hP0 hPd hPp hPs hPD
      by_cases hb : weightedDegree P ≤ B
      · exact generated_bounded Wmax hlocal P hP0 hPd hPp hPs hPD
          (Nat.le_trans hb hle)
      · obtain ⟨parts, hparts, cs, d, hnz, he⟩ :=
          h_bound P hP0 hPd hPp hPs hPD (by omega)
        apply generated_of_decomposition P parts cs d hnz he
        intro G hG
        obtain ⟨hG0, hGd, hGp, hGs, hGD, hGw⟩ := hparts G hG
        exact ih G (by omega) hG0 hGd hGp hGs hGD
  exact aux (weightedDegree F + 1) F (by omega) h0 hd hp hsupp hDF

end GenerationClosure
