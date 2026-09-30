import AdjQuad.GeneratorSupport
import AdjQuad.GenerationScatter

open scoped Rat

namespace GenerationSpan

private theorem eval_lc_range (cs : List Int) (ps : List Poly)
    (hlen : cs.length = ps.length) (x : Exp) :
    evalCoeff (polyLincomb cs ps) x =
      ((List.range cs.length).map fun j =>
        ((cs[j]?.getD 0 : Int) : Rat) * evalCoeff (ps[j]?.getD []) x).sum := by
  induction cs generalizing ps with
  | nil =>
    have : ps = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst ps
    rfl
  | cons c cs ih =>
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      have ht : cs.length = ps.length := by simpa using hlen
      simp only [polyLincomb, evalCoeff_polyAdd, evalCoeff_polySmulInt,
        List.length_cons, range_succ_head, List.map_cons, List.sum_cons,
        List.getElem?_cons_zero, Option.getD_some, List.map_map,
        Function.comp_def, List.getElem?_cons_succ, ih ps ht]

private theorem decode_indices (w : Nat) (sel : List Nat) (G : IMat) (D0 : Int)
    (h : gselDecode w sel G D0 = true) :
    D0 ≠ 0 ∧ ∀ j, j < sel.length → (sel[j]?.getD 0) < (genMonos w).length := by
  simp only [gselDecode, Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1.1.1.1, ?_⟩
  intro j hj
  have hall := h.1.2
  have hm : decide ((sel[j]?.getD 0) < (genMonos w).length) ∈
      (List.range sel.length).map (fun j =>
        decide ((sel[j]?.getD 0) < (genMonos w).length)) :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  exact of_decide_eq_true ((List.all_eq_true.mp hall) _ hm)

/-- Matrix kernel spanning lifts to the actual selected rational generator
polynomials; decode denominators and input denominators are both explicit. -/
theorem span_selected (w : Nat) (sel : List Nat) (G : IMat) (D0 : Int)
    (hdec : gselDecode w sel G D0 = true)
    (hGr : imatRows G = (monoW w).length) (hGc : imatCols G = sel.length)
    (hk : 0 < sel.length)
    (hker : ∀ v : List Int, v.length = (monoW w).length →
      matVecMul (dmat w) v = zeroVec (monoW w).length →
      ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧ cs.length = sel.length ∧
        vecSmul d v = lincomb cs (imatTranspose G))
    (F : Poly) (h0 : hasNoZeros F) (hd : hasNoDups F)
    (hp : List.Pairwise (fun a b => monoLE a b = true) F)
    (hs : supp6 F) (hh : homogeneous F w) (hDF : D F = []) :
    ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧ cs.length = sel.length ∧
      polySmulInt d F = polyLincomb cs
        (sel.map (fun j => ((genMonos w)[j]?).getD [])) := by
  obtain ⟨L, F', hL, heF, hInt, hz, hdup, hpair, hD, hhom, hsupp⟩ :=
    scaled_invariant F w h0 hd hp hDF hh hs
  obtain ⟨cs, d, hnz, hlen, he⟩ := hker (coordIn (monoW w) F')
    (coordIn_length _ _) (invariant_coord_kernel w F' hInt hdup hz hD hhom hsupp)
  have hLn : (L : Int) ≠ 0 := by omega
  have hden : d * (L : Int) ≠ 0 := Int.mul_ne_zero hnz hLn
  let ps := sel.map (fun j => ((genMonos w)[j]?).getD [])
  have hps : ∀ P ∈ ps, P ∈ genMonos w := by
    intro P hP
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hP
    obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hj
    have hsI : sel[i]?.getD 0 = j := by rw [List.getElem?_eq_getElem hi, Option.getD_some, hei]
    have hjn := (decode_indices w sel G D0 hdec).2 i hi
    rw [hsI] at hjn
    rw [List.getElem?_eq_getElem hjn, Option.getD_some]
    exact List.getElem_mem hjn
  refine ⟨cs.map (D0 * ·), d * (L : Int), hden, by simp [hlen], ?_⟩
  have hn := polyLincomb_normalized (cs.map (D0 * ·)) ps
  apply normalized_eq_of_same_eval _ _ (smul_noZeros _ hden F h0) hn.1
    (smul_nodup _ F hd) hn.2.1 (smul_pairwise _ F hp) hn.2.2
  intro x
  by_cases hx : x ∈ monoW w
  · obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hx
    have hti : i < (((imatTranspose G)[0]?).getD []).length := by
      have hkp : 0 < imatCols G := by omega
      simp [imatTranspose, List.getElem?_map, List.getElem?_range hkp, hGr]
      exact hi
    have hec := congrArg (fun v : List Int => ((v[i]?.getD 0 : Int) : Rat)) he
    rw [vecSmul_cast, lincomb_entry_cast cs _ i hti,
      coord_cast_getD _ _ i (List.mem_range.mpr hi) hInt hdup] at hec
    have hix : (monoW w)[i]?.getD [] = x := by
      rw [List.getElem?_eq_getElem hi, Option.getD_some, hei]
    rw [hix, heF, evalCoeff_polySmulInt] at hec
    have hpslen : cs.length = ps.length := by simp [ps, hlen]
    rw [evalCoeff_polySmulInt, Rat.intCast_mul, Rat.mul_assoc]
    rw [evalCoeff_polyLincomb _ _ (by simp [ps, hlen]), zipWith_map_left',
      zipWith_smul_map, ← mul_sum_dist, ← evalCoeff_polyLincomb cs ps hpslen,
      eval_lc_range cs ps hpslen]
    rw [hec, mul_sum_dist, List.map_map]
    apply congrArg
    apply List.map_congr_left
    intro j hj
    have hjk : j < sel.length := by have := List.mem_range.mp hj; omega
    have hij : i < imatRows G := by omega
    have hjc : j < imatCols G := by omega
    rw [← imatGet_rowGet_aux, transpose_entry G j i hjc hij,
      imatGet_rowGet_aux, crossmul_decode w sel G D0 hdec i j hi hjk]
    have hget : ps[j]?.getD [] = ((genMonos w)[sel[j]?.getD 0]?).getD [] := by
      simp [ps, List.getElem?_eq_getElem hjk]
    simp only [Function.comp_apply]
    rw [hget, hix]
    rw [← Rat.mul_assoc, Rat.mul_comm _ (D0 : Rat), Rat.mul_assoc]
  · have hFx := evalCoeff_homogeneous_off_basis F w hh hs x hx
    rw [evalCoeff_polySmulInt, hFx, Rat.mul_zero,
      eval_lc_range _ ps (by simp [ps, hlen])]
    symm
    apply sum_zero_terms
    intro j hj
    have hjk : j < ps.length := by
      have := List.mem_range.mp hj
      simp only [List.length_map] at this
      simp [ps, hlen] at this ⊢
      omega
    have hpm : ps[j]?.getD [] ∈ ps := by
      rw [List.getElem?_eq_getElem hjk, Option.getD_some]
      exact List.getElem_mem hjk
    rw [evalCoeff_genMonos_off_basis w _ (hps _ hpm) x hx, Rat.mul_zero]

/-- Polynomial lift of matrix kernel spanning. The final checked-bundle wrapper
must discharge `hker`; no polynomial spanning or equality is assumed here. -/
theorem span_of_kernel_span (w : Nat) (sel : List Nat) (G : IMat) (D0 : Int)
    (hdec : gselDecode w sel G D0 = true)
    (hGr : imatRows G = (monoW w).length) (hGc : imatCols G = sel.length)
    (hk : 0 < sel.length)
    (hker : ∀ v : List Int, v.length = (monoW w).length →
      matVecMul (dmat w) v = zeroVec (monoW w).length →
      ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧ cs.length = sel.length ∧
        vecSmul d v = lincomb cs (imatTranspose G))
    (F : Poly) (h0 : hasNoZeros F) (hd : hasNoDups F)
    (hp : List.Pairwise (fun a b => monoLE a b = true) F)
    (hs : supp6 F) (hh : homogeneous F w) (hDF : D F = []) :
    ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧ cs.length = (genMonos w).length ∧
      polySmulInt d F = polyLincomb cs (genMonos w) := by
  obtain ⟨cs, d, hnz, hlen, he⟩ :=
    span_selected w sel G D0 hdec hGr hGc hk hker F h0 hd hp hs hh hDF
  have hsub : ∀ P ∈ sel.map (fun j => ((genMonos w)[j]?).getD []),
      P ∈ genMonos w := by
    intro P hP
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hP
    obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hj
    have hsI : sel[i]?.getD 0 = j := by
      rw [List.getElem?_eq_getElem hi, Option.getD_some, hei]
    have hjn := (decode_indices w sel G D0 hdec).2 i hi
    rw [hsI] at hjn
    rw [List.getElem?_eq_getElem hjn, Option.getD_some]
    exact List.getElem_mem hjn
  obtain ⟨as, has, hea⟩ := polyLincomb_scatter (genMonos w) _ cs
    (by simpa only [List.length_map] using hlen) hsub
  exact ⟨as, d, hnz, has, he.trans hea⟩

end GenerationSpan
