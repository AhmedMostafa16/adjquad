import AdjQuad.Witness

namespace KernelSpan

/-- Column-vector multiplication; dimensions are explicit in its laws. -/
def matVecMul (A : IMat) (v : List Int) : List Int :=
  (List.range (imatRows A)).map fun i =>
    sumRange (fun j => imatGet A i j * (v[j]?).getD 0) v.length

private theorem mapRange_get (n i : Nat) (f : Nat → Int) (hi : i < n) :
    (((List.range n).map f)[i]?).getD 0 = f i := by
  simp [List.getElem?_map, List.getElem?_range hi]

@[simp] theorem matVecMul_length (A : IMat) (v : List Int) :
    (matVecMul A v).length = imatRows A := by simp [matVecMul]

private theorem entry (A : IMat) (v : List Int) (i : Nat) (hi : i < imatRows A) :
    ((matVecMul A v)[i]?).getD 0 =
      sumRange (fun j => imatGet A i j * (v[j]?).getD 0) v.length :=
  mapRange_get _ _ _ hi

private theorem ext {u v : List Int} (hlen : u.length = v.length)
    (h : ∀ i, i < u.length → (u[i]?).getD 0 = (v[i]?).getD 0) : u = v := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < u.length
  · have hj : i < v.length := by omega
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some, Option.some.injEq] using h i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

private theorem zero_get (n i : Nat) : ((zeroVec n)[i]?).getD 0 = 0 := by
  by_cases h : i < n <;> simp [zeroVec, List.getElem?_replicate, h]

private theorem smul_get (d : Int) (v : List Int) (i : Nat) :
    ((vecSmul d v)[i]?).getD 0 = d * (v[i]?).getD 0 :=
  map_mul_getD_aux v d i

private theorem mul_assoc (A B : IMat) (v : List Int)
    (hab : imatCols A = imatRows B) (hv : v.length = imatCols B) :
    matVecMul A (matVecMul B v) = matVecMul (imatMul A B) v := by
  apply ext
  · simp [imatMul_rows_aux, imatRows]
  intro i hi
  have hiA : i < imatRows A := by simpa using hi
  rw [entry _ _ _ hiA, matVecMul_length,
    entry _ _ _ (by simpa [imatRows, imatMul_rows_aux] using hiA)]
  calc
    _ = sumRange (fun t => imatGet A i t *
        sumRange (fun j => imatGet B t j * (v[j]?).getD 0) v.length)
        (imatRows B) := by
      apply sumRange_congr_lt
      intro t ht
      rw [entry _ _ _ ht]
    _ = sumRange (fun t => sumRange
        (fun j => imatGet A i t * (imatGet B t j * (v[j]?).getD 0)) v.length)
        (imatRows B) := by
      apply sumRange_congr_lt
      intro t _
      rw [sumRange_smul_left]
    _ = sumRange (fun j => sumRange
        (fun t => (imatGet A i t * imatGet B t j) * (v[j]?).getD 0)
        (imatCols A)) v.length := by
      rw [sumRange_swap, hab]
      simp only [Int.mul_assoc]
    _ = _ := by
      apply sumRange_congr_lt
      intro j hj
      rw [sumRange_smul_right, imatMul_entry_aux A B i j hiA (by omega)]

private theorem mul_zero (A : IMat) (n : Nat) :
    matVecMul A (zeroVec n) = zeroVec (imatRows A) := by
  apply ext (by simp [zeroVec_length_aux])
  intro i hi
  rw [entry _ _ _ (by simpa using hi), zero_get]
  apply sumRange_eq_zero_of_eq_zero
  intro j _
  simp [zero_get]

private theorem eye_mul (d : Int) (n : Nat) (v : List Int) (hv : v.length = n) :
    matVecMul (imatSmul d (imatEye n)) v = vecSmul d v := by
  apply ext
  · simp [imatRows, imatSmul, imatEye, vecSmul_length_aux, hv]
  intro i hi
  have hin : i < n := by
    simpa [imatRows, imatSmul, imatEye] using hi
  rw [entry _ _ _ (by simpa [imatRows, imatSmul, imatEye] using hin), smul_get]
  simp only [imatSmul_entry_aux]
  simp only [Int.mul_assoc]
  rw [sumRange_smul_left]
  congr 1
  rw [hv]
  calc
    _ = sumRange (fun j => (v[j]?).getD 0 *
        (if j == i then (1 : Int) else 0)) n := by
      apply sumRange_congr_lt
      intro j hj
      rw [imatEye_entry_aux n i j hin hj]
      simp only [BEq.comm (a := i) (b := j), Int.mul_comm]
    _ = _ := sumRange_eye _ _ _ hin

private theorem mul_sub_smul (A : IMat) (d : Int) (v u : List Int)
    (hu : u.length = v.length) :
    matVecMul A (vecSub (vecSmul d v) u) =
      vecSub (vecSmul d (matVecMul A v)) (matVecMul A u) := by
  apply ext
  · simp [vecSub_length_aux, vecSmul_length_aux]
  intro i hi
  have hiA : i < imatRows A := by simpa using hi
  rw [entry _ _ _ hiA]
  have hri : i < (vecSmul d (matVecMul A v)).length := by
    simpa [vecSmul_length_aux] using hiA
  rw [vecSub_entry_aux _ _ _ hri, Option.getD_some, smul_get,
    entry _ _ _ hiA, entry _ _ _ hiA, vecSub_length_aux, vecSmul_length_aux]
  rw [← sumRange_smul_left, ← hu, ← sumRange_sub_aux]
  apply sumRange_congr_lt
  intro j hj
  rw [vecSub_entry_aux _ _ _ (by simp [vecSmul_length_aux]; omega),
    Option.getD_some, smul_get]
  rw [Int.mul_sub]
  congr 1
  ac_rfl

private theorem zero_matrix_mul (m n : Nat) (v : List Int) :
    matVecMul (imatZero m n) v = zeroVec m := by
  apply ext (by simp [matVecMul, imatRows, imatZero, zeroVec])
  intro i hi
  have him : i < m := by simpa [matVecMul, imatRows, imatZero] using hi
  rw [entry _ _ _ (by simpa [imatRows, imatZero] using him), zero_get]
  apply sumRange_eq_zero_of_eq_zero
  intro j _
  simp [imatGet, imatZero, List.getElem?_map, List.getElem?_range him]
  cases (List.range n)[j]? <;> simp

private theorem sub_self (v : List Int) : vecSub v v = zeroVec v.length := by
  apply ext (by simp [vecSub_length_aux, zeroVec_length_aux])
  intro i hi
  have hiv : i < v.length := by simpa [vecSub_length_aux] using hi
  simp [vecSub_entry_aux v v i hiv, zero_get]

private theorem sub_eq_zero (u v : List Int) (hv : v.length = u.length)
    (h : vecSub u v = zeroVec u.length) : u = v := by
  apply ext hv.symm
  intro i hi
  have hh := congrArg (fun l : List Int => (l[i]?).getD 0) h
  rw [vecSub_entry_aux _ _ _ hi, Option.getD_some, zero_get] at hh
  omega

private theorem rowsOf_kernel (M : IMat) (S : List Nat) (v : List Int)
    (hS : ∀ i ∈ S, i < imatRows M)
    (h : matVecMul M v = zeroVec (imatRows M)) :
    matVecMul (imatRowsOf M S) v = zeroVec S.length := by
  apply ext (by simp [matVecMul, imatRowsOf, imatRows, zeroVec])
  intro i hi
  have hiS : i < S.length := by simpa [matVecMul, imatRowsOf, imatRows] using hi
  have hsi := hS S[i] (List.getElem_mem hiS)
  have hh := congrArg (fun l : List Int => (l[S[i]]?).getD 0) h
  rw [entry _ _ _ hsi, zero_get] at hh
  rw [entry _ _ _ (by simpa [imatRowsOf, imatRows] using hiS), zero_get]
  apply Eq.trans (b := sumRange (fun j => imatGet M S[i] j * (v[j]?).getD 0) v.length) ?_ hh
  apply sumRange_congr_lt
  intro j _
  rw [imatGet_rowGet_aux M]
  simp [imatRowsOf, imatGet, List.getElem?_map, List.getElem?_eq_getElem hiS]

private theorem append_mul (A B : IMat) (v : List Int) :
    matVecMul (A ++ B) v = matVecMul A v ++ matVecMul B v := by
  simp only [matVecMul, imatRows, List.length_append, List.range_add, List.map_append,
    List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    apply sumRange_congr_lt
    intro j _
    simp [imatGet, List.getElem?_append_left (List.mem_range.mp hi)]
  · apply List.map_congr_left
    intro i hi
    apply sumRange_congr_lt
    intro j _
    simp [imatGet, List.getElem?_append_right, Nat.add_comm]

/-- Existing `qLeftInv`, `gselKernel`, and the `Kg Gsel` check give full
    kernel spanning. No spanning or rank premise is assumed. -/
theorem kernel_span_of_qLeftInv
    (M Gsel Kg Y : IMat) (S : List Nat) (n k : Nat) (dg dY : Int)
    (hk : 0 < k)
    (hMc : imatCols M = n) (hMr : imatRows M = n)
    (hGr : imatRows Gsel = n) (hGc : imatCols Gsel = k)
    (hKr : imatRows Kg = k) (hKc : imatCols Kg = n)
    (hQc : imatCols (imatRowsOf M S ++ Kg) = n)
    (hYc : imatCols Y = imatRows (imatRowsOf M S ++ Kg))
    (hS : ∀ i ∈ S, i < n)
    (hdg : dg ≠ 0) (hdY : dY ≠ 0)
    (hMG : imatMul M Gsel = imatZero n k)
    (hKG : imatMul Kg Gsel = imatSmul dg (imatEye k))
    (hYQ : imatMul Y (imatRowsOf M S ++ Kg) = imatSmul dY (imatEye n))
    (v : List Int) (hv : v.length = n)
    (hMv : matVecMul M v = zeroVec n) :
    ∃ cs d, d ≠ 0 ∧ cs.length = k ∧
      vecSmul d v = lincomb cs (imatTranspose Gsel) := by
  let c := matVecMul Kg v
  let u := matVecMul Gsel c
  let z := vecSub (vecSmul dg v) u
  have hc : c.length = k := by simp [c, hKr]
  have hu : u.length = v.length := by simp [u, hGr, hv]
  have hz : z.length = n := by simp [z, vecSub_length_aux, vecSmul_length_aux, hv]
  have hMu : matVecMul M u = zeroVec n := by
    rw [show u = matVecMul Gsel c from rfl, mul_assoc M Gsel c (by omega) (by omega),
      hMG, zero_matrix_mul]
  have hKu : matVecMul Kg u = vecSmul dg c := by
    rw [show u = matVecMul Gsel c from rfl, mul_assoc Kg Gsel c (by omega) (by omega),
      hKG, eye_mul dg k c hc]
  have hMz : matVecMul M z = zeroVec n := by
    rw [show z = vecSub (vecSmul dg v) u from rfl, mul_sub_smul _ _ _ _ hu,
      hMv, hMu, vecSmul_zeroVec_aux, sub_self, zeroVec_length_aux]
  have hKz : matVecMul Kg z = zeroVec k := by
    rw [show z = vecSub (vecSmul dg v) u from rfl, mul_sub_smul _ _ _ _ hu,
      hKu, show matVecMul Kg v = c from rfl, sub_self, vecSmul_length_aux, hc]
  have hQz : matVecMul (imatRowsOf M S ++ Kg) z =
      zeroVec (imatRows (imatRowsOf M S ++ Kg)) := by
    rw [append_mul, rowsOf_kernel M S z (by simpa [hMr] using hS) (by simpa [hMr] using hMz), hKz]
    have hr : (zeroVec S.length ++ zeroVec k) = zeroVec (S.length + k) := by
      induction S.length with
      | zero => simp [zeroVec]
      | succ m ih => simpa [zeroVec, List.replicate_succ, Nat.succ_add] using congrArg (List.cons 0) ih
    simpa [imatRows, imatRowsOf, ← hKr] using hr
  have hz0 : z = zeroVec n := by
    have hh := mul_assoc Y (imatRowsOf M S ++ Kg) z hYc (by omega)
    rw [hQz, mul_zero, hYQ, eye_mul dY n z hz] at hh
    have hy : imatRows Y = n := by
      have he := congrArg imatRows hYQ
      simpa [imatRows, imatMul_rows_aux, imatSmul, imatEye] using he
    simpa [hz] using vecSmul_eq_zeroVec_aux dY hdY z (by simpa [hz, hy] using hh.symm)
  have hvu : vecSmul dg v = u :=
    sub_eq_zero _ _ (by simpa [vecSmul_length_aux] using hu) (by simpa [z, vecSmul_length_aux, hv] using hz0)
  refine ⟨c, dg, hdg, hc, hvu.trans ?_⟩
  have htrows : imatRows (imatTranspose Gsel) = k := by simp [imatTranspose, imatRows, hGc]
  have htcols : imatCols (imatTranspose Gsel) = n := by
    unfold imatCols
    change ((((List.range (imatCols Gsel)).map fun j =>
      (List.range (imatRows Gsel)).map fun i => imatGet Gsel i j)[0]?).getD []).length = n
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp [hGr]
  apply ext
  · rw [show u = matVecMul Gsel c from rfl, matVecMul_length, hGr,
      lincomb_length_aux c (imatTranspose Gsel) (by omega), htcols]
  intro i hi
  have hin : i < n := by simpa [u, hGr] using hi
  rw [show u = matVecMul Gsel c from rfl, entry _ _ _ (by omega),
    lincomb_entry_aux c _ i (by omega), Option.getD_some]
  apply sumRange_congr_lt
  intro j hj
  have hjk : j < k := by omega
  rw [← imatGet_rowGet_aux]
  have he : imatGet (imatTranspose Gsel) j i = imatGet Gsel i j := by
    simp [imatTranspose, imatGet, List.getElem?_map,
      List.getElem?_range (show j < imatCols Gsel by omega),
      List.getElem?_range (show i < imatRows Gsel by omega)]
  rw [he, Int.mul_comm]

end KernelSpan
