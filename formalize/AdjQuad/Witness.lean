import AdjQuad.Poly

abbrev IMat := List (List Int)

def imatGet (M : IMat) (i j : Nat) : Int :=
  ((M[i]?).bind (·[j]?)).getD 0

def imatRows (M : IMat) : Nat := M.length
def imatCols (M : IMat) : Nat := ((M[0]?).getD []).length

def imatMul (A B : IMat) : IMat :=
  let n := imatCols A
  let p := imatCols B
  (List.range (imatRows A)).map fun i =>
    (List.range p).map fun j =>
      (List.range n).foldl (fun acc k => acc + imatGet A i k * imatGet B k j) 0

def imatEye (n : Nat) : IMat :=
  (List.range n).map fun i =>
    (List.range n).map fun j => if i == j then 1 else 0

def imatSmul (d : Int) (M : IMat) : IMat :=
  M.map (fun row => row.map (fun x => d * x))

def imatSub (A B : IMat) : IMat :=
  (List.range (imatRows A)).map fun i =>
    (List.range (imatCols A)).map fun j => imatGet A i j - imatGet B i j

theorem imatSub_small :
    imatSub [[1, 2], [3, 4]] [[5, 6], [7, 8]] = [[-4, -4], [-4, -4]] := by decide

def imatZero (m n : Nat) : IMat :=
  (List.range m).map fun _ => (List.range n).map fun _ => 0

def imatRowsOf (M : IMat) (S : List Nat) : IMat :=
  S.map fun i => ((M[i]?).getD [])

def imatTranspose (M : IMat) : IMat :=
  (List.range (imatCols M)).map fun j =>
    (List.range (imatRows M)).map fun i => imatGet M i j

def vecMatMul (c : List Int) (A : IMat) : List Int :=
  (List.range (imatCols A)).map fun j =>
    (List.range c.length).foldl (fun acc i => acc + (c[i]?).getD 0 * imatGet A i j) 0

def zeroVec (n : Nat) : List Int := List.replicate n 0

def vecSmul (d : Int) (v : List Int) : List Int := v.map (fun x => d * x)

def polySmulInt (d : Int) (p : Poly) : Poly :=
  p.map (fun m => ((d : Rat) * m.1, m.2))

def lincomb (coeffs : List Int) (vecs : List (List Int)) : List Int :=
  match vecs with
  | [] => zeroVec coeffs.length  -- unused shape; length fixed by caller lemmas
  | v0 :: _ =>
    (List.range v0.length).map fun j =>
      (List.range coeffs.length).foldl
        (fun acc i => acc + (coeffs[i]?).getD 0 * ((((vecs[i]?).getD [])[j]?).getD 0)) 0

def independent (vecs : List (List Int)) : Prop :=
  ∀ coeffs, coeffs.length = vecs.length →
    lincomb coeffs vecs = zeroVec (((vecs[0]?).getD []).length) →
    coeffs = zeroVec vecs.length

theorem imatMul_eye_small :
    imatMul [[1, 2], [3, 4]] (imatEye 2) = [[1, 2], [3, 4]] := by decide

theorem imatEye_zero : imatEye 0 = [] := by decide

theorem imatRowsOf_single : imatRowsOf [[1, 2], [3, 4]] [1] = [[3, 4]] := by decide

theorem imatTranspose_small :
    imatTranspose [[1, 2, 3], [4, 5, 6]] = [[1, 4], [2, 5], [3, 6]] := by decide

theorem vecSmul_two : vecSmul 2 [1, -3] = [2, -6] := by decide

theorem polySmulInt_one (p : Poly) : polySmulInt 1 p = p := by
  simp [polySmulInt]

-- Independence and row-span lemmas.

def sumRange (f : Nat → Int) (n : Nat) : Int :=
  (List.range n).foldl (fun acc i => acc + f i) 0

theorem sumRange_succ (f : Nat → Int) (n : Nat) :
    sumRange f (n+1) = sumRange f n + f n := by
  unfold sumRange
  rw [List.range_succ, List.foldl_append]
  simp

theorem sumRange_add (f g : Nat → Int) (n : Nat) :
    sumRange (fun i => f i + g i) n = sumRange f n + sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih]
    ac_rfl

theorem sumRange_smul_left (a : Int) (f : Nat → Int) (n : Nat) :
    sumRange (fun i => a * f i) n = a * sumRange f n := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih, Int.mul_add]

theorem sumRange_smul_right (f : Nat → Int) (a : Int) (n : Nat) :
    sumRange (fun i => f i * a) n = (sumRange f n) * a := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih, Int.add_mul]

theorem sumRange_congr_lt (f g : Nat → Int) (n : Nat) (h : ∀ i, i < n → f i = g i) :
    sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ]
    have h1 : sumRange f n = sumRange g n := by
      apply ih
      intro i hi
      exact h i (by omega)
    have h2 : f n = g n := h n (by omega)
    rw [h1, h2]

theorem sumRange_swap (f : Nat → Nat → Int) (n m : Nat) :
    sumRange (fun i => sumRange (fun j => f i j) m) n =
    sumRange (fun j => sumRange (fun i => f i j) n) m := by
  induction n with
  | zero =>
    have h0 : (fun j => sumRange (fun i => f i j) 0) = (fun _ => (0 : Int)) := by
      funext j
      rfl
    calc sumRange (fun i => sumRange (fun j => f i j) m) 0
        = 0 := rfl
      _ = sumRange (fun _ => (0 : Int)) m := by
        have h : sumRange (fun _ => (0 : Int)) m = 0 := by
          induction m with
          | zero => rfl
          | succ m ihm => rw [sumRange_succ, ihm, Int.add_zero]
        rw [h]
      _ = sumRange (fun j => sumRange (fun i => f i j) 0) m := by rw [h0]
  | succ n ih =>
    rw [sumRange_succ]
    have hexpand : (fun j => sumRange (fun i => f i j) (n+1)) =
        (fun j => sumRange (fun i => f i j) n + f n j) := by
      funext j
      exact sumRange_succ _ n
    rw [hexpand, sumRange_add, ih]

theorem sumRange_eq_zero_of_eq_zero (f : Nat → Int) (n : Nat)
    (h : ∀ i, i < n → f i = 0) : sumRange f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ]
    have h1 : sumRange f n = 0 := by
      apply ih
      intro i hi
      exact h i (by omega)
    have h2 : f n = 0 := h n (by omega)
    rw [h1, h2, Int.add_zero]

theorem sumRange_eye (f : Nat → Int) (n : Nat) (j : Nat) (hj : j < n) :
    sumRange (fun i => f i * (if i == j then (1 : Int) else 0)) n = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumRange_succ]
    by_cases hjn : j = n
    · have hzero : sumRange (fun i => f i * (if i == j then (1 : Int) else 0)) n = 0 := by
        apply sumRange_eq_zero_of_eq_zero
        intro i hi
        have hne : i ≠ j := by omega
        have hbeq : (i == j) = false := by simp [hne]
        rw [hbeq]
        simp
      rw [hzero]
      have hbeq2 : (n == j) = true := by simp [Eq.symm hjn]
      have hterm : f n * (if n == j then (1 : Int) else 0) = f n := by
        rw [hbeq2]
        simp
      rw [hterm]
      have hfj : f n = f j := by rw [← hjn]
      rw [hfj]
      simp
    · have hlt : j < n := by omega
      have ih' := ih hlt
      have hne : n ≠ j := by
        intro h
        exact hjn (Eq.symm h)
      have hbeq : (n == j) = false := by simp [hne]
      have hterm : f n * (if n == j then (1 : Int) else 0) = 0 := by
        rw [hbeq]
        simp
      rw [hterm, ih']
      simp

theorem vecMatMul_length_aux (c : List Int) (A : IMat) :
    (vecMatMul c A).length = imatCols A := by
  unfold vecMatMul imatCols
  rw [List.length_map, List.length_range]

theorem vecMatMul_entry_aux (c : List Int) (A : IMat) (j : Nat) (hj : j < imatCols A) :
    (vecMatMul c A)[j]? = some (sumRange (fun i => (c[i]?).getD 0 * imatGet A i j) c.length) := by
  unfold vecMatMul sumRange
  rw [List.getElem?_map]
  have hrange : (List.range (imatCols A))[j]? = some j := List.getElem?_range hj
  rw [hrange]
  simp

theorem imatMul_rows_aux (A B : IMat) : (imatMul A B).length = imatRows A := by
  unfold imatMul imatRows
  simp

theorem imatMul_cols_aux (A B : IMat) (c : List Int)
    (hc : c.length = imatRows A) (hab : imatCols A = imatRows B) :
    imatCols (imatMul A B) = imatCols B := by
  cases A with
  | nil =>
    simp [imatRows] at hc
    simp [imatCols, imatRows] at hab
    simp [imatMul, imatRows]
    match B with
    | [] => simp [imatCols]
    | b0 :: rest => simp_all
  | cons a0 rest =>
    simp only [imatMul, imatRows, imatCols]
    have h0lt : 0 < (a0 :: rest).length := by simp
    have hrange : (List.range (a0 :: rest).length)[0]? = some 0 :=
      List.getElem?_range h0lt
    rw [List.getElem?_map, hrange]
    simp [List.length_map, List.length_range]

theorem imatMul_entry_aux (A B : IMat) (i j : Nat)
    (hi : i < imatRows A) (hj : j < imatCols B) :
    imatGet (imatMul A B) i j =
      sumRange (fun k => imatGet A i k * imatGet B k j) (imatCols A) := by
  simp only [imatRows] at hi
  simp only [imatCols] at hj
  simp only [imatGet, imatMul, imatRows, imatCols]
  rw [List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.bind_some]
  rw [List.getElem?_map, List.getElem?_range hj]
  simp [sumRange]

theorem imatEye_rows_aux (n : Nat) : (imatEye n).length = n := by
  unfold imatEye
  rw [List.length_map, List.length_range]

theorem imatEye_cols_aux (r : Nat) : imatCols (imatEye r) = r := by
  cases r with
  | zero => simp [imatEye, imatCols]
  | succ n =>
    unfold imatCols imatEye
    have h0lt : 0 < n + 1 := by omega
    have hrange : (List.range (n+1))[0]? = some 0 := List.getElem?_range h0lt
    rw [List.getElem?_map, hrange]
    simp [List.length_map, List.length_range]

theorem imatEye_entry_aux (r i j : Nat) (hi : i < r) (hj : j < r) :
    imatGet (imatEye r) i j = (if i == j then (1 : Int) else 0) := by
  simp only [imatEye, imatGet]
  rw [List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.bind_some]
  rw [List.getElem?_map, List.getElem?_range hj]
  simp

theorem imatSmul_rows_aux (d : Int) (M : IMat) : imatRows (imatSmul d M) = imatRows M := by
  unfold imatSmul imatRows
  rw [List.length_map]

theorem imatSmul_cols_aux (d : Int) (M : IMat) : imatCols (imatSmul d M) = imatCols M := by
  unfold imatSmul imatCols
  rw [List.getElem?_map]
  cases M[0]? with
  | none => simp
  | some row => simp

theorem imatSmul_entry_aux (d : Int) (M : IMat) (i j : Nat) :
    imatGet (imatSmul d M) i j = d * imatGet M i j := by
  unfold imatSmul imatGet
  rw [List.getElem?_map]
  cases hMi : M[i]? with
  | none =>
    simp only [Option.map_none, Option.bind_none, Option.getD_none, Int.mul_zero]
  | some row =>
    simp only [Option.map_some, Option.bind_some]
    rw [List.getElem?_map]
    cases hRj : row[j]? with
    | none =>
      simp only [Option.map_none, Option.getD_none, Int.mul_zero]
    | some x =>
      simp only [Option.map_some, Option.getD_some]

theorem imatGet_rowGet_aux (S : IMat) (i j : Nat) :
    imatGet S i j = ((((S[i]?).getD [])[j]?).getD 0) := by
  unfold imatGet
  cases hSi : S[i]? with
  | none =>
    simp only [Option.bind_none, Option.getD_none, Option.getD_none] at ⊢
    rfl
  | some row =>
    simp only [Option.bind_some, Option.getD_some, Option.getD_some]

theorem zeroVec_length_aux (n : Nat) : (zeroVec n).length = n := by
  unfold zeroVec
  rw [List.length_replicate]

theorem zeroVec_entry_aux (n j : Nat) (hj : j < n) : (zeroVec n)[j]? = some (0 : Int) := by
  unfold zeroVec
  rw [List.getElem?_replicate]
  simp [hj]

theorem vecSmul_length_aux (d : Int) (v : List Int) : (vecSmul d v).length = v.length := by
  unfold vecSmul
  rw [List.length_map]

theorem vecSmul_entry_aux (d : Int) (v : List Int) (j : Nat) (hj : j < v.length) :
    (vecSmul d v)[j]? = some (d * ((v[j]?).getD 0)) := by
  unfold vecSmul
  rw [List.getElem?_map]
  have h : v[j]? = some ((v[j]?).getD 0) := by
    cases hv : v[j]? with
    | none =>
      have hlen : ¬ j < v.length := by
        intro hlt
        have heq := List.getElem?_eq_getElem hlt
        rw [hv] at heq
        simp at heq
      omega
    | some x => simp
  rw [h]
  simp

theorem lincomb_length_aux (coeffs : List Int) (S : IMat)
    (h : coeffs.length = imatRows S) : (lincomb coeffs S).length = imatCols S := by
  cases S with
  | nil =>
    simp [imatRows, lincomb, zeroVec, imatCols] at h ⊢
    exact h
  | cons v0 rest =>
    simp [lincomb, imatCols]

theorem lincomb_entry_aux (coeffs : List Int) (S : IMat) (j : Nat) (hj : j < imatCols S) :
    (lincomb coeffs S)[j]? =
      some (sumRange (fun i => (coeffs[i]?).getD 0 * ((((S[i]?).getD [])[j]?).getD 0)) coeffs.length) := by
  cases S with
  | nil =>
    simp [imatCols] at hj
  | cons v0 rest =>
    simp [imatCols] at hj
    simp only [lincomb]
    rw [List.getElem?_map, List.getElem?_range hj]
    simp only [Option.map_some, sumRange]

theorem vecMatMul_assoc_entry_aux (c : List Int) (A B : IMat)
    (hc : c.length = imatRows A) (hab : imatCols A = imatRows B)
    (j : Nat) (hj : j < imatCols B) :
    sumRange (fun k => ((vecMatMul c A)[k]?).getD 0 * imatGet B k j) (imatCols A) =
    sumRange (fun i => (c[i]?).getD 0 * imatGet (imatMul A B) i j) c.length := by
  have h1 : ∀ k, k < imatCols A →
      ((vecMatMul c A)[k]?).getD 0 * imatGet B k j =
      (sumRange (fun i => (c[i]?).getD 0 * imatGet A i k) c.length) * imatGet B k j := by
    intro k hk
    have hentry := vecMatMul_entry_aux c A k hk
    have hget : ((vecMatMul c A)[k]?).getD 0 =
        sumRange (fun i => (c[i]?).getD 0 * imatGet A i k) c.length := by
      rw [hentry]
      simp
    rw [hget]
  rw [sumRange_congr_lt _ _ _ h1]
  have h2 : ∀ k, k < imatCols A →
      (sumRange (fun i => (c[i]?).getD 0 * imatGet A i k) c.length) * imatGet B k j =
      sumRange (fun i => ((c[i]?).getD 0 * imatGet A i k) * imatGet B k j) c.length := by
    intro k hk
    rw [sumRange_smul_right]
  rw [sumRange_congr_lt _ _ _ h2]
  have hswap := sumRange_swap (fun k i => ((c[i]?).getD 0 * imatGet A i k) * imatGet B k j) (imatCols A) c.length
  rw [hswap]
  have h3 : ∀ i, i < c.length →
      sumRange (fun k => ((c[i]?).getD 0 * imatGet A i k) * imatGet B k j) (imatCols A) =
      sumRange (fun k => (c[i]?).getD 0 * (imatGet A i k * imatGet B k j)) (imatCols A) := by
    intro i hi
    apply sumRange_congr_lt
    intro k hk
    rw [Int.mul_assoc]
  rw [sumRange_congr_lt _ _ _ h3]
  have h4 : ∀ i, i < c.length →
      sumRange (fun k => (c[i]?).getD 0 * (imatGet A i k * imatGet B k j)) (imatCols A) =
      (c[i]?).getD 0 * sumRange (fun k => imatGet A i k * imatGet B k j) (imatCols A) := by
    intro i hi
    rw [sumRange_smul_left]
  rw [sumRange_congr_lt _ _ _ h4]
  have h5 : ∀ i, i < c.length →
      (c[i]?).getD 0 * sumRange (fun k => imatGet A i k * imatGet B k j) (imatCols A) =
      (c[i]?).getD 0 * imatGet (imatMul A B) i j := by
    intro i hi
    have hiA : i < imatRows A := by omega
    have hmul := imatMul_entry_aux A B i j hiA hj
    rw [hmul]
  rw [sumRange_congr_lt _ _ _ h5]

instance : HSMul Int (List Int) (List Int) where
  hSMul := vecSmul

theorem vecMatMul_assoc (c : List Int) (A B : IMat)
    (hc : c.length = imatRows A) (hab : imatCols A = imatRows B) :
    vecMatMul (vecMatMul c A) B = vecMatMul c (imatMul A B) := by
  have hcols : imatCols (imatMul A B) = imatCols B := imatMul_cols_aux A B c hc hab
  have hlenL : (vecMatMul (vecMatMul c A) B).length = imatCols B := vecMatMul_length_aux _ _
  have hlenR : (vecMatMul c (imatMul A B)).length = imatCols B := by
    rw [vecMatMul_length_aux, hcols]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < imatCols B
  · have hjR : j < imatCols (imatMul A B) := by omega
    have hL := vecMatMul_entry_aux (vecMatMul c A) B j hj
    have hR := vecMatMul_entry_aux c (imatMul A B) j hjR
    have hlenC : (vecMatMul c A).length = imatCols A := vecMatMul_length_aux c A
    rw [hlenC] at hL
    have hentry := vecMatMul_assoc_entry_aux c A B hc hab j hj
    rw [hL, hR, hentry]
  · have hleL : (vecMatMul (vecMatMul c A) B).length ≤ j := by omega
    have hleR : (vecMatMul c (imatMul A B)).length ≤ j := by omega
    have hnoneL : (vecMatMul (vecMatMul c A) B)[j]? = none :=
      List.getElem?_eq_none hleL
    have hnoneR : (vecMatMul c (imatMul A B))[j]? = none :=
      List.getElem?_eq_none hleR
    rw [hnoneL, hnoneR]

theorem vecMatMul_zeroVec_aux (n : Nat) (T : IMat) :
    vecMatMul (zeroVec n) T = zeroVec (imatCols T) := by
  have hlenL : (vecMatMul (zeroVec n) T).length = imatCols T := vecMatMul_length_aux _ _
  have hlenR : (zeroVec (imatCols T)).length = imatCols T := zeroVec_length_aux _
  apply List.ext_getElem?
  intro j
  by_cases hj : j < imatCols T
  · have hL := vecMatMul_entry_aux (zeroVec n) T j hj
    have hR := zeroVec_entry_aux (imatCols T) j hj
    rw [hL, hR]
    have hzero : sumRange (fun i => ((zeroVec n)[i]?).getD 0 * imatGet T i j)
        (zeroVec n).length = 0 := by
      apply sumRange_eq_zero_of_eq_zero
      intro i hi
      have hlenZ : (zeroVec n).length = n := zeroVec_length_aux n
      have hi_n : i < n := by omega
      have hentry := zeroVec_entry_aux n i hi_n
      have hget : ((zeroVec n)[i]?).getD 0 = 0 := by
        rw [hentry]
        simp
      rw [hget]
      simp
    rw [hzero]
  · have hleL : (vecMatMul (zeroVec n) T).length ≤ j := by omega
    have hleR : (zeroVec (imatCols T)).length ≤ j := by omega
    have hnoneL : (vecMatMul (zeroVec n) T)[j]? = none :=
      List.getElem?_eq_none hleL
    have hnoneR : (zeroVec (imatCols T))[j]? = none :=
      List.getElem?_eq_none hleR
    rw [hnoneL, hnoneR]

theorem vecMatMul_smul_eye_aux (c : List Int) (d : Int) (r : Nat)
    (hc : c.length = r) :
    vecMatMul c (imatSmul d (imatEye r)) = vecSmul d c := by
  have hcolsEye : imatCols (imatEye r) = r := imatEye_cols_aux r
  have hcolsSmul : imatCols (imatSmul d (imatEye r)) = r := by
    rw [imatSmul_cols_aux, hcolsEye]
  have hlenL : (vecMatMul c (imatSmul d (imatEye r))).length = r := by
    rw [vecMatMul_length_aux, hcolsSmul]
  have hlenR : (vecSmul d c).length = r := by
    rw [vecSmul_length_aux, hc]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < r
  · have hjSmul : j < imatCols (imatSmul d (imatEye r)) := by omega
    have hjC : j < c.length := by omega
    have hL := vecMatMul_entry_aux c (imatSmul d (imatEye r)) j hjSmul
    have hR := vecSmul_entry_aux d c j hjC
    rw [hL, hR]
    have h1 : ∀ i, i < c.length →
        (c[i]?).getD 0 * imatGet (imatSmul d (imatEye r)) i j =
        d * ((c[i]?).getD 0 * (if i == j then (1 : Int) else 0)) := by
      intro i hi
      have hiR : i < r := by omega
      have hsmul := imatSmul_entry_aux d (imatEye r) i j
      have heye := imatEye_entry_aux r i j hiR hj
      rw [hsmul, heye]
      ac_rfl
    rw [sumRange_congr_lt _ _ _ h1, sumRange_smul_left]
    have heyeSum : sumRange (fun i => (c[i]?).getD 0 * (if i == j then (1 : Int) else 0)) c.length =
        (c[j]?).getD 0 := by
      have hrw : (fun i => (c[i]?).getD 0 * (if i == j then (1 : Int) else 0)) =
          (fun i => (fun k => (c[k]?).getD 0) i * (if i == j then (1 : Int) else 0)) := rfl
      rw [hrw]
      have hcast : c.length = r := hc
      rw [hcast] at ⊢
      -- sumRange_eye expects f : Nat → Int, n, j with j < n
      have h := sumRange_eye (fun k => (c[k]?).getD 0) r j hj
      exact h
    rw [heyeSum]
  · have hleL : (vecMatMul c (imatSmul d (imatEye r))).length ≤ j := by omega
    have hleR : (vecSmul d c).length ≤ j := by omega
    rw [List.getElem?_eq_none hleL, List.getElem?_eq_none hleR]

theorem rows_independent_of_right_inv (A T : IMat) (d1 : Int) (r : Nat)
    (hd : d1 ≠ 0)
    (hAT : imatMul A T = imatSmul d1 (imatEye r))
    (hr : imatRows A = r) (hcA : imatCols A = imatRows T) :
    ∀ c : List Int, c.length = r → vecMatMul c A = zeroVec (imatCols A) →
      c = zeroVec r := by
  intro c hc hzero
  have hcA' : c.length = imatRows A := by omega
  have hassoc := vecMatMul_assoc c A T hcA' hcA
  have hleft : vecMatMul (vecMatMul c A) T = zeroVec (imatCols T) := by
    rw [hzero]
    exact vecMatMul_zeroVec_aux (imatCols A) T
  rw [hleft] at hassoc
  have hATc : vecMatMul c (imatMul A T) = vecMatMul c (imatSmul d1 (imatEye r)) := by
    rw [hAT]
  rw [hATc] at hassoc
  have hsmul : vecMatMul c (imatSmul d1 (imatEye r)) = vecSmul d1 c :=
    vecMatMul_smul_eye_aux c d1 r hc
  rw [hsmul] at hassoc
  -- hassoc : zeroVec (imatCols T) = vecSmul d1 c, need symmetric
  have hcolsT : imatCols T = r := by
    have h1 : imatCols (imatMul A T) = imatCols T := imatMul_cols_aux A T c hcA' hcA
    have h2 : imatCols (imatSmul d1 (imatEye r)) = r := by
      rw [imatSmul_cols_aux, imatEye_cols_aux]
    have h3 : imatCols (imatMul A T) = imatCols (imatSmul d1 (imatEye r)) := by
      rw [hAT]
    omega
  have hsmulZero : vecSmul d1 c = zeroVec r := by
    have hsym : vecSmul d1 c = zeroVec (imatCols T) := hassoc.symm
    rw [hcolsT] at hsym
    exact hsym
  -- cancel d1 entry-wise
  have hlenC : c.length = r := hc
  have hlenZ : (zeroVec r).length = r := zeroVec_length_aux r
  apply List.ext_getElem?
  intro j
  by_cases hj : j < r
  · have hjC : j < c.length := by omega
    have hjZ : j < (zeroVec r).length := by omega
    have hS := vecSmul_entry_aux d1 c j hjC
    have hZ := zeroVec_entry_aux r j hj
    have heq : (vecSmul d1 c)[j]? = (zeroVec r)[j]? := by
      rw [hsmulZero]
    rw [hS, hZ] at heq
    have hmul : d1 * ((c[j]?).getD 0) = 0 := Option.some_inj.mp heq
    have hczero : ((c[j]?).getD 0) = 0 := by
      have hdisj := (Int.mul_eq_zero.mp hmul)
      rcases hdisj with h1 | h2
      · exact False.elim (hd h1)
      · exact h2
    -- c[j]? = some 0, zeroVec entry = some 0
    have hcSome : c[j]? = some (((c[j]?).getD 0)) := by
      cases hv : c[j]? with
      | none =>
        have hlen : ¬ j < c.length := by
          intro hlt
          have heq2 := List.getElem?_eq_getElem hlt
          rw [hv] at heq2
          simp at heq2
        omega
      | some x => simp
    rw [hcSome, hczero]
    have hZsome : (zeroVec r)[j]? = some (0 : Int) := hZ
    rw [hZsome]
  · have hleC : c.length ≤ j := by omega
    have hleZ : (zeroVec r).length ≤ j := by omega
    rw [List.getElem?_eq_none hleC, List.getElem?_eq_none hleZ]

theorem imatMul_row_length_aux (C S : IMat) (i : Nat) (hi : i < imatRows C) :
    (((imatMul C S)[i]?).getD []).length = imatCols S := by
  simp only [imatRows] at hi
  simp only [imatMul, imatRows, imatCols]
  rw [List.getElem?_map, List.getElem?_range hi]
  simp [List.length_map, List.length_range]

theorem imatSmul_row_length_aux (d : Int) (M : IMat) (i : Nat) (hi : i < imatRows M) :
    (((imatSmul d M)[i]?).getD []).length = (((M[i]?).getD []).length) := by
  simp only [imatRows] at hi
  unfold imatSmul
  rw [List.getElem?_map]
  have hsome : M[i]? = some ((M[i]?).getD []) := by
    cases hv : M[i]? with
    | none =>
      have hlen : ¬ i < M.length := by
        intro hlt
        have heq := List.getElem?_eq_getElem hlt
        rw [hv] at heq
        simp at heq
      omega
    | some row => simp
  rw [hsome]
  simp [List.length_map]

theorem spanning_row_length_aux (M S C : IMat) (d4 : Int)
    (hC : imatMul C S = imatSmul d4 M) (i : Nat) (hi : i < imatRows M) :
    (((M[i]?).getD []).length) = imatCols S := by
  have hrowsC : imatRows C = imatRows M := by
    have h1 : (imatMul C S).length = imatRows C := imatMul_rows_aux C S
    have h2 : (imatSmul d4 M).length = imatRows M := by
      exact imatSmul_rows_aux d4 M
    have h3 : (imatMul C S).length = (imatSmul d4 M).length := by
      rw [hC]
    simp only [imatRows] at h1 h2 h3 ⊢
    omega
  have hiC : i < imatRows C := by omega
  have hmulLen := imatMul_row_length_aux C S i hiC
  have hsmulLen := imatSmul_row_length_aux d4 M i hi
  have hget : (imatMul C S)[i]? = (imatSmul d4 M)[i]? := by
    rw [hC]
  rw [hget] at hmulLen
  omega

theorem sumRange_if_min_aux (f : Nat → Int) (n m : Nat) :
    sumRange (fun k => if k < m then f k else 0) n = sumRange f (min n m) := by
  induction n with
  | zero => simp [sumRange, Nat.min_def]
  | succ n ih =>
    rw [sumRange_succ]
    by_cases hnm : n < m
    · have hmin_n : min n m = n := Nat.min_eq_left (by omega)
      have hmin_succ : min (n+1) m = n + 1 := Nat.min_eq_left (by omega)
      rw [hmin_n] at ih
      rw [hmin_succ]
      have hif : (if n < m then f n else 0) = f n := by simp [hnm]
      rw [hif, sumRange_succ, ih]
    · have hmin_n : min n m = m := Nat.min_eq_right (by omega)
      have hmin_succ : min (n+1) m = m := Nat.min_eq_right (by omega)
      rw [hmin_n] at ih
      rw [hmin_succ]
      have hif : (if n < m then f n else 0) = 0 := by simp [hnm]
      rw [hif, ih, Int.add_zero]

theorem sumRange_zero_beyond_min_aux (f : Nat → Int) (n m : Nat)
    (hz : ∀ k, n ≤ k → f k = 0) :
    sumRange f m = sumRange f (min n m) := by
  induction m with
  | zero =>
    have hmin : min n 0 = 0 := by omega
    rw [hmin]
  | succ m ihm =>
    by_cases hmn : m < n
    · rw [Nat.min_eq_right (by omega : m + 1 ≤ n)]
    · have hfm : f m = 0 := hz m (by omega)
      have hmin_m : min n m = min n (m+1) := by
        have h1 : min n m = n := Nat.min_eq_left (by omega)
        have h2 : min n (m+1) = n := Nat.min_eq_left (by omega)
        omega
      calc sumRange f (m+1) = sumRange f m + f m := sumRange_succ _ _
        _ = sumRange f m + 0 := by rw [hfm]
        _ = sumRange f m := by rw [Int.add_zero]
        _ = sumRange f (min n m) := ihm
        _ = sumRange f (min n (m+1)) := by rw [hmin_m]

theorem rows_spanned_of_left_combo (M S : IMat) (C : IMat) (d4 : Int)
    (hd : d4 ≠ 0)
    (hC : imatMul C S = imatSmul d4 M) :
    ∀ i : Nat, i < imatRows M →
      ∃ coeffs, coeffs.length = imatRows S ∧
        d4 • ((M[i]?).getD []) = lincomb coeffs S := by
  intro i hi
  have hrowsC : imatRows C = imatRows M := by
    have h1 : (imatMul C S).length = imatRows C := imatMul_rows_aux C S
    have h2 : (imatSmul d4 M).length = imatRows M := by
      exact imatSmul_rows_aux d4 M
    have h3 : (imatMul C S).length = (imatSmul d4 M).length := by
      rw [hC]
    simp only [imatRows] at h1 h2 h3 ⊢
    omega
  have hiC : i < imatRows C := by omega
  have hrowLen : (((M[i]?).getD []).length) = imatCols S :=
    spanning_row_length_aux M S C d4 hC i hi
  let coeffs : List Int := (List.range (imatRows S)).map
    fun k => if k < imatCols C then imatGet C i k else 0
  have hcoeffsLen : coeffs.length = imatRows S := by
    simp [coeffs, List.length_map, List.length_range]
  refine ⟨coeffs, hcoeffsLen, ?_⟩
  have hlinLen : (lincomb coeffs S).length = imatCols S :=
    lincomb_length_aux coeffs S hcoeffsLen
  have hsmulLen : (vecSmul d4 ((M[i]?).getD [])).length = imatCols S := by
    rw [vecSmul_length_aux]
    exact hrowLen
  have hsmulEq : d4 • ((M[i]?).getD []) = vecSmul d4 ((M[i]?).getD []) := rfl
  rw [hsmulEq]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < imatCols S
  · have hjRow : j < (((M[i]?).getD []).length) := by omega
    have hjVec : j < (vecSmul d4 ((M[i]?).getD [])).length := by omega
    have hL := vecSmul_entry_aux d4 ((M[i]?).getD []) j hjRow
    -- simplify LHS getD to imatGet M i j via rowGet
    have hrowGet : ((((M[i]?).getD [])[j]?).getD 0) = imatGet M i j := by
      rw [imatGet_rowGet_aux]
    -- hL : (vecSmul ...)[j]? = some (d4 * ((row[j]?).getD 0))
    have hR := lincomb_entry_aux coeffs S j hj
    rw [hL, hR]
    -- need d4 * row_j = sum coeffs*S
    have hcoeffsGet : ∀ k, k < imatRows S →
        ((coeffs[k]?).getD 0) = (if k < imatCols C then imatGet C i k else 0) := by
      intro k hk
      have hrange : (List.range (imatRows S))[k]? = some k := List.getElem?_range hk
      have hmap : (coeffs[k]?) = some (if k < imatCols C then imatGet C i k else 0) := by
        simp [coeffs, List.getElem?_map, hrange]
      rw [hmap]
      simp
    have hsum1 : sumRange (fun k => (coeffs[k]?).getD 0 * ((((S[k]?).getD [])[j]?).getD 0))
        coeffs.length =
        sumRange (fun k => (if k < imatCols C then imatGet C i k else 0) * imatGet S k j)
        (imatRows S) := by
      rw [hcoeffsLen]
      apply sumRange_congr_lt
      intro k hk
      simp only [hcoeffsGet k hk, imatGet_rowGet_aux]
    rw [hsum1]
    have hsum2 : ∀ k, (if k < imatCols C then imatGet C i k else (0 : Int)) * imatGet S k j =
        (if k < imatCols C then imatGet C i k * imatGet S k j else 0) := by
      intro k
      by_cases hk : k < imatCols C
      · simp [hk]
      · simp [hk]
    have hsum2' : sumRange (fun k => (if k < imatCols C then imatGet C i k else 0) * imatGet S k j)
        (imatRows S) =
        sumRange (fun k => if k < imatCols C then imatGet C i k * imatGet S k j else 0)
        (imatRows S) := by
      apply sumRange_congr_lt
      intro k hk
      exact hsum2 k
    rw [hsum2']
    have hmin1 := sumRange_if_min_aux (fun k => imatGet C i k * imatGet S k j)
      (imatRows S) (imatCols C)
    rw [hmin1]
    -- mul sum equals min sum via zero-beyond (S zero beyond rows S)
    have hzeroBeyond : ∀ k, imatRows S ≤ k → imatGet C i k * imatGet S k j = 0 := by
      intro k hk
      have hSzero : imatGet S k j = 0 := by
        unfold imatRows at hk
        unfold imatGet
        have hnone : S[k]? = none := List.getElem?_eq_none hk
        rw [hnone]
        simp
      rw [hSzero, Int.mul_zero]
    have hmin2 := sumRange_zero_beyond_min_aux (fun k => imatGet C i k * imatGet S k j)
      (imatRows S) (imatCols C) hzeroBeyond
    -- hmin2 : sum f (cols C) = sum f (min rows cols)
    have hmulEntry : imatGet (imatMul C S) i j =
        sumRange (fun k => imatGet C i k * imatGet S k j) (imatCols C) := by
      have hjS : j < imatCols S := hj
      -- need j < cols S for mul entry? mul entry needs j < cols S? Actually imatMul_entry needs j < cols S? No, needs j < cols S? Second arg is S, so j < cols S? Wait imatMul C S entry needs j < cols S (since B=S). Yes hj gives that.
      -- Also need i < rows C (hiC).
      exact imatMul_entry_aux C S i j hiC hjS
    have hsmulEntry : imatGet (imatSmul d4 M) i j = d4 * imatGet M i j :=
      imatSmul_entry_aux d4 M i j
    have hcong : imatGet (imatMul C S) i j = imatGet (imatSmul d4 M) i j := by
      rw [hC]
    rw [hmulEntry, hsmulEntry] at hcong
    -- hcong : sum_{k<cols C} = d4 * M_{i,j}
    -- goal: d4 * row_j = sum_{min} ; row_j = M_{i,j} via rowGet
    have hrowM : (((M[i]?).getD [])[j]?).getD 0 = imatGet M i j := by
      rw [imatGet_rowGet_aux]
    -- LHS of goal after rw hL is d4 * row_j, need to rewrite row_j to M
    have hLhs : d4 * ((((M[i]?).getD [])[j]?).getD 0) = d4 * imatGet M i j := by
      rw [hrowM]
    -- goal is some (d4*row) = some (min sum); rewrite LHS via hLhs, RHS min sum vs mul sum via hmin2
    have hgoal : d4 * ((((M[i]?).getD [])[j]?).getD 0) =
        sumRange (fun k => imatGet C i k * imatGet S k j) (min (imatRows S) (imatCols C)) := by
      rw [hrowM, ← hcong, ← hmin2]
    exact congrArg some hgoal
  · have hleL : (vecSmul d4 ((M[i]?).getD [])).length ≤ j := by omega
    have hleR : (lincomb coeffs S).length ≤ j := by omega
    rw [List.getElem?_eq_none hleL, List.getElem?_eq_none hleR]

-- Steinitz exchange helpers.

theorem vecSmul_zeroVec_aux (d : Int) (n : Nat) :
    vecSmul d (zeroVec n) = zeroVec n := by
  unfold vecSmul zeroVec
  rw [List.map_replicate]
  simp

theorem vecSmul_eq_zeroVec_aux (d : Int) (hd : d ≠ 0) (v : List Int)
    (h : vecSmul d v = zeroVec v.length) : v = zeroVec v.length := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < v.length
  · have h1 : (vecSmul d v)[j]? = some (d * ((v[j]?).getD 0)) :=
      vecSmul_entry_aux d v j hj
    have h2 : (zeroVec v.length)[j]? = some (0 : Int) :=
      zeroVec_entry_aux v.length j hj
    have h3 : (vecSmul d v)[j]? = (zeroVec v.length)[j]? := by rw [h]
    rw [h1, h2] at h3
    have hdx : d * ((v[j]?).getD 0) = 0 := by simpa using h3
    have hx : ((v[j]?).getD 0) = 0 := by
      rcases Int.mul_eq_zero.mp hdx with h | h
      · omega
      · exact h
    have h4 : v[j]? = some ((v[j]?).getD 0) := by
      cases hv : v[j]? with
      | none =>
        have hlen : ¬ j < v.length := by
          intro hlt
          have heq := List.getElem?_eq_getElem hlt
          rw [hv] at heq
          simp at heq
        omega
      | some x => simp
    rw [hx] at h4
    rw [h4, h2]
  · have hn1 : v[j]? = none := List.getElem?_eq_none (by omega)
    have hn2 : (zeroVec v.length)[j]? = none := by
      apply List.getElem?_eq_none
      rw [zeroVec_length_aux]
      omega
    rw [hn1, hn2]

theorem lincomb_zeroVec_aux (S : IMat) :
    lincomb (zeroVec S.length) S = zeroVec (((S[0]?).getD []).length) := by
  cases S with
  | nil =>
    simp [lincomb, zeroVec]
  | cons v0 rest =>
    have hget : (((v0 :: rest)[0]?).getD []) = v0 := by simp
    rw [hget]
    have hlenC : (zeroVec (v0 :: rest).length).length = (v0 :: rest).length :=
      zeroVec_length_aux _
    apply List.ext_getElem?
    intro j
    by_cases hj : j < v0.length
    · have him : imatCols (v0 :: rest) = v0.length := by simp [imatCols]
      have hL := lincomb_entry_aux (zeroVec (v0 :: rest).length) (v0 :: rest) j
        (by omega)
      have hR : (zeroVec v0.length)[j]? = some (0 : Int) :=
        zeroVec_entry_aux v0.length j hj
      have hsum : sumRange
          (fun i => ((zeroVec (v0 :: rest).length)[i]?).getD 0 *
            (((((v0 :: rest)[i]?).getD [])[j]?).getD 0))
          (zeroVec (v0 :: rest).length).length = 0 := by
        apply sumRange_eq_zero_of_eq_zero
        intro i hi
        have hi0 : ((zeroVec (v0 :: rest).length)[i]?).getD 0 = 0 := by
          have he : (zeroVec (v0 :: rest).length)[i]? = some (0 : Int) := by
            apply zeroVec_entry_aux
            simpa [zeroVec_length_aux] using hi
          rw [he]
          simp
        rw [hi0, Int.zero_mul]
      rw [hL, hR]
      have hlenrw : (zeroVec (v0 :: rest).length).length = (v0 :: rest).length :=
        zeroVec_length_aux _
      rw [hlenrw] at hsum ⊢
      exact congrArg some hsum
    · have hn1 : (lincomb (zeroVec (v0 :: rest).length) (v0 :: rest))[j]? = none := by
        apply List.getElem?_eq_none
        have hl := lincomb_length_aux (zeroVec (v0 :: rest).length) (v0 :: rest) hlenC
        rw [hl]
        simp [imatCols]
        omega
      have hn2 : (zeroVec v0.length)[j]? = none := by
        apply List.getElem?_eq_none
        rw [zeroVec_length_aux]
        omega
      rw [hn1, hn2]

def unitVec (n i : Nat) : List Int :=
  (List.range n).map fun k => if k == i then 1 else 0

theorem unitVec_length_aux (n i : Nat) : (unitVec n i).length = n := by
  unfold unitVec
  rw [List.length_map, List.length_range]

theorem unitVec_entry_aux (n i k : Nat) (hk : k < n) :
    ((unitVec n i)[k]?).getD 0 = (if k == i then (1 : Int) else 0) := by
  unfold unitVec
  have hr : (List.range n)[k]? = some k := List.getElem?_range hk
  rw [List.getElem?_map, hr]
  simp

theorem lincomb_unitVec_aux (S : IMat) (hlen : Nat)
    (hS : ∀ s ∈ S, s.length = hlen)
    (i : Nat) (hi : i < S.length) :
    lincomb (unitVec S.length i) S = ((S[i]?).getD []) := by
  have hne : S ≠ [] := by
    intro hcon
    rw [hcon] at hi
    simp at hi
  obtain ⟨v0, rest, hScons⟩ : ∃ v0 rest, S = v0 :: rest := by
    cases S with
    | nil => simp at hi
    | cons v0 rest => exact ⟨v0, rest, rfl⟩
  subst hScons
  have hv0len : v0.length = hlen := hS v0 (by simp)
  have him : imatCols (v0 :: rest) = hlen := by simp [imatCols, hv0len]
  have hget : ((v0 :: rest)[i]?) = some ((v0 :: rest)[i]'hi) :=
    List.getElem?_eq_getElem hi
  have hmem : ((v0 :: rest)[i]'hi) ∈ (v0 :: rest) := List.getElem_mem hi
  have hgetD : (((v0 :: rest)[i]?).getD []) = ((v0 :: rest)[i]'hi) := by
    rw [hget]; simp
  have hSilen : (((v0 :: rest)[i]?).getD []).length = hlen := by
    rw [hgetD]; exact hS _ hmem
  have hlenC : (unitVec (v0 :: rest).length i).length = (v0 :: rest).length :=
    unitVec_length_aux _ _
  have hlinlen := lincomb_length_aux (unitVec (v0 :: rest).length i) (v0 :: rest) hlenC
  rw [him] at hlinlen
  apply List.ext_getElem?
  intro j
  by_cases hj : j < hlen
  · have hjC : j < imatCols (v0 :: rest) := by omega
    have hL := lincomb_entry_aux (unitVec (v0 :: rest).length i) (v0 :: rest) j hjC
    have hR : ((((v0 :: rest)[i]?).getD [])[j]?) =
        some ((((((v0 :: rest)[i]?).getD [])[j]?).getD 0)) := by
      cases hmem : ((((v0 :: rest)[i]?).getD [])[j]?) with
      | none =>
        have hlen : ¬ j < ((((v0 :: rest)[i]?).getD []).length) := by
          intro hlt
          have heq := List.getElem?_eq_getElem hlt
          rw [hmem] at heq
          simp at heq
        omega
      | some x => simp
    rw [hL]
    have hterm : ∀ t, t < (unitVec (v0 :: rest).length i).length →
        (((unitVec (v0 :: rest).length i)[t]?).getD 0 *
          (((((v0 :: rest)[t]?).getD [])[j]?).getD 0)) =
        (((((v0 :: rest)[t]?).getD [])[j]?).getD 0 *
          (if t == i then (1 : Int) else 0)) := by
      intro t ht
      have htlen : t < (v0 :: rest).length := by
        rw [unitVec_length_aux] at ht
        exact ht
      rw [unitVec_entry_aux _ _ _ htlen, Int.mul_comm]
    have hcongr := sumRange_congr_lt _ _
      ((unitVec (v0 :: rest).length i).length) hterm
    rw [hcongr]
    have hey := sumRange_eye
      (fun t => (((((v0 :: rest)[t]?).getD [])[j]?).getD 0))
      (unitVec (v0 :: rest).length i).length i
      (by simpa [unitVec_length_aux] using hi)
    rw [unitVec_length_aux] at hey hcongr ⊢
    rw [hey]
    exact hR.symm
  · have hn1 : (lincomb (unitVec (v0 :: rest).length i) (v0 :: rest))[j]? = none := by
      apply List.getElem?_eq_none
      omega
    have hn2 : ((((v0 :: rest)[i]?).getD [])[j]?) = none := by
      apply List.getElem?_eq_none
      omega
    rw [hn1, hn2]

theorem not_independent_of_mem_zeroVec_aux (S : IMat) (hlen : Nat)
    (hS : ∀ s ∈ S, s.length = hlen)
    (i : Nat) (hi : i < S.length)
    (h0 : ((S[i]?).getD []) = zeroVec hlen) : ¬ independent S := by
  intro hindep
  have hunit := lincomb_unitVec_aux S hlen hS i hi
  rw [h0] at hunit
  have hS0 : (((S[0]?).getD []).length) = hlen := by
    have h0lt : 0 < S.length := by omega
    have hget : (S[0]?) = some (S[0]'h0lt) := List.getElem?_eq_getElem h0lt
    have hmem : (S[0]'h0lt) ∈ S := List.getElem_mem h0lt
    have hlen0 : ((S[0]'h0lt)).length = hlen := hS _ hmem
    rw [hget]
    simpa using hlen0
  have hlenU : (unitVec S.length i).length = S.length := unitVec_length_aux _ _
  have hcon := hindep (unitVec S.length i) hlenU (by rw [hunit, hS0])
  have hei : ((unitVec S.length i)[i]?).getD 0 = 1 := by
    rw [unitVec_entry_aux _ _ _ hi]
    simp
  have hez : ((zeroVec S.length)[i]?).getD 0 = 0 := by
    have he : (zeroVec S.length)[i]? = some (0 : Int) :=
      zeroVec_entry_aux _ _ hi
    rw [he]; simp
  have hcc : ((unitVec S.length i)[i]?).getD 0 =
      ((zeroVec S.length)[i]?).getD 0 := by
    rw [hcon]
  omega

theorem sumRange_succ'_aux (f : Nat → Int) (n : Nat) :
    sumRange f (n + 1) = f 0 + sumRange (fun t => f (t + 1)) n := by
  induction n with
  | zero =>
    rw [sumRange_succ]
    simp [sumRange]
  | succ n ih =>
    rw [sumRange_succ, ih, sumRange_succ]
    ac_rfl

theorem lincomb_cons_zero_aux (v0 v1 : List Int) (rest : List (List Int))
    (hlen : Nat) (hv0 : v0.length = hlen) (hv1 : v1.length = hlen)
    (coeffs : List Int) (hc : coeffs.length = (v1 :: rest).length) :
    lincomb (0 :: coeffs) (v0 :: v1 :: rest) = lincomb coeffs (v1 :: rest) := by
  have himL : imatCols (v0 :: v1 :: rest) = hlen := by simp [imatCols, hv0]
  have himR : imatCols (v1 :: rest) = hlen := by simp [imatCols, hv1]
  have hlenL : (lincomb (0 :: coeffs) (v0 :: v1 :: rest)).length = hlen := by
    have hcc : (0 :: coeffs).length = (v0 :: v1 :: rest).length := by
      simp at hc ⊢
      omega
    have := lincomb_length_aux (0 :: coeffs) (v0 :: v1 :: rest) hcc
    omega
  have hlenR : (lincomb coeffs (v1 :: rest)).length = hlen := by
    have := lincomb_length_aux coeffs (v1 :: rest) hc
    omega
  apply List.ext_getElem?
  intro j
  by_cases hj : j < hlen
  · have hjL : j < imatCols (v0 :: v1 :: rest) := by omega
    have hjR : j < imatCols (v1 :: rest) := by omega
    have hL := lincomb_entry_aux (0 :: coeffs) (v0 :: v1 :: rest) j hjL
    have hR := lincomb_entry_aux coeffs (v1 :: rest) j hjR
    rw [hL, hR]
    have hlen0 : (0 :: coeffs).length = coeffs.length + 1 := rfl
    rw [hlen0, sumRange_succ'_aux]
    have hz : (((0 :: coeffs)[0]?).getD 0 *
        (((((v0 :: v1 :: rest)[0]?).getD [])[j]?).getD 0)) = 0 := by
      simp
    rw [hz, Int.zero_add]
    apply congrArg some
    apply sumRange_congr_lt
    intro t ht
    have hc1 : ((((0 :: coeffs)[t + 1]?).getD 0)) = (((coeffs[t]?).getD 0)) := rfl
    have hw1 : ((((v0 :: v1 :: rest)[t + 1]?).getD [])) = ((((v1 :: rest)[t]?).getD [])) := rfl
    rw [hc1, hw1]
  · have hn1 : (lincomb (0 :: coeffs) (v0 :: v1 :: rest))[j]? = none := by
      apply List.getElem?_eq_none
      omega
    have hn2 : (lincomb coeffs (v1 :: rest))[j]? = none := by
      apply List.getElem?_eq_none
      omega
    rw [hn1, hn2]

theorem independent_cons_tail_aux (v0 : List Int) (vs : List (List Int))
    (hlen : Nat) (hv0 : v0.length = hlen) (hvs : ∀ s ∈ vs, s.length = hlen)
    (h : independent (v0 :: vs)) : independent vs := by
  cases vs with
  | nil =>
    intro coeffs hlenC hlin
    have hc0 : coeffs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlenC)
    subst hc0
    simp [zeroVec]
  | cons v1 rest =>
    have hv1 : v1.length = hlen := hvs v1 (by simp)
    intro coeffs hlenC hlin
    have hlenC' : (0 :: coeffs).length = (v0 :: v1 :: rest).length := by
      simp at hlenC ⊢
      omega
    have hcons0 := lincomb_cons_zero_aux v0 v1 rest hlen hv0 hv1 coeffs
      (by simpa using hlenC)
    have hzv : zeroVec (((v0 :: v1 :: rest)[0]?).getD []).length =
        zeroVec (((v1 :: rest)[0]?).getD []).length := by
      simp [hv0, hv1]
    have hfull : lincomb (0 :: coeffs) (v0 :: v1 :: rest) =
        zeroVec ((((v0 :: v1 :: rest)[0]?).getD []).length) := by
      rw [hcons0, hlin, hzv]
    have hcon := h (0 :: coeffs) hlenC' hfull
    have hz : zeroVec (v0 :: v1 :: rest).length =
        0 :: zeroVec (v1 :: rest).length := by
      simp [zeroVec, List.replicate_succ]
    rw [hz] at hcon
    exact (List.cons_eq_cons.mp hcon).2

def vecSub (x y : List Int) : List Int :=
  (List.range x.length).map fun k => ((x[k]?).getD 0) - ((y[k]?).getD 0)

theorem vecSub_length_aux (x y : List Int) : (vecSub x y).length = x.length := by
  unfold vecSub
  rw [List.length_map, List.length_range]

theorem vecSub_entry_aux (x y : List Int) (k : Nat) (hk : k < x.length) :
    ((vecSub x y)[k]?) = some ((((x[k]?).getD 0) - ((y[k]?).getD 0))) := by
  unfold vecSub
  have hr : (List.range x.length)[k]? = some k := List.getElem?_range hk
  rw [List.getElem?_map, hr]
  simp

/-- The exchange combination `a • v - cj • v₀` as a list. -/
def psiVec (a : Int) (v v₀ : List Int) (cj : Int) : List Int :=
  vecSub (vecSmul a v) (vecSmul cj v₀)

theorem psiVec_length_aux (a : Int) (v v₀ : List Int) (cj : Int) :
    (psiVec a v v₀ cj).length = v.length := by
  unfold psiVec
  rw [vecSub_length_aux, vecSmul_length_aux]

theorem psiVec_entry_aux (a : Int) (v v₀ : List Int) (cj : Int) (hlen k : Nat)
    (hv : v.length = hlen) (hv₀ : v₀.length = hlen) (hk : k < hlen) :
    ((psiVec a v v₀ cj)[k]?) =
      some (a * ((v[k]?).getD 0) - cj * ((v₀[k]?).getD 0)) := by
  have e1 : ((vecSmul a v)[k]?) = some (a * ((v[k]?).getD 0)) :=
    vecSmul_entry_aux _ _ _ (by omega)
  have e2 : ((vecSmul cj v₀)[k]?) = some (cj * ((v₀[k]?).getD 0)) :=
    vecSmul_entry_aux _ _ _ (by omega)
  unfold psiVec
  rw [vecSub_entry_aux _ _ _ (by rw [vecSmul_length_aux]; omega)]
  simp only [e1, e2, Option.getD_some]

theorem sumRange_peel_last_aux (f : Nat → Int) (n : Nat) (hn : 0 < n) :
    sumRange f n = sumRange f (n - 1) + f (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact sumRange_succ f m

/-- Reindexing sum over an erased list equals the full sum minus the erased term. -/
theorem sigma_sum_erase_aux (F : Nat → Int) (n j₀ : Nat) (hj₀ : j₀ < n) :
    sumRange (fun t => F (if t < j₀ then t else t + 1)) (n - 1) =
      sumRange F n - F j₀ := by
  induction n generalizing j₀ with
  | zero => omega
  | succ n ih =>
    by_cases hjn : j₀ = n
    · have hn1 : (n + 1) - 1 = n := by omega
      have hcongr : sumRange (fun t => F (if t < j₀ then t else t + 1)) ((n + 1) - 1) =
          sumRange F n := by
        rw [hn1]
        apply sumRange_congr_lt
        intro t ht
        have htt : (if t < j₀ then t else t + 1) = t := by
          have hlt : t < j₀ := by omega
          simp [hlt]
        rw [htt]
      rw [hcongr, sumRange_succ, hjn]
      omega
    · have hj₀n : j₀ < n := by omega
      have hih := ih j₀ hj₀n
      have hn1 : (n + 1) - 1 = n := by omega
      rw [hn1, sumRange_peel_last_aux _ n (by omega)]
      have hsig : (if n - 1 < j₀ then n - 1 else n - 1 + 1) = n := by
        have h1 : ¬ (n - 1 < j₀) := by omega
        simp only [h1, if_false]
        omega
      rw [hsig]
      have hFs := sumRange_succ F n
      omega

theorem eraseIdx_length_aux (U : IMat) (j₀ : Nat) (hj₀ : j₀ < U.length) :
    (U.eraseIdx j₀).length = U.length - 1 := by
  rw [List.length_eraseIdx]
  simp [hj₀]

theorem eraseIdx_getD_aux (U : IMat) (j₀ t : Nat) :
    ((((U.eraseIdx j₀)[t]?).getD [])) =
      ((((U[if t < j₀ then t else t + 1]?).getD []))) := by
  have h := List.getElem?_eraseIdx (l := U) (i := j₀) (j := t)
  rw [h]
  by_cases hlt : t < j₀ <;> simp [hlt]

theorem sumRange_sub_aux (f g : Nat → Int) (n : Nat) :
    sumRange (fun i => f i - g i) n = sumRange f n - sumRange g n := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [sumRange_succ (fun i => f i - g i) n, ih,
      sumRange_succ f n, sumRange_succ g n]
    omega

/-- Exchange coefficient combination at index `s`:
    `(a • c[s] - cj • c₀[s]) • U[s][k]`. -/
def exchangeF (a cj : Int) (c c₀ : List Int) (U : IMat) (k : Nat) : Nat → Int :=
  fun s => (a * (((c[s]?).getD 0)) - cj * (((c₀[s]?).getD 0))) *
    (((((U[s]?).getD [])[k]?).getD 0))

/-- Core exchange identity: `d • ψ` expands over the erased index family.
    The `j₀`-terms cancel because `c₀[j₀] = a`. -/
theorem exchange_entry_aux (U : IMat) (j₀ : Nat) (hj₀ : j₀ < U.length)
    (a d cj : Int) (hlen : Nat)
    (hlenU : ∀ u ∈ U, u.length = hlen)
    (v v₀ : List Int) (hv : v.length = hlen) (hv₀ : v₀.length = hlen)
    (c c₀ : List Int) (hclen : c.length = U.length) (hc0len : c₀.length = U.length)
    (hc : vecSmul d v = lincomb c U) (hc0 : vecSmul d v₀ = lincomb c₀ U)
    (hcj : ((c[j₀]?).getD 0) = cj) (ha : ((c₀[j₀]?).getD 0) = a)
    (k : Nat) (hk : k < hlen) :
    d * (a * (((v[k]?).getD 0)) - cj * (((v₀[k]?).getD 0))) =
      sumRange (fun t => (a * (((c[if t < j₀ then t else t + 1]?).getD 0)) -
        cj * (((c₀[if t < j₀ then t else t + 1]?).getD 0))) *
        (((((U[if t < j₀ then t else t + 1]?).getD [])[k]?).getD 0)))
      (U.eraseIdx j₀).length := by
  have hUne : U ≠ [] := by
    intro hcon
    rw [hcon] at hj₀
    simp at hj₀
  obtain ⟨u0, us, hUcons⟩ : ∃ u0 us, U = u0 :: us := by
    cases U with
    | nil => simp at hj₀
    | cons u0 us => exact ⟨u0, us, rfl⟩
  subst hUcons
  have himU : imatCols (u0 :: us) = hlen := by
    simp [imatCols, hlenU u0 (by simp)]
  have hjU : k < imatCols (u0 :: us) := by omega
  have ev : d * (((v[k]?).getD 0)) =
      sumRange (fun s => (((c[s]?).getD 0)) * (((((u0 :: us)[s]?).getD [])[k]?).getD 0))
        c.length := by
    have h1 : (vecSmul d v)[k]? = some (d * (((v[k]?).getD 0))) :=
      vecSmul_entry_aux _ _ _ (by omega)
    have h2 := lincomb_entry_aux c (u0 :: us) k hjU
    have h3 : (vecSmul d v)[k]? = (lincomb c (u0 :: us))[k]? := by rw [hc]
    rw [h1, h2] at h3
    simpa using h3
  have ev0 : d * (((v₀[k]?).getD 0)) =
      sumRange (fun s => (((c₀[s]?).getD 0)) * (((((u0 :: us)[s]?).getD [])[k]?).getD 0))
        c₀.length := by
    have h1 : (vecSmul d v₀)[k]? = some (d * (((v₀[k]?).getD 0))) :=
      vecSmul_entry_aux _ _ _ (by omega)
    have h2 := lincomb_entry_aux c₀ (u0 :: us) k hjU
    have h3 : (vecSmul d v₀)[k]? = (lincomb c₀ (u0 :: us))[k]? := by rw [hc0]
    rw [h1, h2] at h3
    simpa using h3
  have hLHS : d * (a * (((v[k]?).getD 0)) - cj * (((v₀[k]?).getD 0))) =
      a * (d * (((v[k]?).getD 0))) - cj * (d * (((v₀[k]?).getD 0))) := by
    have c1 : d * a = a * d := Int.mul_comm _ _
    have c2 : d * cj = cj * d := Int.mul_comm _ _
    simp only [Int.mul_sub, ← Int.mul_assoc]
    rw [c1, c2]
  rw [hLHS, ev, ev0, hclen, hc0len]
  have hcomb : a * sumRange
        (fun s => (((c[s]?).getD 0)) * (((((u0 :: us)[s]?).getD [])[k]?).getD 0))
        (u0 :: us).length -
      cj * sumRange
        (fun s => (((c₀[s]?).getD 0)) * (((((u0 :: us)[s]?).getD [])[k]?).getD 0))
        (u0 :: us).length =
      sumRange (exchangeF a cj c c₀ (u0 :: us) k) (u0 :: us).length := by
    have e1 : a * sumRange
          (fun s => (((c[s]?).getD 0)) * (((((u0 :: us)[s]?).getD [])[k]?).getD 0))
          (u0 :: us).length =
        sumRange (fun s => a * ((((c[s]?).getD 0)) * (((((u0 :: us)[s]?).getD [])[k]?).getD 0)))
          (u0 :: us).length := by
      rw [sumRange_smul_left]
    have e2 : cj * sumRange
          (fun s => (((c₀[s]?).getD 0)) * (((((u0 :: us)[s]?).getD [])[k]?).getD 0))
          (u0 :: us).length =
        sumRange (fun s => cj * ((((c₀[s]?).getD 0)) * (((((u0 :: us)[s]?).getD [])[k]?).getD 0)))
          (u0 :: us).length := by
      rw [sumRange_smul_left]
    rw [e1, e2, ← sumRange_sub_aux]
    apply sumRange_congr_lt
    intro s hs
    simp only [exchangeF, Int.sub_mul, Int.mul_assoc]
  rw [hcomb]
  have hsplit := sigma_sum_erase_aux (exchangeF a cj c c₀ (u0 :: us) k)
    (u0 :: us).length j₀ hj₀
  have hHj0 : exchangeF a cj c c₀ (u0 :: us) k j₀ = 0 := by
    have hcomm : a * cj = cj * a := Int.mul_comm _ _
    simp only [exchangeF]
    rw [hcj, ha, hcomm]
    simp
  have hUU : ((u0 :: us).eraseIdx j₀).length = (u0 :: us).length - 1 :=
    eraseIdx_length_aux _ _ hj₀
  have hB : sumRange (exchangeF a cj c c₀ (u0 :: us) k) (u0 :: us).length =
      sumRange (fun t => exchangeF a cj c c₀ (u0 :: us) k (if t < j₀ then t else t + 1))
        ((u0 :: us).length - 1) := by
    omega
  rw [hB, hUU]
  apply sumRange_congr_lt
  intro t ht
  simp only [exchangeF]

/-- Exchange coefficients over the erased list. -/
def exchangeCoeffs (a cj : Int) (c c₀ : List Int) (U : IMat) (j₀ : Nat) : List Int :=
  (List.range (U.eraseIdx j₀).length).map fun t =>
    a * (((c[if t < j₀ then t else t + 1]?).getD 0)) -
    cj * (((c₀[if t < j₀ then t else t + 1]?).getD 0))

theorem exchangeCoeffs_length_aux (a cj : Int) (c c₀ : List Int) (U : IMat) (j₀ : Nat) :
    (exchangeCoeffs a cj c c₀ U j₀).length = (U.eraseIdx j₀).length := by
  simp [exchangeCoeffs]

theorem exchangeCoeffs_entry_aux (a cj : Int) (c c₀ : List Int) (U : IMat) (j₀ : Nat)
    (t : Nat) (ht : t < (U.eraseIdx j₀).length) :
    (((exchangeCoeffs a cj c c₀ U j₀)[t]?).getD 0) =
      (a * (((c[if t < j₀ then t else t + 1]?).getD 0)) -
       cj * (((c₀[if t < j₀ then t else t + 1]?).getD 0))) := by
  have hr : (List.range (U.eraseIdx j₀).length)[t]? = some t :=
    List.getElem?_range ht
  simp only [exchangeCoeffs, List.getElem?_map, hr, Option.map_some, Option.getD_some]

/-- Exchange spanning: `d • ψ` is a `lincomb` over the erased list. -/
theorem exchange_span_aux (U : IMat) (j₀ : Nat) (hj₀ : j₀ < U.length)
    (a d cj : Int) (hlen : Nat)
    (hlenU : ∀ u ∈ U, u.length = hlen)
    (v v₀ : List Int) (hv : v.length = hlen) (hv₀ : v₀.length = hlen)
    (c c₀ : List Int) (hclen : c.length = U.length) (hc0len : c₀.length = U.length)
    (hc : vecSmul d v = lincomb c U) (hc0 : vecSmul d v₀ = lincomb c₀ U)
    (hcj : ((c[j₀]?).getD 0) = cj) (ha : ((c₀[j₀]?).getD 0) = a)
    (hneU' : (U.eraseIdx j₀) ≠ []) :
    ∃ c', c'.length = (U.eraseIdx j₀).length ∧
      vecSmul d (psiVec a v v₀ cj) = lincomb c' (U.eraseIdx j₀) := by
  obtain ⟨w0, ws, hWcons⟩ : ∃ w0 ws, U.eraseIdx j₀ = w0 :: ws := by
    cases hW : (U.eraseIdx j₀) with
    | nil => exact absurd hW hneU'
    | cons w0 ws => exact ⟨w0, ws, rfl⟩
  have hw0U : w0 ∈ U := by
    apply List.mem_of_mem_eraseIdx
    rw [hWcons]
    simp
  have hw0len : w0.length = hlen := hlenU _ hw0U
  have himU' : imatCols (U.eraseIdx j₀) = hlen := by
    rw [hWcons]
    simp [imatCols, hw0len]
  refine ⟨exchangeCoeffs a cj c c₀ U j₀, exchangeCoeffs_length_aux _ _ _ _ _ _, ?_⟩
  have hlenC' := exchangeCoeffs_length_aux a cj c c₀ U j₀
  have hlenψ : (psiVec a v v₀ cj).length = hlen := by
    rw [psiVec_length_aux]
    exact hv
  have hlinlen := lincomb_length_aux (exchangeCoeffs a cj c c₀ U j₀)
    (U.eraseIdx j₀) hlenC'
  rw [himU'] at hlinlen
  have hsmullen : (vecSmul d (psiVec a v v₀ cj)).length = hlen := by
    rw [vecSmul_length_aux]
    exact hlenψ
  apply List.ext_getElem?
  intro k
  by_cases hk : k < hlen
  · have hL := vecSmul_entry_aux d (psiVec a v v₀ cj) k (by omega)
    have hP := psiVec_entry_aux a v v₀ cj hlen k hv hv₀ hk
    have hR := lincomb_entry_aux (exchangeCoeffs a cj c c₀ U j₀)
      (U.eraseIdx j₀) k (by omega)
    rw [hL, hR, hP]
    simp only [Option.getD_some]
    have hsum := sumRange_congr_lt
      (fun t => (((exchangeCoeffs a cj c c₀ U j₀)[t]?).getD 0) *
        (((((U.eraseIdx j₀)[t]?).getD [])[k]?).getD 0))
      (fun t => (a * (((c[if t < j₀ then t else t + 1]?).getD 0)) -
        cj * (((c₀[if t < j₀ then t else t + 1]?).getD 0))) *
        (((((U[if t < j₀ then t else t + 1]?).getD [])[k]?).getD 0)))
      (exchangeCoeffs a cj c c₀ U j₀).length
      (fun t ht => by
        have ht' : t < (U.eraseIdx j₀).length := by
          rw [← hlenC']
          exact ht
        rw [exchangeCoeffs_entry_aux _ _ _ _ _ _ _ ht', eraseIdx_getD_aux])
    rw [hsum, hlenC']
    exact congrArg some
      (exchange_entry_aux U j₀ hj₀ a d cj hlen hlenU v v₀ hv hv₀ c c₀
        hclen hc0len hc hc0 hcj ha k hk)
  · have hn1 : (vecSmul d (psiVec a v v₀ cj))[k]? = none := by
      apply List.getElem?_eq_none
      omega
    have hn2 : (lincomb (exchangeCoeffs a cj c c₀ U j₀) (U.eraseIdx j₀))[k]? = none := by
      apply List.getElem?_eq_none
      omega
    rw [hn1, hn2]

/-- Exchange torsion: over an empty erased list, `d • ψ` vanishes entry-wise. -/
theorem exchange_torsion_aux (U : IMat) (j₀ : Nat) (hj₀ : j₀ < U.length)
    (a d cj : Int) (hlen : Nat)
    (hlenU : ∀ u ∈ U, u.length = hlen)
    (v v₀ : List Int) (hv : v.length = hlen) (hv₀ : v₀.length = hlen)
    (c c₀ : List Int) (hclen : c.length = U.length) (hc0len : c₀.length = U.length)
    (hc : vecSmul d v = lincomb c U) (hc0 : vecSmul d v₀ = lincomb c₀ U)
    (hcj : ((c[j₀]?).getD 0) = cj) (ha : ((c₀[j₀]?).getD 0) = a)
    (hU'nil : (U.eraseIdx j₀) = [])
    (k : Nat) (hk : k < hlen) :
    d * (a * (((v[k]?).getD 0)) - cj * (((v₀[k]?).getD 0))) = 0 := by
  have hlen0 : (U.eraseIdx j₀).length = 0 := by
    rw [hU'nil]
    rfl
  have he := exchange_entry_aux U j₀ hj₀ a d cj hlen hlenU v v₀ hv hv₀ c c₀
    hclen hc0len hc hc0 hcj ha k hk
  rw [hlen0] at he
  have e0 : sumRange (fun t => (a * (((c[if t < j₀ then t else t + 1]?).getD 0)) -
      cj * (((c₀[if t < j₀ then t else t + 1]?).getD 0))) *
      (((((U[if t < j₀ then t else t + 1]?).getD [])[k]?).getD 0))) 0 = 0 :=
    sumRange_eq_zero_of_eq_zero _ _ (fun i hi => absurd hi (by omega))
  rw [e0] at he
  exact he

/-- A `d`-torsion independent family (all `d • w = 0⃗`) is empty. -/
theorem independent_torsion_nil_aux (W : IMat) (hlen : Nat) (d : Int) (hd : d ≠ 0)
    (hW : ∀ w ∈ W, w.length = hlen)
    (htor : ∀ w ∈ W, vecSmul d w = zeroVec hlen)
    (hindep : independent W) : W = [] := by
  cases hWc : W with
  | nil => rfl
  | cons w0 ws =>
    exfalso
    have hw0len : w0.length = hlen := hW w0 (by simp [hWc])
    have hw0 : vecSmul d w0 = zeroVec w0.length := by
      have h1 := htor w0 (by simp [hWc])
      rw [hw0len]
      exact h1
    have hw0z : w0 = zeroVec hlen := by
      have hz := vecSmul_eq_zeroVec_aux d hd w0 hw0
      rw [hw0len] at hz
      exact hz
    have h0 : ((((w0 :: ws)[0]?).getD [])) = zeroVec hlen := by
      simp [hw0z]
    have hindep' : independent (w0 :: ws) := by
      rw [← hWc]
      exact hindep
    exact not_independent_of_mem_zeroVec_aux _ _
      (fun s hs => hW s (by simp [hWc, hs])) 0 (by simp) h0 hindep'

theorem map_mul_getD_aux (e : List Int) (a : Int) (m : Nat) :
    ((((e.map fun x => a * x)[m]?).getD 0)) = a * (((e[m]?).getD 0)) := by
  rw [List.getElem?_map]
  cases (e[m]?) <;> simp

theorem lincomb_cons_entry_aux (e₀ : Int) (e : List Int) (v₀ : List Int)
    (vs : List (List Int)) (hlen k : Nat)
    (hv₀ : v₀.length = hlen) (hvs : ∀ s ∈ vs, s.length = hlen)
    (hk : k < hlen) :
    ((lincomb (e₀ :: e) (v₀ :: vs))[k]?) =
      some (e₀ * (((v₀[k]?).getD 0)) +
        sumRange (fun m => (((e[m]?).getD 0)) * (((((vs[m]?).getD [])[k]?).getD 0)))
          e.length) := by
  have him : imatCols (v₀ :: vs) = hlen := by simp [imatCols, hv₀]
  have hL := lincomb_entry_aux (e₀ :: e) (v₀ :: vs) k (by omega)
  have hlen0 : (e₀ :: e).length = e.length + 1 := rfl
  have hS1 := sumRange_succ'_aux
    (fun t => (((e₀ :: e)[t]?).getD 0) * (((((v₀ :: vs)[t]?).getD [])[k]?).getD 0))
    e.length
  rw [hL, hlen0, hS1]
  rfl

/-- Head coefficient for the dependence witness: negated total pivot mass. -/
def eHead (e : List Int) (g : List Int → Int) (vs : List (List Int)) : Int :=
  -(sumRange (fun i => (((e[i]?).getD 0)) * (g (((vs[i]?).getD [])))) e.length)

/-- Full dependence witness list: head mass plus scaled tail. -/
def eWit (e : List Int) (a : Int) (g : List Int → Int) (vs : List (List Int)) : List Int :=
  (eHead e g vs) :: (e.map fun x => a * x)

theorem exchange_indep_aux (v₀ : List Int) (vs : List (List Int))
    (a : Int) (ha : a ≠ 0) (hlen : Nat)
    (hv₀ : v₀.length = hlen) (hvs : ∀ s ∈ vs, s.length = hlen)
    (hindep : independent (v₀ :: vs))
    (g : List Int → Int) :
    independent (vs.map fun v => psiVec a v v₀ (g v)) := by
  intro e helenE hlinE
  have hEW : e.length = vs.length := by
    have h := helenE
    rw [List.length_map] at h
    exact h
  cases hvsn : vs with
  | nil =>
    have he0 : e.length = 0 := by
      rw [hvsn] at hEW
      simpa using hEW
    have hee : e = [] := List.eq_nil_of_length_eq_zero he0
    rw [hee]
    simp [hvsn, zeroVec]
  | cons v₁ rest =>
    subst hvsn
    have hW0lt : 0 < (((v₁ :: rest).map fun v => psiVec a v v₀ (g v))).length := by
      rw [List.length_map]
      simp
    have hW0get := List.getElem?_eq_getElem hW0lt
    have hW0mem := List.getElem_mem hW0lt
    obtain ⟨vstar, hstar_mem, hstar_eq⟩ := List.mem_map.mp hW0mem
    have hW0len : (((((v₁ :: rest).map fun v => psiVec a v v₀ (g v))[0]?).getD []).length) =
        hlen := by
      have h1 : ((((v₁ :: rest).map fun v => psiVec a v v₀ (g v))[0]?)) =
          some (psiVec a vstar v₀ (g vstar)) := by
        rw [hW0get]
        exact congrArg some hstar_eq.symm
      rw [h1]
      simp only [Option.getD_some]
      rw [psiVec_length_aux]
      exact hvs _ hstar_mem
    have himW : imatCols (((v₁ :: rest).map fun v => psiVec a v v₀ (g v))) = hlen :=
      hW0len
    have hWget : ∀ i, i < e.length →
        (((((v₁ :: rest).map fun v => psiVec a v v₀ (g v))[i]?).getD [])) =
          psiVec a (((v₁ :: rest)[i]?).getD []) v₀ (g (((v₁ :: rest)[i]?).getD [])) := by
      intro i hi
      have hilt : i < (v₁ :: rest).length := by omega
      obtain ⟨si, hsi⟩ : ∃ si, ((((v₁ :: rest)[i]?)) = some si) :=
        ⟨_, List.getElem?_eq_getElem hilt⟩
      have hgi : (((((v₁ :: rest).map fun v => psiVec a v v₀ (g v))[i]?))) =
          some (psiVec a si v₀ (g si)) := by
        rw [List.getElem?_map, hsi]
        simp
      rw [hgi, hsi]
      simp only [Option.getD_some]
    have hvi : ∀ i, i < e.length → ((((v₁ :: rest)[i]?).getD []).length) = hlen := by
      intro i hi
      have hilt : i < (v₁ :: rest).length := by omega
      have e1 : ((((v₁ :: rest)[i]?).getD [])) = ((v₁ :: rest)[i]'hilt) := by
        rw [List.getElem?_eq_getElem hilt, Option.getD_some]
      rw [e1]
      exact hvs _ (List.getElem_mem hilt)
    have hper : ∀ k, k < hlen →
        sumRange (fun i => (((e[i]?).getD 0)) *
          ((((((v₁ :: rest).map fun v => psiVec a v v₀ (g v))[i]?).getD [])[k]?).getD 0))
          e.length = 0 := by
      intro k hk
      have hjW : k < imatCols (((v₁ :: rest).map fun v => psiVec a v v₀ (g v))) := by omega
      have hLe := lincomb_entry_aux e
        (((v₁ :: rest).map fun v => psiVec a v v₀ (g v))) k hjW
      have hze : ((zeroVec (((((v₁ :: rest).map fun v => psiVec a v v₀ (g v))[0]?).getD []).length))[k]?) =
          some (0 : Int) := by
        apply zeroVec_entry_aux
        rw [hW0len]
        exact hk
      have hcong : (lincomb e (((v₁ :: rest).map fun v => psiVec a v v₀ (g v))))[k]? =
          ((zeroVec (((((v₁ :: rest).map fun v => psiVec a v v₀ (g v))[0]?).getD []).length))[k]?) := by
        rw [hlinE]
      rw [hLe] at hcong
      rw [hze] at hcong
      simpa using hcong
    have hident : ∀ k, k < hlen →
        sumRange (fun i => (((e[i]?).getD 0)) *
          (a * (((((v₁ :: rest)[i]?).getD [])[k]?).getD 0) -
           (g (((v₁ :: rest)[i]?).getD [])) * (((v₀[k]?).getD 0))))
        e.length = 0 := by
      intro k hk
      have h0 := hper k hk
      calc sumRange (fun i => (((e[i]?).getD 0)) *
            (a * (((((v₁ :: rest)[i]?).getD [])[k]?).getD 0) -
             (g (((v₁ :: rest)[i]?).getD [])) * (((v₀[k]?).getD 0))))
            e.length
          = sumRange (fun i => (((e[i]?).getD 0)) *
            ((((((v₁ :: rest).map fun v => psiVec a v v₀ (g v))[i]?).getD [])[k]?).getD 0))
            e.length := by
              apply sumRange_congr_lt
              intro i hi
              have hwi := hWget i hi
              have hpsi := psiVec_entry_aux a (((v₁ :: rest)[i]?).getD []) v₀
                (g (((v₁ :: rest)[i]?).getD [])) hlen k (hvi i hi) hv₀ hk
              rw [hwi, hpsi]
              simp only [Option.getD_some]
        _ = 0 := h0
    have hkey : ∀ k, k < hlen →
        (eHead e g (v₁ :: rest)) * (((v₀[k]?).getD 0)) +
        sumRange (fun m => ((((e.map fun x => a * x)[m]?).getD 0)) *
          (((((v₁ :: rest)[m]?).getD [])[k]?).getD 0))
          ((e.map fun x => a * x)).length = 0 := by
      intro k hk
      rw [List.length_map]
      have h0 := hident k hk
      have hexp : sumRange (fun i => (((e[i]?).getD 0)) *
            (a * (((((v₁ :: rest)[i]?).getD [])[k]?).getD 0) -
             (g (((v₁ :: rest)[i]?).getD [])) * (((v₀[k]?).getD 0))))
          e.length =
          sumRange (fun i => (((e[i]?).getD 0)) * (a * (((((v₁ :: rest)[i]?).getD [])[k]?).getD 0)))
            e.length -
          sumRange (fun i => (((e[i]?).getD 0)) * ((g (((v₁ :: rest)[i]?).getD [])) * (((v₀[k]?).getD 0))))
            e.length := by
        rw [← sumRange_sub_aux]
        apply sumRange_congr_lt
        intro i hi
        simp only [Int.mul_sub]
      rw [hexp] at h0
      have hfac1 : sumRange (fun i => (((e[i]?).getD 0)) * (a * (((((v₁ :: rest)[i]?).getD [])[k]?).getD 0)))
          e.length =
          a * sumRange (fun i => (((e[i]?).getD 0)) * (((((v₁ :: rest)[i]?).getD [])[k]?).getD 0))
            e.length := by
        have hc1 := sumRange_congr_lt
          (fun i => (((e[i]?).getD 0)) * (a * (((((v₁ :: rest)[i]?).getD [])[k]?).getD 0)))
          (fun i => a * ((((e[i]?).getD 0)) * (((((v₁ :: rest)[i]?).getD [])[k]?).getD 0)))
          e.length
          (fun i hi => by
            rw [← Int.mul_assoc, Int.mul_comm (((e[i]?).getD 0)) a, Int.mul_assoc])
        rw [hc1, sumRange_smul_left]
      have hfac2 : sumRange (fun i => (((e[i]?).getD 0)) * ((g (((v₁ :: rest)[i]?).getD [])) * (((v₀[k]?).getD 0))))
          e.length =
          (sumRange (fun i => (((e[i]?).getD 0)) * (g (((v₁ :: rest)[i]?).getD []))) e.length) *
            (((v₀[k]?).getD 0)) := by
        have hc2 := sumRange_congr_lt
          (fun i => (((e[i]?).getD 0)) * ((g (((v₁ :: rest)[i]?).getD [])) * (((v₀[k]?).getD 0))))
          (fun i => ((((e[i]?).getD 0)) * (g (((v₁ :: rest)[i]?).getD []))) * (((v₀[k]?).getD 0)))
          e.length
          (fun i hi => by rw [Int.mul_assoc])
        rw [hc2, sumRange_smul_right]
      rw [hfac1, hfac2] at h0
      have htail : sumRange (fun m => ((((e.map fun x => a * x)[m]?).getD 0)) *
          (((((v₁ :: rest)[m]?).getD [])[k]?).getD 0))
          e.length =
          a * sumRange (fun i => (((e[i]?).getD 0)) * (((((v₁ :: rest)[i]?).getD [])[k]?).getD 0))
            e.length := by
        have hc3 := sumRange_congr_lt
          (fun m => ((((e.map fun x => a * x)[m]?).getD 0)) * (((((v₁ :: rest)[m]?).getD [])[k]?).getD 0))
          (fun m => (a * (((e[m]?).getD 0))) * (((((v₁ :: rest)[m]?).getD [])[k]?).getD 0))
          e.length
          (fun m hm => by rw [map_mul_getD_aux])
        have hc4 := sumRange_congr_lt
          (fun m => (a * (((e[m]?).getD 0))) * (((((v₁ :: rest)[m]?).getD [])[k]?).getD 0))
          (fun m => a * ((((e[m]?).getD 0)) * (((((v₁ :: rest)[m]?).getD [])[k]?).getD 0)))
          e.length
          (fun m hm => by rw [Int.mul_assoc])
        rw [hc3, hc4, sumRange_smul_left]
      rw [htail]
      simp only [eHead]
      rw [Int.neg_mul]
      omega
    have hElen : ((- (sumRange (fun i => (((e[i]?).getD 0)) * (g (((v₁ :: rest)[i]?).getD [])))) e.length) ::
        (e.map fun x => a * x)).length = (v₀ :: v₁ :: rest).length := by
      simp [hEW]
    have hElin : lincomb ((- (sumRange (fun i => (((e[i]?).getD 0)) * (g (((v₁ :: rest)[i]?).getD [])))) e.length) ::
        (e.map fun x => a * x)) (v₀ :: v₁ :: rest) =
        zeroVec (((((v₀ :: v₁ :: rest)[0]?).getD []).length)) := by
      have hRlen : (zeroVec (((((v₀ :: v₁ :: rest)[0]?).getD []).length))).length = hlen := by
        rw [zeroVec_length_aux]
        simp [hv₀]
      have hLlen : (lincomb ((- (sumRange (fun i => (((e[i]?).getD 0)) * (g (((v₁ :: rest)[i]?).getD [])))) e.length) ::
          (e.map fun x => a * x)) (v₀ :: v₁ :: rest)).length = hlen := by
        have hll := lincomb_length_aux
          ((- (sumRange (fun i => (((e[i]?).getD 0)) * (g (((v₁ :: rest)[i]?).getD [])))) e.length) ::
            (e.map fun x => a * x)) (v₀ :: v₁ :: rest) hElen
        have himV : imatCols (v₀ :: v₁ :: rest) = hlen := by simp [imatCols, hv₀]
        omega
      apply List.ext_getElem?
      intro k
      by_cases hk : k < hlen
      · have hLc := lincomb_cons_entry_aux
            (-(sumRange (fun i => (((e[i]?).getD 0)) * (g (((v₁ :: rest)[i]?).getD [])))) e.length)
            (e.map fun x => a * x) v₀ (v₁ :: rest) hlen k hv₀ hvs hk
        have hR0 : ((zeroVec (((((v₀ :: v₁ :: rest)[0]?).getD []).length)))[k]?) =
            some (0 : Int) := by
          apply zeroVec_entry_aux
          have hrw : (((((v₀ :: v₁ :: rest)[0]?).getD []).length)) = hlen := by simp [hv₀]
          omega
        have hkk := hkey k hk
        rw [hLc, hR0]
        exact congrArg some hkk
      · have hn1 : (lincomb ((- (sumRange (fun i => (((e[i]?).getD 0)) * (g (((v₁ :: rest)[i]?).getD [])))) e.length) ::
            (e.map fun x => a * x)) (v₀ :: v₁ :: rest))[k]? = none := by
          apply List.getElem?_eq_none
          omega
        have hn2 : ((zeroVec (((((v₀ :: v₁ :: rest)[0]?).getD []).length)))[k]?) = none := by
          apply List.getElem?_eq_none
          omega
        rw [hn1, hn2]
    have hcon := hindep
      ((- (sumRange (fun i => (((e[i]?).getD 0)) * (g (((v₁ :: rest)[i]?).getD [])))) e.length) ::
        (e.map fun x => a * x)) hElen hElin
    have hzE : zeroVec (v₀ :: v₁ :: rest).length =
        0 :: zeroVec (v₁ :: rest).length := by
      simp [zeroVec, List.replicate_succ]
    rw [hzE] at hcon
    have hmap0 := (List.cons_eq_cons.mp hcon).2
    have hzero : ∀ m, m < e.length → (((e[m]?).getD 0)) = 0 := by
      intro m hm
      have h1 : ((((e.map fun x => a * x)[m]?).getD 0)) = a * (((e[m]?).getD 0)) :=
        map_mul_getD_aux _ _ _
      have hz1 : ((e.map fun x => a * x)[m]?) = ((zeroVec (v₁ :: rest).length)[m]?) := by
        rw [hmap0]
      have hz2 : ((((zeroVec (v₁ :: rest).length)[m]?).getD 0)) = 0 := by
        have he : ((zeroVec (v₁ :: rest).length)[m]?) = some (0 : Int) := by
          apply zeroVec_entry_aux
          omega
        rw [he]
        simp
      have h2 : ((((e.map fun x => a * x)[m]?).getD 0)) = 0 := by
        rw [hz1]
        exact hz2
      have h3 : a * (((e[m]?).getD 0)) = 0 := by omega
      rcases Int.mul_eq_zero.mp h3 with h | h
      · omega
      · exact h
    apply List.ext_getElem?
    intro j
    by_cases hj : j < e.length
    · have hg1 : (e[j]?) = some ((((e[j]?).getD 0))) := by
        cases hm : (e[j]?) with
        | none =>
          have hcon2 : ¬ j < e.length := by
            intro hlt
            have heq := List.getElem?_eq_getElem hlt
            rw [hm] at heq
            simp at heq
          omega
        | some x => simp
      have hg2 : ((((zeroVec (((v₁ :: rest).map fun v => psiVec a v v₀ (g v))).length)[j]?))) =
          some (0 : Int) := by
        apply zeroVec_entry_aux
        rw [List.length_map]
        omega
      have hg3 : (((e[j]?).getD 0)) = 0 := hzero j hj
      rw [hg1, hg3]
      exact hg2.symm
    · have hn1 : (e[j]?) = none := List.getElem?_eq_none (by omega)
      have hn2 : ((zeroVec (((v₁ :: rest).map fun v => psiVec a v v₀ (g v))).length)[j]?) = none := by
        apply List.getElem?_eq_none
        rw [zeroVec_length_aux, List.length_map]
        omega
      rw [hn1, hn2]

/-- Pivot existence: some expansion coefficient is nonzero,
    else `v₀ = 0⃗` contradicting independence. -/
theorem exists_nonzero_coeff_aux (U : IMat) (u₀ : List Int) (us : List (List Int))
    (hU : U = u₀ :: us)
    (v₀ : List Int) (vs : List (List Int)) (d : Int) (hd : d ≠ 0) (hlen : Nat)
    (hlenU : ∀ u ∈ U, u.length = hlen)
    (hlenV : ∀ v ∈ v₀ :: vs, v.length = hlen)
    (c₀ : List Int) (hc0len : c₀.length = U.length)
    (hc0 : vecSmul d v₀ = lincomb c₀ U)
    (hindep : independent (v₀ :: vs)) :
    ∃ j₀, j₀ < U.length ∧ ((c₀[j₀]?).getD 0) ≠ 0 := by
  by_cases hex : ∃ j₀, j₀ < U.length ∧ ((c₀[j₀]?).getD 0) ≠ 0
  · exact hex
  · exfalso
    have hall : ∀ j₀, j₀ < U.length → ((c₀[j₀]?).getD 0) = 0 := by
      intro j₀ hj
      by_cases h : ((c₀[j₀]?).getD 0) = 0
      · exact h
      · exact absurd ⟨j₀, hj, h⟩ hex
    have hcz : c₀ = zeroVec U.length := by
      apply List.ext_getElem?
      intro j
      by_cases hj : j < U.length
      · have h1 : (c₀[j]?) = some ((((c₀[j]?).getD 0))) := by
          cases hm : (c₀[j]?) with
          | none =>
            have hcon : ¬ j < c₀.length := by
              intro hlt
              have heq := List.getElem?_eq_getElem hlt
              rw [hm] at heq
              simp at heq
            omega
          | some x => simp
        have h2 : (((c₀[j]?).getD 0)) = 0 := hall j hj
        have h3 : ((zeroVec U.length)[j]?) = some (0 : Int) :=
          zeroVec_entry_aux _ _ hj
        rw [h1, h2]
        exact h3.symm
      · have hn1 : (c₀[j]?) = none := by
          apply List.getElem?_eq_none
          omega
        have hn2 : ((zeroVec U.length)[j]?) = none := by
          apply List.getElem?_eq_none
          rw [zeroVec_length_aux]
          omega
        rw [hn1, hn2]
    have hlc0 : lincomb c₀ U = zeroVec (((U[0]?).getD []).length) := by
      rw [hcz]
      exact lincomb_zeroVec_aux U
    have hU0 : ((((u₀ :: us)[0]?).getD []).length) = hlen := by
      have heq : ((((u₀ :: us)[0]?).getD [])) = u₀ := by simp
      rw [heq]
      exact hlenU u₀ (by simp [hU])
    have hdv0 : vecSmul d v₀ = zeroVec v₀.length := by
      have h1 : vecSmul d v₀ = zeroVec (((U[0]?).getD []).length) := by
        rw [hc0]
        exact hlc0
      have hv₀len : v₀.length = hlen := hlenV v₀ (by simp)
      have hlenU0 : ((((U)[0]?).getD []).length) = hlen := by
        rw [hU]
        exact hU0
      rw [hv₀len]
      rw [hlenU0] at h1
      exact h1
    have hv0z : v₀ = zeroVec hlen := by
      have hz := vecSmul_eq_zeroVec_aux d hd v₀ hdv0
      have hv₀len : v₀.length = hlen := hlenV v₀ (by simp)
      rw [hv₀len] at hz
      exact hz
    have h0 : ((((v₀ :: vs)[0]?).getD [])) = zeroVec hlen := by
      simp [hv0z]
    exact not_independent_of_mem_zeroVec_aux _ _ hlenV 0 (by simp) h0 hindep

theorem steinitz_bound_aux : ∀ (n : Nat) (U V : List (List Int)) (d : Int),
    d ≠ 0 → U.length = n →
    (hlen : Nat) → (∀ u ∈ U, u.length = hlen) → (∀ v ∈ V, v.length = hlen) →
    (∀ v ∈ V, ∃ coeffs, coeffs.length = U.length ∧ vecSmul d v = lincomb coeffs U) →
    independent V → V.length ≤ U.length := by
  intro n
  induction n with
  | zero =>
    intro U V d hd hUlen hlen hlenU hlenV hspan hindep
    have hUnil : U = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hUnil
    have hVnil : V = [] := by
      apply independent_torsion_nil_aux V hlen d hd hlenV _ hindep
      intro w hw
      obtain ⟨c, hclen, hceq⟩ := hspan w hw
      have hc0 : c = [] := List.eq_nil_of_length_eq_zero (by simpa using hclen)
      have hsm : vecSmul d w = [] := by
        rw [hceq, hc0]
        rfl
      have hwlen : w.length = 0 := by
        have hll := vecSmul_length_aux d w
        rw [hsm] at hll
        have hz : (([] : List Int).length) = 0 := by simp
        omega
      have hhlen : hlen = 0 := by
        have h1 := hlenV w hw
        omega
      have e0 : zeroVec hlen = [] := by
        simp [hhlen, zeroVec]
      rw [hsm, e0]
    rw [hVnil]
    simp
  | succ n ih =>
    intro U V d hd hUlen hlen hlenU hlenV hspan hindep
    cases hVcons : V with
    | nil => simp
    | cons v₀ vs =>
      subst hVcons
      obtain ⟨u₀, us, hUcons⟩ : ∃ u₀ us, U = u₀ :: us := by
        cases hU : U with
        | nil =>
          subst hU
          simp at hUlen
        | cons w₀ ws =>
          subst hU
          exact ⟨w₀, ws, rfl⟩
      subst hUcons
      obtain ⟨c₀, hc0len, hc0eq⟩ := hspan v₀ (by simp)
      obtain ⟨j₀, hj₀lt, hj₀ne⟩ := exists_nonzero_coeff_aux (u₀ :: us) u₀ us rfl
        v₀ vs d hd hlen hlenU hlenV c₀ hc0len hc0eq hindep
      have hv₀len : v₀.length = hlen := hlenV v₀ (by simp)
      have hvslen : ∀ s ∈ vs, s.length = hlen := fun s hs => hlenV s (by simp [hs])
      have hex : ∀ v ∈ vs, ∃ c, c.length = (u₀ :: us).length ∧
          vecSmul d v = lincomb c (u₀ :: us) := by
        intro v hv
        exact hspan v (by simp [hv])
      have hsk : ∀ v, ∃ c, (v ∈ vs →
          (c.length = (u₀ :: us).length ∧ vecSmul d v = lincomb c (u₀ :: us))) := by
        intro v
        by_cases hv : v ∈ vs
        · obtain ⟨c, hc⟩ := hex v hv
          exact ⟨c, fun _ => hc⟩
        · exact ⟨[], fun h => absurd h hv⟩
      obtain ⟨f, hf⟩ := Classical.skolem.mp hsk
      have hU'len : (((u₀ :: us).eraseIdx j₀)).length = n := by
        have h1 := eraseIdx_length_aux (u₀ :: us) j₀ hj₀lt
        omega
      have hU'uni : ∀ u ∈ ((u₀ :: us).eraseIdx j₀), u.length = hlen := by
        intro u hu
        have hmem : u ∈ (u₀ :: us) := List.mem_of_mem_eraseIdx hu
        exact hlenU u hmem
      have hWuni : ∀ w ∈ vs.map
          (fun v => psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0)),
          w.length = hlen := by
        intro w hw
        obtain ⟨v, hvmem, rfl⟩ := List.mem_map.mp hw
        rw [psiVec_length_aux]
        exact hlenV v (by simp [hvmem])
      have hWindep : independent
          (vs.map fun v => psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0)) := by
        have h0 := exchange_indep_aux v₀ vs (((c₀[j₀]?).getD 0)) hj₀ne hlen hv₀len hvslen
          hindep (fun v => (((f v)[j₀]?).getD 0))
        exact h0
      by_cases hU'eq : (((u₀ :: us).eraseIdx j₀)) = []
      · have htor : ∀ w ∈ vs.map
            (fun v => psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0)),
            vecSmul d w = zeroVec hlen := by
          intro w hw
          obtain ⟨v, hvmem, rfl⟩ := List.mem_map.mp hw
          have hvlen : v.length = hlen := hlenV v (by simp [hvmem])
          obtain ⟨hcvlen, hcveq⟩ := hf v hvmem
          have hplen : (psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0)).length =
              hlen := by
            rw [psiVec_length_aux]
            exact hvlen
          apply List.ext_getElem?
          intro k
          by_cases hk : k < hlen
          · have hL := vecSmul_entry_aux d
              (psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0)) k (by omega)
            have hP := psiVec_entry_aux (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0)
              hlen k hvlen hv₀len hk
            have hR : ((zeroVec hlen)[k]?) = some (0 : Int) :=
              zeroVec_entry_aux _ _ hk
            have htor0 := exchange_torsion_aux (u₀ :: us) j₀ hj₀lt
              (((c₀[j₀]?).getD 0)) d (((f v)[j₀]?).getD 0) hlen hlenU v v₀ hvlen hv₀len
              (f v) c₀ hcvlen hc0len hcveq hc0eq rfl rfl hU'eq k hk
            rw [hL, hR, hP]
            simp only [Option.getD_some]
            rw [htor0]
          · have hn1 : (vecSmul d
              (psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0)))[k]? = none := by
              apply List.getElem?_eq_none
              have hl2 : (vecSmul d
                (psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0))).length = hlen := by
                rw [vecSmul_length_aux]
                exact hplen
              omega
            have hn2 : ((zeroVec hlen)[k]?) = none := by
              apply List.getElem?_eq_none
              rw [zeroVec_length_aux]
              omega
            rw [hn1, hn2]
        have hWnil := independent_torsion_nil_aux _ hlen d hd hWuni htor hWindep
        have hvsnil : vs.length = 0 := by
          have h1 : (vs.map
            (fun v => psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0))).length = 0 := by
            simp [hWnil]
          have h2 : (vs.map
            (fun v => psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0))).length =
              vs.length := List.length_map _
          omega
        have hVn : (v₀ :: vs).length = 1 := by
          simp [hvsnil]
        have hUn : (u₀ :: us).length = 1 := by
          have h1 := eraseIdx_length_aux (u₀ :: us) j₀ hj₀lt
          rw [hU'eq] at h1
          have hz : (([] : List (List Int)).length) = 0 := by simp
          omega
        omega
      · have hWspan : ∀ w ∈ vs.map
            (fun v => psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0)),
            ∃ c', c'.length = (((u₀ :: us).eraseIdx j₀)).length ∧
              vecSmul d w = lincomb c' (((u₀ :: us).eraseIdx j₀)) := by
          intro w hw
          obtain ⟨v, hvmem, rfl⟩ := List.mem_map.mp hw
          obtain ⟨hcvlen, hcveq⟩ := hf v hvmem
          obtain ⟨c', hc'len, hc'eq⟩ := exchange_span_aux (u₀ :: us) j₀ hj₀lt
            (((c₀[j₀]?).getD 0)) d (((f v)[j₀]?).getD 0) hlen hlenU v v₀
            (hlenV v (by simp [hvmem])) hv₀len (f v) c₀ hcvlen hc0len hcveq hc0eq rfl rfl hU'eq
          exact ⟨c', hc'len, hc'eq⟩
        have hIH := ih (((u₀ :: us).eraseIdx j₀))
          (vs.map fun v => psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0))
          d hd hU'len hlen hU'uni hWuni hWspan hWindep
        have hWlen2 : (vs.map
          fun v => psiVec (((c₀[j₀]?).getD 0)) v v₀ (((f v)[j₀]?).getD 0)).length =
            vs.length := List.length_map _
        have hVl : (v₀ :: vs).length = vs.length + 1 := rfl
        omega

-- Revised denominator contract.
-- The fixed `d ^ U.length` form is refuted by `SteinitzCounterexample`
-- (U = [[1]], V = [[2]], d = 1 would need `1 = 2 * c` over `Int`).
-- Length premises use a well-typed `hlen : Nat` (the old
-- `(U[0]?).getD v.length` form is ill-typed: `getD` needs a `List Int`
-- default, not a `Nat`).

theorem steinitz_bound (U V : List (List Int)) (d : Int) (hd : d ≠ 0)
    (hlen : Nat)
    (hlenU : ∀ u ∈ U, u.length = hlen)
    (hlenV : ∀ v ∈ V, v.length = hlen)
    (hspan : ∀ v ∈ V, ∃ coeffs, coeffs.length = U.length ∧
      vecSmul d v = lincomb coeffs U)
    (hindep : independent V) :
    V.length ≤ U.length := by
  exact steinitz_bound_aux U.length U V d hd rfl hlen hlenU hlenV hspan hindep

/-- Scalar-multiple spanning for a member: `d • u` is a `lincomb` over `U`. -/
theorem smul_mem_span_aux (U : IMat) (hlen : Nat) (hU : ∀ u ∈ U, u.length = hlen)
    (d : Int) (u : List Int) (hu : u ∈ U) :
    ∃ c', c'.length = U.length ∧ vecSmul d u = lincomb c' U := by
  obtain ⟨idx, hidx, hUidx⟩ := List.getElem_of_mem hu
  obtain ⟨v0, rest, hUcons⟩ : ∃ v0 rest, U = v0 :: rest := by
    cases hU0 : U with
    | nil =>
      subst hU0
      simp at hu
    | cons w0 ws =>
      subst hU0
      exact ⟨w0, ws, rfl⟩
  subst hUcons
  refine ⟨(unitVec (v0 :: rest).length idx).map fun x => d * x,
    by simp [List.length_map, unitVec_length_aux], ?_⟩
  have hu_len : u.length = hlen := hU u hu
  have hv0 : v0.length = hlen := hU v0 (by simp)
  have himU : imatCols (v0 :: rest) = hlen := by simp [imatCols, hv0]
  have hunit := lincomb_unitVec_aux (v0 :: rest) hlen hU idx hidx
  have hUg : ((((v0 :: rest)[idx]?).getD [])) = u := by
    have h1 : (((v0 :: rest)[idx]?)) = some (((v0 :: rest)[idx]'hidx)) :=
      List.getElem?_eq_getElem hidx
    rw [h1, Option.getD_some]
    exact hUidx
  have hsumid : ∀ k, k < hlen →
      sumRange (fun i => (((unitVec (v0 :: rest).length idx)[i]?).getD 0) *
        (((((v0 :: rest)[i]?).getD [])[k]?).getD 0))
      (unitVec (v0 :: rest).length idx).length =
        (((((v0 :: rest)[idx]?).getD [])[k]?).getD 0) := by
    intro k hk
    have hjU : k < imatCols (v0 :: rest) := by omega
    have hLe := lincomb_entry_aux (unitVec (v0 :: rest).length idx) (v0 :: rest) k hjU
    have hRe : (((((v0 :: rest)[idx]?).getD [])[k]?)) =
        some ((((((v0 :: rest)[idx]?).getD [])[k]?).getD 0)) := by
      cases hm : (((((v0 :: rest)[idx]?).getD [])[k]?)) with
      | none =>
        have hcon : ¬ k < ((((v0 :: rest)[idx]?).getD []).length) := by
          intro hlt
          have heq := List.getElem?_eq_getElem hlt
          rw [hm] at heq
          simp at heq
        have hll : ((((v0 :: rest)[idx]?).getD []).length) = hlen := by
          have e1 : ((((v0 :: rest)[idx]?).getD [])) = ((v0 :: rest)[idx]'hidx) := by
            rw [List.getElem?_eq_getElem hidx, Option.getD_some]
          rw [e1]
          have hmem : ((v0 :: rest)[idx]'hidx) ∈ (v0 :: rest) := List.getElem_mem hidx
          exact hU _ hmem
        omega
      | some x => simp
    have hcong : (lincomb (unitVec (v0 :: rest).length idx) (v0 :: rest))[k]? =
        (((((v0 :: rest)[idx]?).getD [])[k]?)) := by
      rw [hunit]
    rw [hLe] at hcong
    rw [hRe] at hcong
    simpa using hcong
  have hconv : ∀ k, k < hlen →
      sumRange (fun i => ((((unitVec (v0 :: rest).length idx).map fun x => d * x)[i]?).getD 0) *
        (((((v0 :: rest)[i]?).getD [])[k]?).getD 0))
      (((unitVec (v0 :: rest).length idx).map fun x => d * x)).length =
        d * (((((v0 :: rest)[idx]?).getD [])[k]?).getD 0) := by
    intro k hk
    have s1 := sumRange_congr_lt
      (fun i => ((((unitVec (v0 :: rest).length idx).map fun x => d * x)[i]?).getD 0) *
        (((((v0 :: rest)[i]?).getD [])[k]?).getD 0))
      (fun i => (d * ((((unitVec (v0 :: rest).length idx)[i]?).getD 0))) *
        (((((v0 :: rest)[i]?).getD [])[k]?).getD 0))
      (((unitVec (v0 :: rest).length idx).map fun x => d * x)).length
      (fun i hi => by rw [map_mul_getD_aux])
    have s2 := sumRange_congr_lt
      (fun i => (d * ((((unitVec (v0 :: rest).length idx)[i]?).getD 0))) *
        (((((v0 :: rest)[i]?).getD [])[k]?).getD 0))
      (fun i => d * (((((unitVec (v0 :: rest).length idx)[i]?).getD 0)) *
        (((((v0 :: rest)[i]?).getD [])[k]?).getD 0)))
      (((unitVec (v0 :: rest).length idx).map fun x => d * x)).length
      (fun i hi => by rw [Int.mul_assoc])
    have s3 : sumRange
        (fun i => d * (((((unitVec (v0 :: rest).length idx)[i]?).getD 0)) *
          (((((v0 :: rest)[i]?).getD [])[k]?).getD 0)))
        (((unitVec (v0 :: rest).length idx).map fun x => d * x)).length =
        d * sumRange (fun i => (((unitVec (v0 :: rest).length idx)[i]?).getD 0) *
          (((((v0 :: rest)[i]?).getD [])[k]?).getD 0))
        (unitVec (v0 :: rest).length idx).length := by
      rw [sumRange_smul_left]
      have hlenEq : ((((unitVec (v0 :: rest).length idx).map fun x => d * x)).length) =
          ((unitVec (v0 :: rest).length idx)).length := List.length_map _
      rw [hlenEq]
    rw [s1, s2, s3]
    congr 1
    exact hsumid k hk
  have hlenL : (vecSmul d u).length = hlen := by
    rw [vecSmul_length_aux]
    exact hu_len
  have hlenR : (lincomb ((unitVec (v0 :: rest).length idx).map fun x => d * x)
      (v0 :: rest)).length = hlen := by
    have hcc : (((unitVec (v0 :: rest).length idx).map fun x => d * x)).length =
        (v0 :: rest).length := by
      simp [List.length_map, unitVec_length_aux]
    have hll := lincomb_length_aux _ _ hcc
    omega
  apply List.ext_getElem?
  intro k
  by_cases hk : k < hlen
  · have hL := vecSmul_entry_aux d u k (by omega)
    have hR := lincomb_entry_aux
      ((unitVec (v0 :: rest).length idx).map fun x => d * x) (v0 :: rest) k (by omega)
    have hinner : d * (((u[k]?).getD 0)) =
        sumRange (fun i => ((((unitVec (v0 :: rest).length idx).map fun x => d * x)[i]?).getD 0) *
          (((((v0 :: rest)[i]?).getD [])[k]?).getD 0))
        (((unitVec (v0 :: rest).length idx).map fun x => d * x)).length := by
      have e1 : d * (((u[k]?).getD 0)) =
          d * (((((v0 :: rest)[idx]?).getD [])[k]?).getD 0) := by
        rw [hUg]
      rw [e1]
      exact (hconv k hk).symm
    rw [hL, hR]
    exact congrArg some hinner
  · have hn1 : (vecSmul d u)[k]? = none := by
      apply List.getElem?_eq_none
      omega
    have hn2 : (lincomb ((unitVec (v0 :: rest).length idx).map fun x => d * x)
        (v0 :: rest))[k]? = none := by
      apply List.getElem?_eq_none
      omega
    rw [hn1, hn2]

theorem steinitz_span_eq (U V : List (List Int)) (d : Int) (hd : d ≠ 0)
    (hlen : Nat)
    (hlenU : ∀ u ∈ U, u.length = hlen)
    (hlenV : ∀ v ∈ V, v.length = hlen)
    (hcard : U.length ≤ V.length)
    (hspanV : ∀ v ∈ V, ∃ coeffs, coeffs.length = U.length ∧
      vecSmul d v = lincomb coeffs U)
    (hindepV : independent V) :
    ∀ u ∈ U, ∃ d' coeffs, d' ≠ 0 ∧ coeffs.length = V.length ∧
      vecSmul d' u = lincomb coeffs V := by
  have hb1 := steinitz_bound U V d hd hlen hlenU hlenV hspanV hindepV
  have hUVeq : U.length = V.length := by omega
  intro u hu
  by_cases hex : ∃ d' coeffs, d' ≠ 0 ∧ coeffs.length = V.length ∧
      vecSmul d' u = lincomb coeffs V
  · exact hex
  · exfalso
    have hu_len : u.length = hlen := hlenU u hu
    have hVne : V ≠ [] := by
      intro hcon
      subst hcon
      have h0 : U.length = 0 := by
        have hz : (([] : List (List Int)).length) = 0 := by simp
        omega
      have hUnil : U = [] := List.eq_nil_of_length_eq_zero h0
      subst hUnil
      simp at hu
    cases hV : V with
    | nil =>
      subst hV
      exact absurd rfl hVne
    | cons v₁ vsV =>
      subst hV
      have hv1 : v₁.length = hlen := hlenV v₁ (by simp)
      have himV : imatCols (v₁ :: vsV) = hlen := by simp [imatCols, hv1]
      have hV0len : (((((v₁ :: vsV)[0]?).getD []).length)) = hlen := by
        have e1 : ((((v₁ :: vsV)[0]?).getD [])) = v₁ := by simp
        rw [e1]
        exact hv1
      have hlenW : ∀ w ∈ u :: v₁ :: vsV, w.length = hlen := by
        intro w hw
        simp at hw
        cases hw with
        | inl h =>
          rw [h]
          exact hu_len
        | inr hv => exact hlenV w (by simp [hv])
      have hspanW : ∀ w ∈ u :: v₁ :: vsV, ∃ coeffs, coeffs.length = U.length ∧
          vecSmul d w = lincomb coeffs U := by
        intro w hw
        simp at hw
        cases hw with
        | inl h =>
          rw [h]
          exact smul_mem_span_aux U hlen hlenU d u hu
        | inr hv => exact hspanV w (by simp [hv])
      have hindepW : independent (u :: v₁ :: vsV) := by
        intro e helenE hlinE
        obtain ⟨e₀, et, hecons⟩ : ∃ e₀ et, e = e₀ :: et := by
          cases he : e with
          | nil =>
            subst he
            simp at helenE
          | cons a as =>
            subst he
            exact ⟨a, as, rfl⟩
        subst hecons
        have hetlen : et.length = (v₁ :: vsV).length := by
          have h1 : (e₀ :: et).length = et.length + 1 := rfl
          have h2 : (u :: v₁ :: vsV).length = (v₁ :: vsV).length + 1 := rfl
          omega
        by_cases ht0 : e₀ = 0
        · subst ht0
          have hEt0 : lincomb et (v₁ :: vsV) =
              zeroVec (((v₁ :: vsV)[0]?).getD []).length := by
            have hLlen : (lincomb et (v₁ :: vsV)).length = hlen := by
              have hll := lincomb_length_aux et (v₁ :: vsV) hetlen
              omega
            have hRlen : (zeroVec (((v₁ :: vsV)[0]?).getD []).length).length = hlen := by
              rw [zeroVec_length_aux]
              exact hV0len
            apply List.ext_getElem?
            intro k
            by_cases hk : k < hlen
            · have hLc := lincomb_cons_entry_aux 0 et u (v₁ :: vsV) hlen k hu_len
                (fun s hs => hlenV s (by simp [hs])) hk
              have hR0 : ((zeroVec (((v₁ :: vsV)[0]?).getD []).length)[k]?) =
                  some (0 : Int) := by
                apply zeroVec_entry_aux
                rw [hV0len]
                exact hk
              have hzero : (0 : Int) * (((u[k]?).getD 0)) +
                  sumRange (fun m => (((et[m]?).getD 0)) *
                    (((((v₁ :: vsV)[m]?).getD [])[k]?).getD 0)) et.length = 0 := by
                have hlinEk : (lincomb (0 :: et) (u :: v₁ :: vsV))[k]? =
                    ((zeroVec (((u :: v₁ :: vsV)[0]?).getD []).length)[k]?) := by
                  rw [hlinE]
                rw [hLc] at hlinEk
                have hzU : ((zeroVec (((u :: v₁ :: vsV)[0]?).getD []).length)[k]?) =
                    some (0 : Int) := by
                  apply zeroVec_entry_aux
                  have eU : ((((u :: v₁ :: vsV)[0]?).getD [])) = u := by simp
                  rw [eU]
                  omega
                rw [hzU] at hlinEk
                simpa using hlinEk
              have hsum0 : sumRange (fun m => (((et[m]?).getD 0)) *
                  (((((v₁ :: vsV)[m]?).getD [])[k]?).getD 0)) et.length = 0 := by
                have hz : (0 : Int) * (((u[k]?).getD 0)) = 0 := Int.zero_mul _
                omega
              have hLe := lincomb_entry_aux et (v₁ :: vsV) k (by omega)
              rw [hLe, hR0, hsum0]
            · have hn1 : (lincomb et (v₁ :: vsV))[k]? = none := by
                apply List.getElem?_eq_none
                omega
              have hn2 : ((zeroVec (((v₁ :: vsV)[0]?).getD []).length)[k]?) = none := by
                apply List.getElem?_eq_none
                omega
              rw [hn1, hn2]
          have het0 : et = zeroVec (v₁ :: vsV).length := hindepV et hetlen hEt0
          simp [het0, zeroVec, List.replicate_succ]
        · have hd'ne : -e₀ ≠ 0 := by
            intro h
            apply ht0
            have h2 : - -e₀ = -0 := congrArg Neg.neg h
            simp at h2
            exact h2
          have hEtV : vecSmul (-e₀) u = lincomb et (v₁ :: vsV) := by
            have hLlen2 : (vecSmul (-e₀) u).length = hlen := by
              rw [vecSmul_length_aux]
              exact hu_len
            have hRlen2 : (lincomb et (v₁ :: vsV)).length = hlen := by
              have hll := lincomb_length_aux et (v₁ :: vsV) hetlen
              omega
            apply List.ext_getElem?
            intro k
            by_cases hk : k < hlen
            · have hLc := lincomb_cons_entry_aux e₀ et u (v₁ :: vsV) hlen k hu_len
                (fun s hs => hlenV s (by simp [hs])) hk
              have hR := lincomb_entry_aux et (v₁ :: vsV) k (by omega)
              have hL := vecSmul_entry_aux (-e₀) u k (by omega)
              have hlinEk : (e₀ * (((u[k]?).getD 0)) +
                  sumRange (fun m => (((et[m]?).getD 0)) *
                    (((((v₁ :: vsV)[m]?).getD [])[k]?).getD 0)) et.length) = 0 := by
                have hlinEk0 : (lincomb (e₀ :: et) (u :: v₁ :: vsV))[k]? =
                    ((zeroVec (((u :: v₁ :: vsV)[0]?).getD []).length)[k]?) := by
                  rw [hlinE]
                rw [hLc] at hlinEk0
                have hzU : ((zeroVec (((u :: v₁ :: vsV)[0]?).getD []).length)[k]?) =
                    some (0 : Int) := by
                  apply zeroVec_entry_aux
                  have eU : ((((u :: v₁ :: vsV)[0]?).getD [])) = u := by simp
                  rw [eU]
                  omega
                rw [hzU] at hlinEk0
                simpa using hlinEk0
              have hgoal : (-e₀) * (((u[k]?).getD 0)) =
                  sumRange (fun m => (((et[m]?).getD 0)) *
                    (((((v₁ :: vsV)[m]?).getD [])[k]?).getD 0)) et.length := by
                rw [Int.neg_mul]
                omega
              rw [hL, hR]
              exact congrArg some hgoal
            · have hn1 : (vecSmul (-e₀) u)[k]? = none := by
                apply List.getElem?_eq_none
                omega
              have hn2 : (lincomb et (v₁ :: vsV))[k]? = none := by
                apply List.getElem?_eq_none
                omega
              rw [hn1, hn2]
          exact absurd ⟨-e₀, et, hd'ne, hetlen, hEtV⟩ hex
      have hb2 := steinitz_bound U (u :: v₁ :: vsV) d hd hlen hlenU hlenW hspanW hindepW
      have hcons : (u :: v₁ :: vsV).length = (v₁ :: vsV).length + 1 := rfl
      omega

-- Certificate checker. When r = 0, C·A = d4·M is replaced by M = 0
-- (C is n×0 and A is 0×n there; w=0,1 have M=0).
def checkWitness (M : IMat) (S : List Nat) (T C N K Gsel Kg : IMat)
    (d1 d4 d3 dg : Int) (r k : Nat) : Bool :=
  decide (S.length = r)
  && decide (d1 ≠ 0) && decide (d4 ≠ 0) && decide (d3 ≠ 0) && decide (dg ≠ 0)
  && (imatMul (imatRowsOf M S) T == imatSmul d1 (imatEye r))
  && ((imatMul C (imatRowsOf M S) == imatSmul d4 M) ||
      (decide (r = 0) && (M == imatZero (imatRows M) (imatCols M))))
  && (imatMul M N == imatZero (imatRows M) k)
  && (imatMul K N == imatSmul d3 (imatEye k))
  && (imatMul Kg Gsel == imatSmul dg (imatEye k))
  && decide (r + k = imatRows M)
