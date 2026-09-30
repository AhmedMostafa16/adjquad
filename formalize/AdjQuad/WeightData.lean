import AdjQuad.Poly
import AdjQuad.Witness
import AdjQuad.Deriv

-- Weight infrastructure: monoW (mirrors mono_w in check_s6.py),
-- dmat (derivative matrix), s6count (Hilbert coefficient), predNull.

/-- All exponent tuples (e0,e1,e2,e3,e4,e5) of (8,5,3,2,1,1)-weight w,
    in the same nesting order as `check_s6.mono_w` (e0 outermost, e4 innermost). -/
def monoW (w : Nat) : List Exp :=
  (List.range (w / 8 + 1)).flatMap fun e0 =>
  let r0 := w - 8 * e0
  (List.range (r0 / 5 + 1)).flatMap fun e1 =>
  let r1 := r0 - 5 * e1
  (List.range (r1 / 3 + 1)).flatMap fun e2 =>
  let r2 := r1 - 3 * e2
  (List.range (r2 / 2 + 1)).flatMap fun e3 =>
  let rem := r2 - 2 * e3
  (List.range (rem + 1)).map fun e4 => [e0, e1, e2, e3, e4, rem - e4]

/-- Single-monomial polynomial (basis vector). -/
def basisPoly (e : Exp) : Poly := [((1 : Rat), e)]

/-- Numerators of the first matching coefficients in the `dom` exponent basis.
    This is not a rational-coordinate map in general. It is lossless on
    integral D-images; `Generation.D_mono_int` proves their integrality.
    `mats_match` independently checks the resulting matrix convention. -/
def coordIn (dom : List Exp) (p : Poly) : List Int :=
  dom.map fun e =>
    ((p.find? (fun m => m.2 == e)).map (fun m => m.1.num)).getD 0

/-- Columns of M_w: coordinates of D-images of basis monomials. -/
def dmatCols (w : Nat) : IMat :=
  let dom := monoW w
  (List.range dom.length).map fun j =>
    coordIn dom (D (basisPoly ((dom[j]?).getD [0,0,0,0,0,0])))

/-- The n×n integer derivative matrix M_w = D|_{V_w}, row-major.
    `dmatCols` is column-major; `IMat` is row-major, hence the transpose. -/
def dmat (w : Nat) : IMat := imatTranspose (dmatCols w)

/-- `s6count w` = number of 6-generated subalgebra monomials of weight w,
    where generators have weights (1,1,6,4,14,24). Mirrors `check_s6.s6`. -/
def s6count (w : Nat) : Nat :=
  let step (dp : List Nat) (coin : Nat) : List Nat :=
    (List.range (w + 1)).map fun s =>
      (List.range (s / coin + 1)).foldl
        (fun acc e => acc + ((dp[s - e * coin]?).getD 0)) 0
  let dp0 : List Nat := (List.range (w + 1)).map fun s => if s == 0 then 1 else 0
  let dp1 := step (step dp0 1) 1
  let dp2 := step (step (step (step dp1 6) 4) 14) 24
  (dp2[w]?).getD 0

/-- Predicted nullity at weight w = s6(w) - s6(w-28) (weight-28 syzygy). -/
def predNull (w : Nat) : Nat :=
  if w < 28 then s6count w else s6count w - s6count (w - 28)

/-- Number of monomials of weight w = |monoW w|, i.e. the dimension of V_w. -/
def nMonos (w : Nat) : Nat := (monoW w).length

-- Anchor theorems (native_decide, verified by computation)
theorem monoW_0 : (monoW 0).length = 1  := by native_decide
theorem monoW_1 : (monoW 1).length = 2  := by native_decide
theorem monoW_2 : (monoW 2).length = 4  := by native_decide
theorem monoW_4 : (monoW 4).length = 11 := by native_decide
theorem monoW_6 : (monoW 6).length = 25 := by native_decide

theorem predNull_23 : predNull 23 = 188 := by native_decide
theorem predNull_24 : predNull 24 = 213 := by native_decide
theorem predNull_25 : predNull 25 = 238 := by native_decide

-- Weight infrastructure: every term of a normalized/combined/mapped
-- polynomial comes from the input, and D preserves the
-- (8,5,3,2,1,1)-weight on monomials.

theorem combine_mem_exp (p : Poly) (x : Exp) :
    x ∈ (combine p).map (·.2) → x ∈ p.map (·.2) := by
  induction p with
  | nil => simp [combine]
  | cons m rest ih =>
    intro h
    simp only [combine] at h
    by_cases h0 : m.1 = 0
    · have e : insertCombine m (combine rest) = combine rest := by
        unfold insertCombine
        simp [h0]
      rw [e] at h
      exact List.mem_cons_of_mem m.2 (ih h)
    · by_cases hmem : m.2 ∈ (combine rest).map (·.2)
      · have e : insertCombine m (combine rest) =
            insertCombineGo m (combine rest) := by
          unfold insertCombine
          simp [h0, hmem]
        rw [e] at h
        have hdis := insertCombineGo_mem m (combine rest) x h
        rcases hdis with h1 | h2
        · exact List.mem_cons_of_mem m.2 (ih h1)
        · rw [h2]
          simp
      · have e : insertCombine m (combine rest) = m :: combine rest := by
          unfold insertCombine
          simp [h0, hmem]
        rw [e] at h
        have hmem2 : x = m.2 ∨ x ∈ (combine rest).map (·.2) := by
          simpa only [List.map_cons, List.mem_cons] using h
        rcases hmem2 with rfl | h1
        · simp
        · exact List.mem_cons_of_mem m.2 (ih h1)

theorem normalize_mem_exp (p : Poly) (x : Exp) :
    x ∈ (normalize p).map (·.2) → x ∈ p.map (·.2) := by
  intro h
  unfold normalize at h
  have hperm := sortPoly_perm (combine p)
  have hmap : List.Perm (((sortPoly (combine p))).map (·.2)) ((combine p).map (·.2)) :=
    List.Perm.map (·.2) hperm
  have hmem : x ∈ (combine p).map (·.2) := (List.Perm.mem_iff hmap).mp h
  exact combine_mem_exp _ _ hmem

theorem polyAdd_mem_exp (p q : Poly) (x : Exp) :
    x ∈ (polyAdd p q).map (·.2) → x ∈ p.map (·.2) ∨ x ∈ q.map (·.2) := by
  intro h
  unfold polyAdd at h
  have hmem := normalize_mem_exp _ _ h
  rw [List.map_append] at hmem
  exact (List.mem_append.mp hmem)

theorem polyMul_mem_exp (p q : Poly) (x : Exp) :
    x ∈ (polyMul p q).map (·.2) →
    ∃ e1 ∈ p.map (·.2), ∃ e2 ∈ q.map (·.2), x = addExp e1 e2 := by
  intro h
  unfold polyMul at h
  have hmem := normalize_mem_exp _ _ h
  rw [List.map_flatMap] at hmem
  obtain ⟨m1, hm1, hx1⟩ := List.mem_flatMap.mp hmem
  obtain ⟨y, hy_mem, hy_eq⟩ := List.mem_map.mp hx1
  obtain ⟨m2, hm2, heq⟩ := List.mem_map.mp hy_mem
  obtain ⟨c1, e1⟩ := m1
  obtain ⟨c2, e2⟩ := m2
  refine ⟨e1, List.mem_map.mpr ⟨(c1, e1), hm1, rfl⟩, e2,
    List.mem_map.mpr ⟨(c2, e2), hm2, rfl⟩, ?_⟩
  simp only [mulMono_correct] at heq
  rw [← hy_eq, ← heq]

theorem partialDeriv_mem_exp (i : Fin 6) (p : Poly) (x : Exp) :
    x ∈ (partialDeriv i p).map (·.2) →
    ∃ m ∈ p, ∃ c', derivMono i m = some (c', x) := by
  intro h
  unfold partialDeriv at h
  have hmem := normalize_mem_exp _ _ h
  rw [List.map_filterMap] at hmem
  obtain ⟨m, hm, hfm⟩ := List.mem_filterMap.mp hmem
  cases hdm : derivMono i m with
  | none => simp [hdm] at hfm
  | some y =>
    obtain ⟨c', e'⟩ := y
    rw [hdm, Option.map_some] at hfm
    have heq : e' = x := Option.some_inj.mp hfm
    subst heq
    exact ⟨m, hm, c', hdm⟩

theorem expSix (e : Exp) (h : e.length = 6) :
    ∃ a b c d e' f, e = [a,b,c,d,e',f] := by
  match e with
  | [a,b,c,d,e',f] => exact ⟨_,_,_,_,_,_,rfl⟩
  | [] => simp only [List.length_nil] at h; omega
  | [_] => simp only [List.length_cons, List.length_nil] at h; omega
  | [_,_] => simp only [List.length_cons, List.length_nil] at h; omega
  | [_,_,_] => simp only [List.length_cons, List.length_nil] at h; omega
  | [_,_,_,_] => simp only [List.length_cons, List.length_nil] at h; omega
  | [_,_,_,_,_] => simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
    simp only [List.length_cons] at h; omega

theorem expWeight_six (a b c d e f : Nat) :
    expWeight [a,b,c,d,e,f] = 8*a+5*b+3*c+2*d+e+f := by
  unfold expWeight weights
  simp

theorem addExp_weight (e1 e2 : Exp) (h1 : e1.length = 6) (h2 : e2.length = 6) :
    expWeight (addExp e1 e2) = expWeight e1 + expWeight e2 := by
  obtain ⟨a1,b1,c1,d1,g1,f1,rfl⟩ := expSix e1 h1
  obtain ⟨a2,b2,c2,d2,g2,f2,rfl⟩ := expSix e2 h2
  show expWeight [a1+a2,b1+b2,c1+c2,d1+d2,g1+g2,f1+f2] = _
  rw [expWeight_six, expWeight_six, expWeight_six]
  omega

theorem monoW_mem_six (w : Nat) (e : Exp) (h : e ∈ monoW w) : e.length = 6 := by
  unfold monoW at h
  simp only [List.mem_flatMap, List.mem_map] at h
  obtain ⟨e0, -, e1, -, e2, -, e3, -, e4, -, rfl⟩ := h
  rfl

theorem monoW_mem_weight (w : Nat) (e : Exp) (h : e ∈ monoW w) : expWeight e = w := by
  unfold monoW at h
  simp only [List.mem_flatMap, List.mem_map] at h
  obtain ⟨e0, h0, e1, h1, e2, h2, e3, h3, e4, h4, rfl⟩ := h
  simp only [List.mem_range] at h0 h1 h2 h3 h4
  rw [expWeight_six]
  omega

theorem Dsum0_weight (cc : Rat) (e : Exp) (h : e.length = 6) (m : Mono) :
    m ∈ polyMul (polyMul a1 a2) (partialDeriv ⟨0, by decide⟩ [(cc, e)]) →
    expWeight m.2 = expWeight e := by
  obtain ⟨a,b,c,d,e',f,rfl⟩ := expSix e h
  have hv1 : varExp 1 = [0,1,0,0,0,0] := rfl
  have hv2 : varExp 2 = [0,0,1,0,0,0] := rfl
  intro hm
  have hm2 : m.2 ∈ (polyMul (polyMul a1 a2)
      (partialDeriv ⟨0, by decide⟩ [(cc, [a,b,c,d,e',f])])).map (·.2) :=
    List.mem_map.mpr ⟨m, hm, rfl⟩
  obtain ⟨e12, he12mem, eP, hePmem, hmeq⟩ := polyMul_mem_exp _ _ _ hm2
  obtain ⟨ea, haemem, eb, hebmem, he12eq⟩ := polyMul_mem_exp _ _ _ he12mem
  have hea : ea = [0,1,0,0,0,0] := by
    have h1 : ea ∈ ([(1, varExp 1)] : Poly).map (·.2) := haemem
    simp at h1
    rw [h1, hv1]
  have heb : eb = [0,0,1,0,0,0] := by
    have h1 : eb ∈ ([(1, varExp 2)] : Poly).map (·.2) := hebmem
    simp at h1
    rw [h1, hv2]
  obtain ⟨m', hm'mem, c', hdm⟩ := partialDeriv_mem_exp _ _ _ hePmem
  have hm'eq : m' = (cc, [a,b,c,d,e',f]) := by simpa using hm'mem
  rw [hm'eq] at hdm
  cases ha : a with
  | zero =>
    subst ha
    have hdn : derivMono (⟨0, by decide⟩ : Fin 6) (cc, [0,b,c,d,e',f]) = none := by
      unfold derivMono
      rfl
    rw [hdn] at hdm
    cases hdm
  | succ n =>
    subst ha
    have hdmc : derivMono (⟨0, by decide⟩ : Fin 6) (cc, [n+1,b,c,d,e',f]) =
        some ((cc * (((n+1 : Nat) : Rat))), [n,b,c,d,e',f]) := by
      unfold derivMono
      simp
    rw [hdmc] at hdm
    have he2 : eP = [n,b,c,d,e',f] := by
      have hp := congrArg Prod.snd (Option.some_inj.mp hdm)
      exact hp.symm
    have he12len : e12.length = 6 := by
      rw [he12eq, hea, heb]
      rfl
    have hePlen : eP.length = 6 := by
      rw [he2]
      rfl
    have hadd := addExp_weight e12 eP he12len hePlen
    rw [hmeq, hadd]
    have heaW : expWeight ([0,1,0,0,0,0] : Exp) = 5 := by
      rw [expWeight_six]
    have hebW : expWeight ([0,0,1,0,0,0] : Exp) = 3 := by
      rw [expWeight_six]
    have he12W : expWeight e12 = 8 := by
      have hadd12 := addExp_weight ea eb (by rw [hea]; rfl) (by rw [heb]; rfl)
      rw [he12eq, hadd12, hea, heb, heaW, hebW]
    rw [he12W, he2, expWeight_six, expWeight_six]
    omega

theorem Dsum1_weight (cc : Rat) (e : Exp) (h : e.length = 6) (m : Mono) :
    m ∈ polyMul (polyMul a2 a3) (partialDeriv ⟨1, by decide⟩ [(cc, e)]) →
    expWeight m.2 = expWeight e := by
  obtain ⟨a,b,c,d,e',f,rfl⟩ := expSix e h
  have hv2 : varExp 2 = [0,0,1,0,0,0] := rfl
  have hv3 : varExp 3 = [0,0,0,1,0,0] := rfl
  intro hm
  have hm2 : m.2 ∈ (polyMul (polyMul a2 a3)
      (partialDeriv ⟨1, by decide⟩ [(cc, [a,b,c,d,e',f])])).map (·.2) :=
    List.mem_map.mpr ⟨m, hm, rfl⟩
  obtain ⟨e12, he12mem, eP, hePmem, hmeq⟩ := polyMul_mem_exp _ _ _ hm2
  obtain ⟨ea, haemem, eb, hebmem, he12eq⟩ := polyMul_mem_exp _ _ _ he12mem
  have hea : ea = [0,0,1,0,0,0] := by
    have h1 : ea ∈ ([(1, varExp 2)] : Poly).map (·.2) := haemem
    simp at h1
    rw [h1, hv2]
  have heb : eb = [0,0,0,1,0,0] := by
    have h1 : eb ∈ ([(1, varExp 3)] : Poly).map (·.2) := hebmem
    simp at h1
    rw [h1, hv3]
  obtain ⟨m', hm'mem, c', hdm⟩ := partialDeriv_mem_exp _ _ _ hePmem
  have hm'eq : m' = (cc, [a,b,c,d,e',f]) := by simpa using hm'mem
  rw [hm'eq] at hdm
  cases hb : b with
  | zero =>
    subst hb
    have hdn : derivMono (⟨1, by decide⟩ : Fin 6) (cc, [a,0,c,d,e',f]) = none := by
      unfold derivMono
      rfl
    rw [hdn] at hdm
    cases hdm
  | succ n =>
    subst hb
    have hdmc : derivMono (⟨1, by decide⟩ : Fin 6) (cc, [a,n+1,c,d,e',f]) =
        some ((cc * (((n+1 : Nat) : Rat))), [a,n,c,d,e',f]) := by
      unfold derivMono
      simp
    rw [hdmc] at hdm
    have he2 : eP = [a,n,c,d,e',f] := by
      have hp := congrArg Prod.snd (Option.some_inj.mp hdm)
      exact hp.symm
    have he12len : e12.length = 6 := by
      rw [he12eq, hea, heb]
      rfl
    have hePlen : eP.length = 6 := by
      rw [he2]
      rfl
    have hadd := addExp_weight e12 eP he12len hePlen
    rw [hmeq, hadd]
    have heaW : expWeight ([0,0,1,0,0,0] : Exp) = 3 := by
      rw [expWeight_six]
    have hebW : expWeight ([0,0,0,1,0,0] : Exp) = 2 := by
      rw [expWeight_six]
    have he12W : expWeight e12 = 5 := by
      have hadd12 := addExp_weight ea eb (by rw [hea]; rfl) (by rw [heb]; rfl)
      rw [he12eq, hadd12, hea, heb, heaW, hebW]
    rw [he12W, he2, expWeight_six, expWeight_six]
    omega

theorem Dsum2_weight (cc : Rat) (e : Exp) (h : e.length = 6) (m : Mono) :
    m ∈ polyMul (polyMul a3 a4) (partialDeriv ⟨2, by decide⟩ [(cc, e)]) →
    expWeight m.2 = expWeight e := by
  obtain ⟨a,b,c,d,e',f,rfl⟩ := expSix e h
  have hv3 : varExp 3 = [0,0,0,1,0,0] := rfl
  have hv4 : varExp 4 = [0,0,0,0,1,0] := rfl
  intro hm
  have hm2 : m.2 ∈ (polyMul (polyMul a3 a4)
      (partialDeriv ⟨2, by decide⟩ [(cc, [a,b,c,d,e',f])])).map (·.2) :=
    List.mem_map.mpr ⟨m, hm, rfl⟩
  obtain ⟨e12, he12mem, eP, hePmem, hmeq⟩ := polyMul_mem_exp _ _ _ hm2
  obtain ⟨ea, haemem, eb, hebmem, he12eq⟩ := polyMul_mem_exp _ _ _ he12mem
  have hea : ea = [0,0,0,1,0,0] := by
    have h1 : ea ∈ ([(1, varExp 3)] : Poly).map (·.2) := haemem
    simp at h1
    rw [h1, hv3]
  have heb : eb = [0,0,0,0,1,0] := by
    have h1 : eb ∈ ([(1, varExp 4)] : Poly).map (·.2) := hebmem
    simp at h1
    rw [h1, hv4]
  obtain ⟨m', hm'mem, c', hdm⟩ := partialDeriv_mem_exp _ _ _ hePmem
  have hm'eq : m' = (cc, [a,b,c,d,e',f]) := by simpa using hm'mem
  rw [hm'eq] at hdm
  cases hc : c with
  | zero =>
    subst hc
    have hdn : derivMono (⟨2, by decide⟩ : Fin 6) (cc, [a,b,0,d,e',f]) = none := by
      unfold derivMono
      rfl
    rw [hdn] at hdm
    cases hdm
  | succ n =>
    subst hc
    have hdmc : derivMono (⟨2, by decide⟩ : Fin 6) (cc, [a,b,n+1,d,e',f]) =
        some ((cc * (((n+1 : Nat) : Rat))), [a,b,n,d,e',f]) := by
      unfold derivMono
      simp
    rw [hdmc] at hdm
    have he2 : eP = [a,b,n,d,e',f] := by
      have hp := congrArg Prod.snd (Option.some_inj.mp hdm)
      exact hp.symm
    have he12len : e12.length = 6 := by
      rw [he12eq, hea, heb]
      rfl
    have hePlen : eP.length = 6 := by
      rw [he2]
      rfl
    have hadd := addExp_weight e12 eP he12len hePlen
    rw [hmeq, hadd]
    have heaW : expWeight ([0,0,0,1,0,0] : Exp) = 2 := by
      rw [expWeight_six]
    have hebW : expWeight ([0,0,0,0,1,0] : Exp) = 1 := by
      rw [expWeight_six]
    have he12W : expWeight e12 = 3 := by
      have hadd12 := addExp_weight ea eb (by rw [hea]; rfl) (by rw [heb]; rfl)
      rw [he12eq, hadd12, hea, heb, heaW, hebW]
    rw [he12W, he2, expWeight_six, expWeight_six]
    omega

theorem Dsum3_weight (cc : Rat) (e : Exp) (h : e.length = 6) (m : Mono) :
    m ∈ polyMul (polyMul a4 a5) (partialDeriv ⟨3, by decide⟩ [(cc, e)]) →
    expWeight m.2 = expWeight e := by
  obtain ⟨a,b,c,d,e',f,rfl⟩ := expSix e h
  have hv4 : varExp 4 = [0,0,0,0,1,0] := rfl
  have hv5 : varExp 5 = [0,0,0,0,0,1] := rfl
  intro hm
  have hm2 : m.2 ∈ (polyMul (polyMul a4 a5)
      (partialDeriv ⟨3, by decide⟩ [(cc, [a,b,c,d,e',f])])).map (·.2) :=
    List.mem_map.mpr ⟨m, hm, rfl⟩
  obtain ⟨e12, he12mem, eP, hePmem, hmeq⟩ := polyMul_mem_exp _ _ _ hm2
  obtain ⟨ea, haemem, eb, hebmem, he12eq⟩ := polyMul_mem_exp _ _ _ he12mem
  have hea : ea = [0,0,0,0,1,0] := by
    have h1 : ea ∈ ([(1, varExp 4)] : Poly).map (·.2) := haemem
    simp at h1
    rw [h1, hv4]
  have heb : eb = [0,0,0,0,0,1] := by
    have h1 : eb ∈ ([(1, varExp 5)] : Poly).map (·.2) := hebmem
    simp at h1
    rw [h1, hv5]
  obtain ⟨m', hm'mem, c', hdm⟩ := partialDeriv_mem_exp _ _ _ hePmem
  have hm'eq : m' = (cc, [a,b,c,d,e',f]) := by simpa using hm'mem
  rw [hm'eq] at hdm
  cases hd : d with
  | zero =>
    subst hd
    have hdn : derivMono (⟨3, by decide⟩ : Fin 6) (cc, [a,b,c,0,e',f]) = none := by
      unfold derivMono
      rfl
    rw [hdn] at hdm
    cases hdm
  | succ n =>
    subst hd
    have hdmc : derivMono (⟨3, by decide⟩ : Fin 6) (cc, [a,b,c,n+1,e',f]) =
        some ((cc * (((n+1 : Nat) : Rat))), [a,b,c,n,e',f]) := by
      unfold derivMono
      simp
    rw [hdmc] at hdm
    have he2 : eP = [a,b,c,n,e',f] := by
      have hp := congrArg Prod.snd (Option.some_inj.mp hdm)
      exact hp.symm
    have he12len : e12.length = 6 := by
      rw [he12eq, hea, heb]
      rfl
    have hePlen : eP.length = 6 := by
      rw [he2]
      rfl
    have hadd := addExp_weight e12 eP he12len hePlen
    rw [hmeq, hadd]
    have heaW : expWeight ([0,0,0,0,1,0] : Exp) = 1 := by
      rw [expWeight_six]
    have hebW : expWeight ([0,0,0,0,0,1] : Exp) = 1 := by
      rw [expWeight_six]
    have he12W : expWeight e12 = 2 := by
      have hadd12 := addExp_weight ea eb (by rw [hea]; rfl) (by rw [heb]; rfl)
      rw [he12eq, hadd12, hea, heb, heaW, hebW]
    rw [he12W, he2, expWeight_six, expWeight_six]
    omega

theorem dmono_weight (cc : Rat) (e : Exp) (h : e.length = 6) (m : Mono) :
    m ∈ D [(cc, e)] → expWeight m.2 = expWeight e := by
  intro hm
  have hm2 : m.2 ∈ (D [(cc, e)]).map (·.2) :=
    List.mem_map.mpr ⟨m, hm, rfl⟩
  rw [D_def] at hm2
  obtain hL | hR := polyAdd_mem_exp _ _ _ hm2
  · obtain h0 | h1 := polyAdd_mem_exp _ _ _ hL
    · obtain ⟨y, hym, hyeq⟩ := List.mem_map.mp h0
      have hw := Dsum0_weight cc e h y hym
      simp only [← hyeq]
      exact hw
    · obtain ⟨y, hym, hyeq⟩ := List.mem_map.mp h1
      have hw := Dsum1_weight cc e h y hym
      simp only [← hyeq]
      exact hw
  · obtain h2 | h3 := polyAdd_mem_exp _ _ _ hR
    · obtain ⟨y, hym, hyeq⟩ := List.mem_map.mp h2
      have hw := Dsum2_weight cc e h y hym
      simp only [← hyeq]
      exact hw
    · obtain ⟨y, hym, hyeq⟩ := List.mem_map.mp h3
      have hw := Dsum3_weight cc e h y hym
      simp only [← hyeq]
      exact hw

theorem dmat_col_weight (w : Nat) (j : Nat) (hj : j < (monoW w).length) (m : Mono) :
    m ∈ D (basisPoly ((monoW w)[j]?.getD [0,0,0,0,0,0])) →
    expWeight m.2 = w := by
  intro hm
  have hsome : ((monoW w)[j]?) = some (((monoW w)[j]'hj)) :=
    List.getElem?_eq_getElem hj
  have hmem : (((monoW w)[j]'hj)) ∈ monoW w := List.getElem_mem hj
  have h6 : (((monoW w)[j]?.getD [0,0,0,0,0,0]).length) = 6 := by
    rw [hsome, Option.getD_some]
    exact monoW_mem_six w _ hmem
  have hw := dmono_weight 1 _ h6 m hm
  have hmemW : expWeight (((monoW w)[j]?.getD [0,0,0,0,0,0])) = w := by
    rw [hsome, Option.getD_some]
    exact monoW_mem_weight w _ hmem
  rw [hmemW] at hw
  exact hw

-- Evaluation infrastructure: coefficient lookup with
-- exact rational arithmetic, preserved by normalization.
-- Used to prove D-linearity and weight-class separation without any
-- Mathlib dependency.

/-- Coefficient of exponent `x` in `p` (sum over matching terms). -/
def evalCoeff (p : Poly) (x : Exp) : Rat :=
  match p with
  | [] => 0
  | (c, e) :: rest => (if e = x then c else 0) + evalCoeff rest x

theorem evalCoeff_nil (x : Exp) : evalCoeff [] x = 0 := rfl

theorem evalCoeff_cons (m : Mono) (rest : Poly) (x : Exp) :
    evalCoeff (m :: rest) x = (if m.2 = x then m.1 else 0) + evalCoeff rest x := by
  obtain ⟨c, e⟩ := m
  rfl

theorem evalCoeff_append (p q : Poly) (x : Exp) :
    evalCoeff (p ++ q) x = evalCoeff p x + evalCoeff q x := by
  induction p with
  | nil => simp only [List.nil_append, evalCoeff_nil, Rat.zero_add]
  | cons hd tl ih =>
    obtain ⟨c, e⟩ := hd
    simp only [List.cons_append, evalCoeff_cons]
    rw [ih, ← Rat.add_assoc]

theorem evalCoeff_perm (p q : Poly) (h : p.Perm q) (x : Exp) :
    evalCoeff p x = evalCoeff q x := by
  induction h with
  | nil => rfl
  | cons y _ ih =>
    simp only [evalCoeff_cons]
    rw [ih]
  | swap x y l =>
    simp only [evalCoeff_cons]
    ac_rfl
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem evalCoeff_cons_pair (c : Rat) (e : Exp) (rest : Poly) (x : Exp) :
    evalCoeff ((c, e) :: rest) x = (if e = x then c else 0) + evalCoeff rest x := rfl

theorem evalCoeff_insertCombineGo (m : Mono) (q : Poly) (x : Exp) :
    evalCoeff (insertCombineGo m q) x = evalCoeff (m :: q) x := by
  obtain ⟨cm, em⟩ := m
  induction q with
  | nil => simp only [insertCombineGo]
  | cons hd tl ih =>
    obtain ⟨c, e⟩ := hd
    simp only [insertCombineGo]
    split
    · next heq =>
      split
      · next hzero =>
        by_cases hmx : em = x
        · rw [evalCoeff_cons_pair, evalCoeff_cons_pair, heq, if_pos hmx, if_pos hmx]
          rw [← Rat.add_assoc, Rat.add_comm cm c, hzero, Rat.zero_add]
        · have hne : e ≠ x := by
            rw [heq]
            exact hmx
          rw [evalCoeff_cons_pair, evalCoeff_cons_pair, if_neg hmx, if_neg hne,
            Rat.zero_add, Rat.zero_add]
      · next hnonzero =>
        by_cases hmx : em = x
        · rw [evalCoeff_cons_pair, evalCoeff_cons_pair, evalCoeff_cons_pair, heq,
            if_pos hmx, if_pos hmx, if_pos hmx]
          ac_rfl
        · rw [evalCoeff_cons_pair, evalCoeff_cons_pair, evalCoeff_cons_pair, heq,
            if_neg hmx, if_neg hmx, if_neg hmx]
          simp only [Rat.zero_add]
    · next _hne =>
      simp only [evalCoeff_cons_pair]
      rw [ih]
      simp only [evalCoeff_cons_pair]
      ac_rfl

theorem evalCoeff_insertCombine (m : Mono) (q : Poly) (x : Exp) :
    evalCoeff (insertCombine m q) x = evalCoeff (m :: q) x := by
  obtain ⟨cm, em⟩ := m
  by_cases h0 : cm = 0
  · have e : insertCombine (cm, em) q = q := by
      simp [insertCombine, h0]
    rw [e, evalCoeff_cons_pair]
    by_cases hmx : em = x
    · rw [if_pos hmx, h0, Rat.zero_add]
    · rw [if_neg hmx, Rat.zero_add]
  · by_cases hmem : em ∈ q.map (·.2)
    · have e : insertCombine (cm, em) q = insertCombineGo (cm, em) q := by
        simp [insertCombine, h0, hmem]
      rw [e]
      exact evalCoeff_insertCombineGo _ _ _
    · have e : insertCombine (cm, em) q = (cm, em) :: q := by
        simp [insertCombine, h0, hmem]
      rw [e]

theorem evalCoeff_combine (p : Poly) (x : Exp) :
    evalCoeff (combine p) x = evalCoeff p x := by
  induction p with
  | nil => simp only [combine]
  | cons hd tl ih =>
    simp only [combine]
    rw [evalCoeff_insertCombine, evalCoeff_cons, evalCoeff_cons, ih]

theorem evalCoeff_normalize (p : Poly) (x : Exp) :
    evalCoeff (normalize p) x = evalCoeff p x := by
  unfold normalize
  have hsort : evalCoeff (sortPoly (combine p)) x = evalCoeff (combine p) x :=
    evalCoeff_perm _ _ (sortPoly_perm _) x
  rw [hsort]
  exact evalCoeff_combine p x

theorem evalCoeff_missing (p : Poly) (x : Exp)
    (h : ∀ m ∈ p, m.2 ≠ x) : evalCoeff p x = 0 := by
  revert h
  induction p with
  | nil => intro h; exact evalCoeff_nil x
  | cons hd tl ih =>
    intro h
    have he : hd.2 ≠ x := h hd (by simp)
    have ht : ∀ m ∈ tl, m.2 ≠ x := fun m hm => h m (List.mem_cons_of_mem _ hm)
    have ihe := ih ht
    rw [evalCoeff_cons, if_neg he, ihe, Rat.zero_add]

theorem evalCoeff_head_eq (c : Rat) (e : Exp) (tl : Poly)
    (hnd : e ∉ tl.map (·.2)) : evalCoeff ((c, e) :: tl) e = c := by
  rw [evalCoeff_cons_pair]
  have h0 : evalCoeff tl e = 0 :=
    evalCoeff_missing tl e (fun m hm => by
      intro hcon
      apply hnd
      rw [← hcon]
      exact List.mem_map.mpr ⟨m, hm, rfl⟩)
  simp only [if_true]
  rw [h0, Rat.add_zero]

theorem mem_of_eval_ne_zero (X : Poly) (y : Exp) (h : evalCoeff X y ≠ 0) :
    ∃ t ∈ X, t.2 = y := by
  revert h
  induction X with
  | nil =>
    intro h
    simp [evalCoeff_nil] at h
  | cons hd tl ih =>
    intro h
    obtain ⟨c, e⟩ := hd
    by_cases heq : e = y
    · exact ⟨(c, e), by simp, heq⟩
    · have htl : evalCoeff tl y ≠ 0 := by
        have e1 : evalCoeff ((c, e) :: tl) y = evalCoeff tl y := by
          rw [evalCoeff_cons_pair, if_neg heq, Rat.zero_add]
        rw [e1] at h
        exact h
      obtain ⟨t, htm, hteq⟩ := ih htl
      exact ⟨t, List.mem_cons_of_mem _ htm, hteq⟩

theorem normalized_eq_of_same_eval (p q : Poly)
    (hp : hasNoZeros p) (hq : hasNoZeros q)
    (hpn : hasNoDups p) (hqn : hasNoDups q)
    (hps : List.Pairwise (fun a b => monoLE a b = true) p)
    (hqs : List.Pairwise (fun a b => monoLE a b = true) q)
    (heq : ∀ x, evalCoeff p x = evalCoeff q x) : p = q := by
  induction p generalizing q hq hqn hqs with
  | nil =>
    cases hQ : q with
    | nil =>
      subst hQ
      rfl
    | cons y ys =>
      subst hQ
      exfalso
      have hy1 : y.1 ≠ 0 := hq y (by simp)
      have hmem : y.2 ∉ ys.map (·.2) := by
        have hqn2 : (y.2 :: ys.map (·.2)).Nodup := hqn
        exact (List.nodup_cons.mp hqn2).1
      have h0 : evalCoeff ys y.2 = 0 :=
        evalCoeff_missing ys y.2 (fun m hm => by
          intro hcon
          apply hmem
          rw [← hcon]
          exact List.mem_map.mpr ⟨m, hm, rfl⟩)
      have heq0 := heq y.2
      rw [evalCoeff_nil] at heq0
      have hcons0 : evalCoeff (y :: ys) y.2 =
          (if y.2 = y.2 then y.1 else 0) + evalCoeff ys y.2 := by
        rw [evalCoeff_cons]
      rw [hcons0] at heq0
      simp only [if_true] at heq0
      rw [h0, Rat.add_zero] at heq0
      exact hy1 heq0.symm
  | cons hd tl ih =>
    cases hQ : q with
    | nil =>
      subst hQ
      exfalso
      have hh1 : hd.1 ≠ 0 := hp hd (by simp)
      have hmem : hd.2 ∉ tl.map (·.2) := by
        have hpn2 : (hd.2 :: tl.map (·.2)).Nodup := hpn
        exact (List.nodup_cons.mp hpn2).1
      have h0 : evalCoeff tl hd.2 = 0 :=
        evalCoeff_missing tl hd.2 (fun m hm => by
          intro hcon
          apply hmem
          rw [← hcon]
          exact List.mem_map.mpr ⟨m, hm, rfl⟩)
      have heq0 := heq hd.2
      rw [evalCoeff_cons] at heq0
      simp only [if_true] at heq0
      rw [h0, evalCoeff_nil, Rat.add_zero] at heq0
      exact hh1 heq0
    | cons y ys =>
      subst hQ
      obtain ⟨cx, ex⟩ := hd
      obtain ⟨cy, ey⟩ := y
      -- Head evaluations on both sides.
      have hYeval : evalCoeff ((cy, ey) :: ys) ey = cy := by
        have hnd : ey ∉ ys.map (·.2) := by
          have hqn2 : (ey :: ys.map (·.2)).Nodup := hqn
          exact (List.nodup_cons.mp hqn2).1
        rw [evalCoeff_cons_pair, if_pos rfl]
        have h0y : evalCoeff ys ey = 0 :=
          evalCoeff_missing ys ey (fun m hm => by
            intro hcon
            apply hnd
            rw [← hcon]
            exact List.mem_map.mpr ⟨m, hm, rfl⟩)
        rw [h0y, Rat.add_zero]
      have hXeval : evalCoeff ((cx, ex) :: tl) ex = cx := by
        have hndX : ex ∉ tl.map (·.2) := by
          have hpn2 : (ex :: tl.map (·.2)).Nodup := hpn
          exact (List.nodup_cons.mp hpn2).1
        rw [evalCoeff_cons_pair, if_pos rfl]
        have h0x : evalCoeff tl ex = 0 :=
          evalCoeff_missing tl ex (fun m hm => by
            intro hcon
            apply hndX
            rw [← hcon]
            exact List.mem_map.mpr ⟨m, hm, rfl⟩)
        rw [h0x, Rat.add_zero]
      -- Direction 1: ex ≤ ey via support of the ey-evaluation in X.
      have h1 : ex ≤ ey := by
        have hXne : evalCoeff ((cx, ex) :: tl) ey ≠ 0 := by
          rw [heq ey, hYeval]
          exact hq (cy, ey) (by simp)
        obtain ⟨t, htm, hteq⟩ := mem_of_eval_ne_zero _ _ hXne
        simp at htm
        rcases htm with rfl | htl
        · have hex : ex = ey := hteq
          rw [hex]
          exact List.le_refl _
        · have hpair := (List.pairwise_cons.mp hps).1 t htl
          have hle : ex ≤ t.2 := of_decide_eq_true hpair
          rw [hteq] at hle
          exact hle
      -- Direction 2: ey ≤ ex, mirrored.
      have h2 : ey ≤ ex := by
        have hYne : evalCoeff ((cy, ey) :: ys) ex ≠ 0 := by
          have hcx : cx ≠ 0 := hp (cx, ex) (by simp)
          have e := heq ex
          rw [hXeval] at e
          rw [← e]
          exact hcx
        obtain ⟨s, hsm, hseq⟩ := mem_of_eval_ne_zero _ _ hYne
        simp at hsm
        rcases hsm with rfl | hsl
        · have hey : ey = ex := hseq
          rw [hey]
          exact List.le_refl _
        · have hpair := (List.pairwise_cons.mp hqs).1 s hsl
          have hle : ey ≤ s.2 := of_decide_eq_true hpair
          rw [hseq] at hle
          exact hle
      have hXY : ex = ey := List.le_antisymm h1 h2
      -- Head of Y evaluated at ex.
      have hYe : evalCoeff ((cy, ey) :: ys) ex = cy := by
        have hnd : ey ∉ ys.map (·.2) := by
          have hqn2 : (ey :: ys.map (·.2)).Nodup := hqn
          exact (List.nodup_cons.mp hqn2).1
        have hnex : ex ∉ ys.map (·.2) := by
          rw [hXY]
          exact hnd
        have h0y : evalCoeff ys ex = 0 :=
          evalCoeff_missing ys ex (fun m hm => by
            intro hcon
            apply hnex
            rw [← hcon]
            exact List.mem_map.mpr ⟨m, hm, rfl⟩)
        rw [evalCoeff_cons_pair, if_pos hXY.symm, h0y, Rat.add_zero]
      -- Coefficients agree.
      have hcc : cx = cy := by
        have eXY := heq ex
        rw [hXeval, hYe] at eXY
        exact eXY
      -- Tails agree pointwise.
      have htail : ∀ x, evalCoeff tl x = evalCoeff ys x := by
        intro x
        have h1x := heq x
        rw [evalCoeff_cons, evalCoeff_cons, hXY, hcc] at h1x
        exact Rat.add_left_cancel _ h1x
      -- Tail hypotheses and induction.
      have htp : hasNoZeros tl := fun m hm => hp m (List.mem_cons_of_mem _ hm)
      have htq : hasNoZeros ys := fun m hm => hq m (List.mem_cons_of_mem _ hm)
      have hnpn : hasNoDups tl := by
        have hpn2 : (ex :: tl.map (·.2)).Nodup := hpn
        exact (List.nodup_cons.mp hpn2).2
      have hnqn : hasNoDups ys := by
        have hqn2 : (ey :: ys.map (·.2)).Nodup := hqn
        exact (List.nodup_cons.mp hqn2).2
      have hps_tl : List.Pairwise (fun a b => monoLE a b = true) tl :=
        (List.pairwise_cons.mp hps).2
      have hqs_tl : List.Pairwise (fun a b => monoLE a b = true) ys :=
        (List.pairwise_cons.mp hqs).2
      have htl_eq : tl = ys := ih ys htp htq hnpn hnqn hps_tl hqs_tl htail
      rw [hXY, hcc, htl_eq]

theorem evalCoeff_polyAdd (p q : Poly) (x : Exp) :
    evalCoeff (polyAdd p q) x = evalCoeff p x + evalCoeff q x := by
  unfold polyAdd
  rw [evalCoeff_normalize]
  exact evalCoeff_append p q x

theorem evalCoeff_polyMul (p q : Poly) (x : Exp) :
    evalCoeff (polyMul p q) x =
      evalCoeff ((p.flatMap fun m1 => q.map fun m2 => mulMono m1 m2)) x := by
  unfold polyMul
  exact evalCoeff_normalize _ _