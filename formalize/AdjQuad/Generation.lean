import AdjQuad.Poly
import AdjQuad.Witness
import AdjQuad.WeightData
import AdjQuad.Deriv
import AdjQuad.Counterexample

open scoped Rat

/-!
# Generation assembly: spanning + generation.

`genMonos w` enumerates the weight-`w` monomials in the six generators
`(p, q, J1, J2, F0, H)` in `_gen_mono_exps` order. `span_of_bundle`
turns a per-weight checked bundle (`checkWitness`, `gselDecode`,
`gselKernel`, `qLeftInv`) into a scaled combination of `genMonos w`
for every normalized homogeneous invariant of weight `w`; the spanning
premise is proved in `KernelSpan` via `z = dg·v - Gsel(Kg·v)`.
`generation_closed` closes generation by induction on `weightedDegree`,
conditional on the per-weight bundles (`hW`) and the reducibility
premise (`h_bound`).

Notes: `hW` is stated about `dmat w` directly, so no separate
`dmat = emitted literal` premise is needed. Poly-level combinations use
`polyLincomb` (`Witness.lincomb` is integer-vector-level). Denominators
are cleared exactly: the producer scales selected columns by
`D0` = LCM of coefficient denominators at `w`, and `gselDecode` checks
`Gsel[i][j] * c.den = D0 * c.num`. `F` is required normalized.
-/

/-- Exponent tuples `(ep,eq,ej1,ej2,ef,eh)` of `(1,1,6,4,14,24)`-weight `w`,
    mirroring the producer's `_gen_mono_exps` order exactly. -/
def genMonoExps (w : Nat) : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  (List.range (w / 24 + 1)).flatMap fun eh =>
  (List.range ((w - 24 * eh) / 14 + 1)).flatMap fun ef =>
  (List.range ((w - 24 * eh - 14 * ef) / 4 + 1)).flatMap fun ej2 =>
  (List.range ((w - 24 * eh - 14 * ef - 4 * ej2) / 6 + 1)).flatMap fun ej1 =>
  (List.range (w - 24 * eh - 14 * ef - 4 * ej2 - 6 * ej1 + 1)).map fun ep =>
    (ep, w - 24 * eh - 14 * ef - 4 * ej2 - 6 * ej1 - ep, ej1, ej2, ef, eh)

/-- Generator monomial as a `Poly`: product of generator powers. -/
def genMono (e : Nat × Nat × Nat × Nat × Nat × Nat) : Poly :=
  match e with
  | (ep, eq, ej1, ej2, ef, eh) =>
    polyMul (polyMul (polyMul (polyPow p ep) (polyPow q eq))
      (polyMul (polyPow J1 ej1) (polyPow J2 ej2)))
      (polyMul (polyPow F0 ef) (polyPow H eh))

/-- Weight-`w` generator monomials as polys. -/
def genMonos (w : Nat) : List Poly := (genMonoExps w).map genMono

/-- Construction weight of an exponent tuple. -/
def genWt : Nat × Nat × Nat × Nat × Nat × Nat → Nat
  | (ep, eq, ej1, ej2, ef, eh) => ep + eq + 6 * ej1 + 4 * ej2 + 14 * ef + 24 * eh

theorem genWt_of_mem (w : Nat) (e : Nat × Nat × Nat × Nat × Nat × Nat)
    (h : e ∈ genMonoExps w) : genWt e = w := by
  obtain ⟨ep, eq, ej1, ej2, ef, eh⟩ := e
  simp only [genMonoExps, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨eh, hheh, ef, hfef, ej2, hj2, ej1, hj1, ep, hpep, htuple⟩ := h
  simp only [Prod.mk.injEq] at htuple
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := htuple
  simp only [genWt]
  omega

theorem genMonos_0 : (genMonos 0).length = 1 := by decide

theorem genMonos_1 : (genMonos 1).length = 2 := by decide

theorem genMonos_2 : (genMonos 2).length = 3 := by decide


/-- Exact decode invariant (corrected contract, no truncation): `Gsel` is
    exactly `D0` times the true rational coefficient vectors of the
    selected `genMonos w` in the `monoW w` basis. Cross-multiplied to stay
    integral: for the coefficient `c` of the selected genMono at basis
    monomial `monoW w [i]`, the check is `Gsel[i][j] * c.den = D0 * c.num`
    (exact `Rat` equality, since `c = c.num / c.den` with `c.den > 0`).
    Also checked: `D0` nonzero, `Gsel` has the `monoW w` row count,
    `selIdx` nodup and in range. -/
def gselDecode (w : Nat) (selIdx : List Nat) (Gsel : IMat) (D0 : Int) : Bool :=
  decide (D0 ≠ 0)
  && decide (Gsel.length = (monoW w).length)
  && decide selIdx.Nodup
  && ((List.range selIdx.length).map (fun j =>
      decide ((selIdx[j]?).getD 0 < (genMonos w).length))).all (fun b => b)
  && (((List.range (monoW w).length).map fun i =>
      (List.range selIdx.length).map fun j =>
        let g : Poly := ((genMonos w)[(selIdx[j]?).getD 0]?).getD []
        let c := evalCoeff g ((monoW w)[i]?.getD [])
        ((Gsel[i]?).getD [])[j]?.getD 0 * (c.den : Int)) ==
    ((List.range (monoW w).length).map fun i =>
      (List.range selIdx.length).map fun j =>
        let g : Poly := ((genMonos w)[(selIdx[j]?).getD 0]?).getD []
        D0 * (evalCoeff g ((monoW w)[i]?.getD [])).num))

-- Poly-level linear combinations + evaluation toolkit (T12-2).

theorem rat_mul_ne_zero {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  fun h => (Rat.mul_eq_zero.mp h).elim ha hb

theorem rat_intCast_ne_zero {d : Int} (hd : d ≠ 0) : (d : Rat) ≠ 0 :=
  fun h => hd (Rat.intCast_eq_zero_iff.mp h)

/-- Poly-level integer linear combination (cf. `Witness.lincomb`, vectors). -/
def polyLincomb : List Int → List Poly → Poly
  | [], _ => []
  | _, [] => []
  | c :: cs, p :: ps => polyAdd (polySmulInt c p) (polyLincomb cs ps)

theorem polyLincomb_nil_right (cs : List Int) : polyLincomb cs [] = [] := by
  cases cs with
  | nil => rfl
  | cons _ _ => rfl

theorem evalCoeff_polySmulInt (d : Int) (p : Poly) (x : Exp) :
    evalCoeff (polySmulInt d p) x = (d : Rat) * evalCoeff p x := by
  induction p with
  | nil => simp [polySmulInt, evalCoeff_nil, Rat.mul_zero]
  | cons hd tl ih =>
    obtain ⟨c0, e0⟩ := hd
    simp only [polySmulInt] at ih ⊢
    by_cases h : e0 = x
    · simp only [List.map_cons, evalCoeff_cons, h, if_true, ih, Rat.mul_add]
    · simp only [List.map_cons, evalCoeff_cons, h, if_false, ih, Rat.zero_add]

theorem evalCoeff_flatMap (p : Poly) (f : Mono → Poly) (x : Exp) :
    evalCoeff (p.flatMap f) x = List.sum (p.map fun m => evalCoeff (f m) x) := by
  induction p with
  | nil => simp [evalCoeff_nil]
  | cons hd tl ih =>
    simp only [List.flatMap_cons, evalCoeff_append, ih, List.map_cons, List.sum_cons]

theorem evalCoeff_filterMap (p : Poly) (f : Mono → Option Mono) (x : Exp) :
    evalCoeff (p.filterMap f) x =
      evalCoeff (p.flatMap fun m => (f m).toList) x := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    cases h : f hd with
    | none =>
      simp [h, ih]
    | some m =>
      simp [h, ih, evalCoeff_cons]

theorem evalCoeff_polyLincomb (cs : List Int) (ps : List Poly)
    (hlen : cs.length = ps.length) (x : Exp) :
    evalCoeff (polyLincomb cs ps) x =
      List.sum (List.zipWith (fun c p => ((c : Int) : Rat) * evalCoeff p x) cs ps) := by
  match cs, ps, hlen with
  | [], [], _ => simp [polyLincomb, evalCoeff_nil]
  | c :: cs, p :: ps, h =>
    have hlen' : cs.length = ps.length := by
      simp only [List.length_cons] at h
      omega
    simp only [polyLincomb, evalCoeff_polyAdd, evalCoeff_polySmulInt,
      List.zipWith_cons_cons, List.sum_cons, evalCoeff_polyLincomb cs ps hlen' x]

/-- `polySmulInt` preserves `hasNoZeros` for nonzero scalars. -/
theorem smul_noZeros (d : Int) (hd : d ≠ 0) (p : Poly) (h : hasNoZeros p) :
    hasNoZeros (polySmulInt d p) := by
  intro m hm
  unfold polySmulInt at hm
  obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
  simp only
  exact rat_mul_ne_zero (rat_intCast_ne_zero hd) (h m' hm')

/-- `polySmulInt` preserves `hasNoDups` (exponents untouched). -/
theorem smul_nodup (d : Int) (p : Poly) (h : hasNoDups p) :
    hasNoDups (polySmulInt d p) := by
  unfold hasNoDups polySmulInt at *
  rw [List.map_map]
  exact h

/-- `polySmulInt` preserves sortedness (comparison sees exponents only). -/
theorem smul_pairwise (d : Int) (p : Poly)
    (h : List.Pairwise (fun a b => monoLE a b = true) p) :
    List.Pairwise (fun a b => monoLE a b = true) (polySmulInt d p) := by
  unfold polySmulInt
  exact List.Pairwise.map _ (fun a b h => h) h

/-- `polySmulInt` distributes over `polyAdd` (nonzero scalar). -/
theorem smul_add_dist (a : Int) (ha : a ≠ 0) (p q : Poly) :
    polySmulInt a (polyAdd p q) = polyAdd (polySmulInt a p) (polySmulInt a q) := by
  have e : ∀ x, evalCoeff (polySmulInt a (polyAdd p q)) x =
      evalCoeff (polyAdd (polySmulInt a p) (polySmulInt a q)) x := by
    intro x
    rw [evalCoeff_polySmulInt, evalCoeff_polyAdd, evalCoeff_polyAdd,
      evalCoeff_polySmulInt, evalCoeff_polySmulInt, Rat.mul_add]
  have lhs0 : hasNoZeros (polySmulInt a (polyAdd p q)) :=
    smul_noZeros a ha _ (normalize_noZeros _)
  have lhsd : hasNoDups (polySmulInt a (polyAdd p q)) :=
    smul_nodup a _ (normalize_nodup _)
  have lhsp : List.Pairwise (fun a b => monoLE a b = true)
      (polySmulInt a (polyAdd p q)) :=
    smul_pairwise a _ (sortPoly_pairwise _)
  have rhs0 : hasNoZeros (polyAdd (polySmulInt a p) (polySmulInt a q)) := by
    unfold polyAdd
    exact normalize_noZeros _
  have rhsd : hasNoDups (polyAdd (polySmulInt a p) (polySmulInt a q)) := by
    unfold polyAdd
    exact normalize_nodup _
  have rhsp : List.Pairwise (fun a b => monoLE a b = true)
      (polyAdd (polySmulInt a p) (polySmulInt a q)) := by
    unfold polyAdd
    exact sortPoly_pairwise _
  exact normalized_eq_of_same_eval _ _ lhs0 rhs0 lhsd rhsd lhsp rhsp e

theorem polyLincomb_normalized (cs : List Int) (ps : List Poly) :
    hasNoZeros (polyLincomb cs ps) ∧ hasNoDups (polyLincomb cs ps) ∧
      List.Pairwise (fun a b => monoLE a b = true) (polyLincomb cs ps) := by
  match cs, ps with
  | [], _ =>
    simp only [polyLincomb]
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      simp at hm
    · unfold hasNoDups
      simp
    · exact List.Pairwise.nil
  | _ :: _, [] =>
    simp only [polyLincomb_nil_right]
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      simp at hm
    · unfold hasNoDups
      simp
    · exact List.Pairwise.nil
  | _ :: _, _ :: _ =>
    simp only [polyLincomb]
    exact ⟨normalize_noZeros _, normalize_nodup _,
      sortPoly_pairwise (combine _)⟩

/-- Scalar distributes into a `List.sum`. -/
theorem mul_sum_dist (a : Rat) (l : List Rat) :
    a * l.sum = (l.map (fun x => a * x)).sum := by
  induction l with
  | nil => simp [Rat.mul_zero]
  | cons hd tl ih => simp [ih, Rat.mul_add]

/-- Scaled `zipWith` factors through `map`. -/
theorem zipWith_smul_map (a : Int) (cs : List Int) (ps : List Poly) (x : Exp) :
    List.zipWith (fun c p => (((a * c : Int)) : Rat) * evalCoeff p x) cs ps =
      (List.zipWith (fun c p => ((c : Int) : Rat) * evalCoeff p x) cs ps).map
        (fun y => (a : Rat) * y) := by
  induction cs generalizing ps with
  | nil => cases ps with | nil => rfl | cons _ _ => rfl
  | cons c cs ih =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      simp only [List.zipWith_cons_cons, List.map_cons]
      rw [ih, Rat.intCast_mul, Rat.mul_assoc]

/-- `zipWith` over a mapped list fuses the map into the body. -/
theorem zipWith_map_left' (f : Int → Poly → Rat) (g : Int → Int) (cs : List Int)
    (ps : List Poly) :
    List.zipWith f (cs.map g) ps =
      List.zipWith (fun c p => f (g c) p) cs ps := by
  induction cs generalizing ps with
  | nil => cases ps with | nil => rfl | cons _ _ => rfl
  | cons c cs ih =>
    cases ps with
    | nil => rfl
    | cons p ps => simp [ih]

/-- `polySmulInt` threads through `polyLincomb` (nonzero scalar). -/
theorem smul_thread (a : Int) (ha : a ≠ 0) (cs : List Int) (ps : List Poly)
    (hlen : cs.length = ps.length) :
    polySmulInt a (polyLincomb cs ps) =
      polyLincomb (cs.map (fun c => a * c)) ps := by
  have hnormL := polyLincomb_normalized cs ps
  have hLc := polyLincomb_normalized (cs.map (fun c => a * c)) ps
  have hsm0 := smul_noZeros a ha _ hnormL.1
  have hsmd := smul_nodup a _ hnormL.2.1
  have hsmp := smul_pairwise a _ hnormL.2.2
  have e : ∀ x, evalCoeff (polySmulInt a (polyLincomb cs ps)) x =
      evalCoeff (polyLincomb (cs.map (fun c => a * c)) ps) x := by
    intro x
    rw [evalCoeff_polySmulInt, evalCoeff_polyLincomb _ _ hlen,
      evalCoeff_polyLincomb _ _ (by simp [hlen]), zipWith_map_left',
      zipWith_smul_map, ← mul_sum_dist]
  exact normalized_eq_of_same_eval _ _ hsm0 hLc.1 hsmd hLc.2.1 hsmp hLc.2.2 e

theorem polyAdd_empty_left (p : Poly) (h0 : hasNoZeros p) (hd : hasNoDups p)
    (hp : List.Pairwise (fun a b => monoLE a b = true) p) :
    polyAdd [] p = p := by
  have e : ∀ x, evalCoeff (polyAdd [] p) x = evalCoeff p x := by
    intro x
    rw [evalCoeff_polyAdd, evalCoeff_nil, Rat.zero_add]
  have lhs0 := normalize_noZeros ( ([] : Poly) ++ p)
  have lhsd := normalize_nodup ( ([] : Poly) ++ p)
  have lhsp := sortPoly_pairwise (combine ([] ++ p))
  have hL0 : hasNoZeros (polyAdd [] p) := lhs0
  have hLd : hasNoDups (polyAdd [] p) := lhsd
  have hLp : List.Pairwise (fun a b => monoLE a b = true) (polyAdd [] p) := lhsp
  exact normalized_eq_of_same_eval _ _ hL0 h0 hLd hd hLp hp e

theorem polyAdd_empty_right (p : Poly) (h0 : hasNoZeros p) (hd : hasNoDups p)
    (hp : List.Pairwise (fun a b => monoLE a b = true) p) :
    polyAdd p [] = p := by
  have e : ∀ x, evalCoeff (polyAdd p []) x = evalCoeff p x := by
    intro x
    rw [evalCoeff_polyAdd, evalCoeff_nil, Rat.add_zero]
  have hL0 : hasNoZeros (polyAdd p []) := normalize_noZeros _
  have hLd : hasNoDups (polyAdd p []) := normalize_nodup _
  have hLp : List.Pairwise (fun a b => monoLE a b = true) (polyAdd p []) :=
    sortPoly_pairwise _
  exact normalized_eq_of_same_eval _ _ hL0 h0 hLd hd hLp hp e

theorem polyAdd_assoc (p q r : Poly) :
    polyAdd (polyAdd p q) r = polyAdd p (polyAdd q r) := by
  have e : ∀ x, evalCoeff (polyAdd (polyAdd p q) r) x =
      evalCoeff (polyAdd p (polyAdd q r)) x := by
    intro x
    simp only [evalCoeff_polyAdd, Rat.add_assoc]
  have hL0 : hasNoZeros (polyAdd (polyAdd p q) r) := normalize_noZeros _
  have hLd : hasNoDups (polyAdd (polyAdd p q) r) := normalize_nodup _
  have hLp : List.Pairwise (fun a b => monoLE a b = true)
      (polyAdd (polyAdd p q) r) := sortPoly_pairwise _
  have hR0 : hasNoZeros (polyAdd p (polyAdd q r)) := normalize_noZeros _
  have hRd : hasNoDups (polyAdd p (polyAdd q r)) := normalize_nodup _
  have hRp : List.Pairwise (fun a b => monoLE a b = true)
      (polyAdd p (polyAdd q r)) := sortPoly_pairwise _
  exact normalized_eq_of_same_eval _ _ hL0 hR0 hLd hRd hLp hRp e

theorem polyLincomb_append (cs1 cs2 : List Int) (ps1 ps2 : List Poly)
    (h1 : cs1.length = ps1.length)
    (hn : ∀ p ∈ ps1 ++ ps2, hasNoZeros p ∧ hasNoDups p ∧
      List.Pairwise (fun a b => monoLE a b = true) p) :
    polyLincomb (cs1 ++ cs2) (ps1 ++ ps2) =
      polyAdd (polyLincomb cs1 ps1) (polyLincomb cs2 ps2) := by
  induction cs1 generalizing ps1 with
  | nil =>
    have hlen0 : ps1.length = 0 := by simpa using h1.symm
    have hps1 : ps1 = [] := List.eq_nil_of_length_eq_zero hlen0
    subst hps1
    simp only [List.nil_append, polyLincomb]
    exact (polyAdd_empty_left _ (polyLincomb_normalized cs2 ps2).1
      (polyLincomb_normalized cs2 ps2).2.1
      (polyLincomb_normalized cs2 ps2).2.2).symm
  | cons c cs1 ih =>
    cases ps1 with
    | nil => simp at h1
    | cons p ps1 =>
      have h1' : cs1.length = ps1.length := by
        simp only [List.length_cons] at h1
        omega
      have hn' : ∀ p ∈ ps1 ++ ps2, hasNoZeros p ∧ hasNoDups p ∧
          List.Pairwise (fun a b => monoLE a b = true) p := by
        intro q hq
        exact hn q (by simp [hq])
      simp only [List.cons_append, polyLincomb]
      rw [ih ps1 h1' hn', polyAdd_assoc]

theorem polyLincomb_zeros (cs : List Int) (ps : List Poly)
    (hlen : cs.length = ps.length) (hall : ∀ c ∈ cs, c = 0) :
    polyLincomb cs ps = [] := by
  match cs, ps, hlen with
  | [], [], _ => simp [polyLincomb]
  | c :: cs, p :: ps, h =>
    have hlen' : cs.length = ps.length := by
      simp only [List.length_cons] at h
      omega
    have hc0 : c = 0 := hall c (by simp)
    have ihr := polyLincomb_zeros cs ps hlen'
      (fun c hc => hall c (List.mem_cons_of_mem _ hc))
    have e : ∀ x, evalCoeff (polyLincomb (c :: cs) (p :: ps)) x =
        evalCoeff ([] : Poly) x := by
      intro x
      simp only [polyLincomb, evalCoeff_polyAdd, evalCoeff_polySmulInt,
        evalCoeff_nil, ihr, hc0, Rat.intCast_ofNat, Rat.zero_mul, Rat.zero_add]
    have hL := polyLincomb_normalized (c :: cs) (p :: ps)
    have hR0 : hasNoZeros ([] : Poly) := by intro m hm; simp at hm
    have hRd : hasNoDups ([] : Poly) := by unfold hasNoDups; simp
    have hRp : List.Pairwise (fun a b => monoLE a b = true) ([] : Poly) :=
      List.Pairwise.nil
    exact normalized_eq_of_same_eval _ _ hL.1 hR0 hL.2.1 hRd hL.2.2 hRp e

-- Range/fold bridges between `vecMatMul`/`lincomb` folds and `List.sum`.

theorem range_succ_head (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => lhs; rw [List.range_succ, ih, List.cons_append]
    conv => rhs; rw [List.range_succ, List.map_append]
    rfl

theorem map_range_get (C j : Nat) (F : Nat → α) (hj : j < C) :
    ((List.range C).map F)[j]? = some (F j) := by
  induction j generalizing C F with
  | zero =>
    obtain ⟨C', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : C ≠ 0)
    rw [range_succ_head]
    simp
  | succ j ih =>
    obtain ⟨C', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : C ≠ 0)
    have hjC : j < C' := by omega
    rw [range_succ_head, List.map_cons, List.getElem?_cons_succ,
      List.map_map]
    exact ih _ _ hjC

theorem sum_zero_terms (l : List α) (f : α → Rat) (h : ∀ a ∈ l, f a = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h hd (by simp), ih (fun a ha => h a (List.mem_cons_of_mem _ ha)),
      Rat.zero_add]

theorem intCast_foldl_range (n : Nat) (f : Nat → Int) :
    ((((List.range n).foldl (fun acc i => acc + f i) 0 : Int)) : Rat) =
      (((List.range n).map fun i => ((f i : Int) : Rat))).sum := by
  induction n with
  | zero => simp [Rat.intCast_ofNat]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.map_append, List.sum_append]
    simp only [List.foldl_cons, List.foldl_nil, Rat.intCast_add]
    rw [ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Rat.add_zero]

theorem zeroVec_getD (n j : Nat) : ((zeroVec n)[j]?.getD 0) = 0 := by
  induction n generalizing j with
  | zero => simp [zeroVec]
  | succ n ih =>
    cases j with
    | zero => simp [zeroVec, List.replicate_succ]
    | succ j =>
      simp only [zeroVec, List.replicate_succ, List.getElem?_cons_succ]
      exact ih j

theorem vec_entry_cast (v : List Int) (W : IMat) (j : Nat)
    (hj : j < imatCols W) :
    ((((vecMatMul v W)[j]?.getD 0 : Int)) : Rat) =
      (((List.range v.length).map fun i =>
        (((v[i]?.getD 0 : Int)) : Rat) * ((imatGet W i j : Int) : Rat))).sum := by
  unfold vecMatMul
  rw [map_range_get _ _ _ hj, Option.getD_some, intCast_foldl_range]
  simp only [Rat.intCast_mul]

theorem vecSmul_cast (d : Int) (v : List Int) (j : Nat) :
    ((((vecSmul d v)[j]?.getD 0 : Int)) : Rat) =
      (d : Rat) * (((v[j]?.getD 0 : Int)) : Rat) := by
  induction v generalizing j with
  | nil => simp [vecSmul, Rat.intCast_ofNat, Rat.mul_zero]
  | cons c cs ih =>
    cases j with
    | zero => simp [vecSmul, Rat.intCast_mul]
    | succ j =>
      simp only [vecSmul, List.map_cons, List.getElem?_cons_succ]
      exact ih j

theorem lincomb_entry_cast (coeffs : List Int) (S : IMat) (j : Nat)
    (hj : j < (((S[0]?).getD []) : List Int).length) :
    ((((lincomb coeffs S)[j]?.getD 0 : Int)) : Rat) =
      (((List.range coeffs.length).map fun i =>
        (((coeffs[i]?.getD 0 : Int)) : Rat) *
          (((((S[i]?.getD [] : List Int))[j]?.getD 0 : Int)) : Rat))).sum := by
  cases S with
  | nil =>
    rw [show lincomb coeffs [] = zeroVec coeffs.length from rfl,
      sum_zero_terms _ _ (fun a _ => by
        simp [Rat.intCast_ofNat, Rat.mul_zero])]
    simp [Rat.intCast_ofNat, zeroVec_getD]
  | cons v0 tl =>
    have hj' : j < v0.length := hj
    rw [show lincomb coeffs (v0 :: tl) =
        (List.range v0.length).map (fun j => (List.range coeffs.length).foldl
          (fun acc i => acc + (coeffs[i]?).getD 0 *
            (((( (v0 :: tl)[i]?.getD [])[j]?).getD 0))) 0) from rfl,
      map_range_get _ _ _ hj', Option.getD_some, intCast_foldl_range]
    simp only [Rat.intCast_mul]

theorem monoW_mem_last (w : Nat) : [0,0,0,0,0,w] ∈ monoW w := by
  unfold monoW
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨0, by omega, 0, by omega, 0, by omega, 0, by omega, 0, by omega, rfl⟩

theorem monoW_complete (w : Nat) (e : Exp) (h6 : e.length = 6)
    (hw : expWeight e = w) : e ∈ monoW w := by
  obtain ⟨a, b, c, d, e4, e5, rfl⟩ := expSix e h6
  rw [expWeight_six] at hw
  unfold monoW
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨a, by omega, b, by omega, c, by omega, d, by omega, e4, by omega, ?_⟩
  have he5 : e5 = w - 8 * a - 5 * b - 3 * c - 2 * d - e4 := by omega
  subst he5
  rfl

theorem pairwise_ne_of_nodup (l : List α) (h : l.Nodup) :
    l.Pairwise (fun x y => x ≠ y) :=
  List.nodup_iff_pairwise_ne.mp h

theorem nodup_of_pairwise_ne (l : List α)
    (h : l.Pairwise (fun x y => x ≠ y)) : l.Nodup :=
  List.nodup_iff_pairwise_ne.mpr h

theorem pairwise_range (n : Nat) (R : Nat → Nat → Prop)
    (h : ∀ a b, a < n → b < n → a ≠ b → R a b) :
    (List.range n).Pairwise R := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih (fun a b ha hb hne => h a b (by omega) (by omega) hne),
      List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    simp only [List.mem_range] at hx
    simp only [List.mem_singleton] at hy
    rw [hy]
    exact h x n (by omega) (by omega) (by omega)

theorem hmap_nodup (m : Nat) (f : Nat → Exp)
    (hinj : ∀ a b, a < m → b < m → a ≠ b → f a ≠ f b) :
    ((List.range m).map f).Nodup := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.nodup_append]
    refine ⟨ih (fun a b ha hb hne => hinj a b (by omega) (by omega) hne),
      by simp, ?_⟩
    · intro a ha b hb
      obtain ⟨i, him, rfl⟩ := List.mem_map.mp ha
      have hb' := List.mem_singleton.mp hb
      subst hb'
      have him' : i < m := List.mem_range.mp him
      exact hinj i m (by omega) (by omega) (by omega)

theorem monoW_nodup (w : Nat) : (monoW w).Nodup := by
  apply nodup_of_pairwise_ne
  unfold monoW
  rw [List.pairwise_flatMap]
  refine ⟨?_, ?_⟩
  · intro e0 _
    rw [List.pairwise_flatMap]
    refine ⟨?_, ?_⟩
    · intro e1 _
      rw [List.pairwise_flatMap]
      refine ⟨?_, ?_⟩
      · intro e2 _
        rw [List.pairwise_flatMap]
        refine ⟨?_, ?_⟩
        · intro e3 _
          exact pairwise_ne_of_nodup _
            (hmap_nodup _ _ (fun a b _ _ hne hcon => by
              have h4 := congrArg (fun x : Exp => x[4]?) hcon
              simp only [List.getElem?_cons_zero,
                List.getElem?_cons_succ] at h4
              exact hne (Option.some_inj.mp h4)))
        · refine pairwise_range _ _ (fun a3 b3 ha3 hb3 hne x hx y hy => ?_)
          simp only [List.mem_map, List.mem_range] at hx hy
          obtain ⟨e4, _, rfl⟩ := hx
          obtain ⟨f4, _, rfl⟩ := hy
          intro hcon
          have h3 := congrArg (fun z : Exp => z[3]?) hcon
          simp at h3
          exact hne h3
      · refine pairwise_range _ _ (fun a2 b2 ha2 hb2 hne x hx y hy => ?_)
        simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hx hy
        obtain ⟨e3, _, e4, _, rfl⟩ := hx
        obtain ⟨f3, _, f4, _, rfl⟩ := hy
        intro hcon
        have h2 := congrArg (fun z : Exp => z[2]?) hcon
        simp at h2
        exact hne h2
    · refine pairwise_range _ _ (fun a1 b1 ha1 hb1 hne x hx y hy => ?_)
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hx hy
      obtain ⟨e2, _, e3, _, e4, _, rfl⟩ := hx
      obtain ⟨f2, _, f3, _, f4, _, rfl⟩ := hy
      intro hcon
      have h1 := congrArg (fun z : Exp => z[1]?) hcon
      simp at h1
      exact hne h1
  · refine pairwise_range _ _ (fun a0 b0 ha0 hb0 hne x hx y hy => ?_)
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hx hy
    obtain ⟨e1, _, e2, _, e3, _, e4, _, rfl⟩ := hx
    obtain ⟨f1, _, f2, _, f3, _, f4, _, rfl⟩ := hy
    intro hcon
    have h0 := congrArg (fun z : Exp => z[0]?) hcon
    simp at h0
    exact hne h0

theorem dmatCols_length (w : Nat) : (dmatCols w).length = (monoW w).length := by
  simp [dmatCols]

theorem coordIn_length (dom : List Exp) (p : Poly) :
    (coordIn dom p).length = dom.length := by
  simp [coordIn]

theorem dmatCols_row_length (w : Nat) (row : List Int)
    (h : row ∈ dmatCols w) : row.length = (monoW w).length := by
  unfold dmatCols at h
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
  simp [coordIn]

theorem imatCols_dmatCols (w : Nat) :
    imatCols (dmatCols w) = (monoW w).length := by
  unfold imatCols
  have hne : dmatCols w ≠ [] := by
    intro hcon
    have hcc := congrArg List.length hcon
    simp only [dmatCols_length] at hcc
    have hnil : monoW w = [] :=
      List.eq_nil_of_length_eq_zero (by simpa using hcc)
    have hmem := monoW_mem_last w
    rw [hnil] at hmem
    simp at hmem
  obtain ⟨r0, rs, hrfl⟩ : ∃ r0 rs, dmatCols w = r0 :: rs :=
    List.exists_cons_of_ne_nil hne
  rw [hrfl]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  have := dmatCols_row_length w r0 (by simp [hrfl])
  omega

theorem imatRows_dmat (w : Nat) : imatRows (dmat w) = (monoW w).length := by
  simp [dmat, imatTranspose, imatRows, imatCols_dmatCols]

theorem imatCols_dmat (w : Nat) : imatCols (dmat w) = (monoW w).length := by
  have h1 : ∀ r ∈ dmat w, r.length = (monoW w).length := by
    intro r hr
    unfold dmat imatTranspose at hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    have hlen : ((List.range (imatRows (dmatCols w))).map fun i =>
        imatGet (dmatCols w) i j).length = (monoW w).length := by
      simp [imatRows, dmatCols_length]
    omega
  have hne : dmat w ≠ [] := by
    intro hcon
    have hcc := congrArg List.length hcon
    have hlen : (dmat w).length = (monoW w).length := imatRows_dmat w
    rw [hlen] at hcc
    have hnil : monoW w = [] :=
      List.eq_nil_of_length_eq_zero (by simpa using hcc)
    have hmem := monoW_mem_last w
    rw [hnil] at hmem
    simp at hmem
  obtain ⟨r0, rs, hrfl⟩ : ∃ r0 rs, dmat w = r0 :: rs :=
    List.exists_cons_of_ne_nil hne
  unfold imatCols
  rw [hrfl]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  exact h1 r0 (by simp [hrfl])

theorem transpose_entry (C : IMat) (i j : Nat) (hi : i < imatCols C)
    (hj : j < imatRows C) :
    imatGet (imatTranspose C) i j = imatGet C j i := by
  unfold imatTranspose imatGet imatRows
  have hj' : j < List.length C := hj
  rw [map_range_get _ _ _ hi, Option.bind_some, map_range_get _ _ _ hj',
    Option.getD_some]

-- Integer-valuedness infrastructure (denominator clearing).

theorem intCast_eq_divInt_one (z : Int) : ((z : Int) : Rat) = z /. 1 := by
  have hnum : (z /. 1).num = z := by simp [Rat.num_divInt]
  have hden : (z /. 1).den = 1 := by simp [Rat.den_divInt]
  have hcast : ((z : Int) : Rat) = Rat.ofInt z := rfl
  rw [hcast]
  exact Rat.ext (by simp [Rat.ofInt_num, hnum]) (by simp [Rat.ofInt_den, hden])

theorem den_ne_zero (c : Rat) (hc : c ≠ 0) : c.den ≠ 0 := by
  intro hz
  have hcc := Rat.num_divInt_den c
  rw [hz] at hcc
  have hcc0 : c.num /. 0 = c := hcc
  rw [Rat.divInt_zero] at hcc0
  exact hc hcc0.symm

theorem prod_ne_zero (l : List Nat) (h : ∀ n ∈ l, n ≠ 0) : l.prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have h1 := h hd (by simp)
    have h2 := ih (fun n hn => h n (List.mem_cons_of_mem _ hn))
    simp only [List.prod_cons]
    intro hcon
    exact (Nat.mul_eq_zero.mp hcon).elim h1 h2

theorem den_dvd_prod (l : List Nat) (d : Nat) (h : d ∈ l) : d ∣ l.prod := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.prod_cons, List.mem_cons] at h ⊢
    cases h with
    | inl heq => subst heq; exact Nat.dvd_mul_right _ _
    | inr hmem =>
      obtain ⟨c1, hc1⟩ := ih hmem
      exact ⟨hd * c1, by
        rw [hc1, ← Nat.mul_assoc, Nat.mul_comm hd d, Nat.mul_assoc]⟩

theorem smul_intValued (L K : Nat) (c : Rat) (hL : L = c.den * K) :
    ∃ z : Int, (((L : Nat) : Rat)) * c = ((z : Int)) := by
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc, Rat.mul_zero, Rat.intCast_ofNat]⟩
  · have hden : c.den ≠ 0 := den_ne_zero c hc
    have hdenI : ((c.den : Nat) : Int) ≠ 0 := by
      simpa [Int.natCast_eq_zero] using hden
    have hLI : (((L : Nat) : Int)) = ((c.den : Nat) : Int) * ((K : Nat) : Int) := by
      rw [hL, Int.natCast_mul]
    have hLc : (((L : Nat) : Rat)) = ((((L : Nat) : Int))) :=
      (Rat.intCast_natCast L).symm
    have hDc : ((((c.den : Nat) : Int)) : Rat) * c = ((c.num : Int)) := by
      have s1 : ((((c.den : Nat) : Int)) : Rat) * c =
          ((((c.den : Nat) : Int)) : Rat) * (c.num /. (((c.den : Nat) : Int))) :=
        congrArg _ (Rat.num_divInt_den c).symm
      have s2 : ((((c.den : Nat) : Int)) : Rat) * (c.num /. (((c.den : Nat) : Int))) =
          ((c.num * (((c.den : Nat) : Int))) /. (((c.den : Nat) : Int))) := by
        rw [intCast_eq_divInt_one (((c.den : Nat) : Int)),
          Rat.divInt_mul_divInt, Int.one_mul,
          Int.mul_comm (((c.den : Nat) : Int)) (c.num)]
      have s3 : ((c.num * (((c.den : Nat) : Int))) /. (((c.den : Nat) : Int))) =
          c.num /. 1 :=
        (Rat.divInt_eq_divInt_iff hdenI (by decide)).mpr (Int.mul_one _)
      exact s1.trans (s2.trans (s3.trans (intCast_eq_divInt_one c.num).symm))
    have hswap : ((((c.den : Nat) : Int)) : Rat) * ((((K : Nat) : Int)) : Rat) * c =
        ((((K : Nat) : Int)) : Rat) * (((((c.den : Nat) : Int)) : Rat) * c) := by
      rw [← Rat.mul_assoc, Rat.mul_comm ((((c.den : Nat) : Int)) : Rat)
        ((((K : Nat) : Int)) : Rat), Rat.mul_assoc]
    rw [hLc, hLI, Rat.intCast_mul, hswap, hDc]
    exact ⟨((K : Nat) : Int) * c.num, (Rat.intCast_mul _ _).symm⟩

/-- One coordinate entry: integer part of the coefficient at `e`. -/
def coordEntry (p : Poly) (e : Exp) : Int :=
  (((p.find? (fun m => m.2 == e)).map (fun m => m.1.num)).getD 0)

theorem find_eval_num (p : Poly) (e : Exp)
    (hInt : ∀ m ∈ p, ∃ z : Int, m.1 = (z : Rat))
    (hnd : hasNoDups p) :
    coordEntry p e = (evalCoeff p e).num := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨c, e'⟩ := hd
    have hInt_tl : ∀ m ∈ tl, ∃ z : Int, m.1 = (z : Rat) :=
      fun m hm => hInt m (List.mem_cons_of_mem _ hm)
    have hnd2 : (e' :: (tl.map (·.2))).Nodup := hnd
    have hnd_tl : hasNoDups tl := (List.nodup_cons.mp hnd2).2
    cases he : (e' == e) with
    | true =>
      have heq : e' = e := beq_iff_eq.mp he
      subst e'
      have htl0 : evalCoeff tl e = 0 :=
        evalCoeff_missing tl e (fun m hm => by
          intro hcon
          have hmem : e ∈ tl.map (·.2) := by
            rw [← hcon]
            exact List.mem_map.mpr ⟨m, hm, rfl⟩
          exact (List.nodup_cons.mp hnd2).1 hmem)
      have hfind : ((c, e) :: tl).find? (fun m => m.2 == e) = some (c, e) := by
        simp
      simp only [coordEntry, hfind, Option.map_some, Option.getD_some]
      rw [evalCoeff_cons_pair, if_pos rfl, htl0, Rat.add_zero]
    | false =>
      have hne : e' ≠ e := ne_of_beq_false he
      have hfind : ((c, e') :: tl).find? (fun m => m.2 == e) =
          tl.find? (fun m => m.2 == e) := by
        simp [he]
      simp only [coordEntry, hfind]
      rw [evalCoeff_cons, if_neg hne, Rat.zero_add]
      exact ih hInt_tl hnd_tl

theorem map_coordEntry (dom : List Exp) (p : Poly) :
    ∀ (i : Nat) (hi : i < dom.length),
    ((dom.map (coordEntry p))[i]? = some (coordEntry p (dom[i]'hi))) := by
  induction dom with
  | nil =>
    intro i hi
    simp at hi
  | cons hd tl ih =>
    intro i hi
    revert hi
    cases i with
    | zero => intro hi; simp
    | succ j =>
      intro hi
      have hj : j < tl.length := by
        have hlen : (hd :: tl).length = tl.length + 1 := rfl
        omega
      simp only [List.map_cons, List.getElem?_cons_succ]
      exact ih j hj

theorem coordIn_eval (dom : List Exp) (p : Poly)
    (hInt : ∀ m ∈ p, ∃ z : Int, m.1 = (z : Rat))
    (hnd : hasNoDups p) (i : Nat) (hi : i < dom.length) :
    (((coordIn dom p)[i]?.getD 0 : Int)) = (evalCoeff p (dom[i])).num := by
  have hco : coordIn dom p = dom.map (coordEntry p) := rfl
  rw [hco, map_coordEntry dom p i hi, Option.getD_some]
  exact find_eval_num p _ hInt hnd

-- Homogeneous/support predicates + weighted-degree membership.

/-- All terms have `(8,5,3,2,1,1)`-weight `w`. -/
def homogeneous (F : Poly) (w : Nat) : Prop :=
  ∀ m ∈ F, expWeight m.2 = w

/-- All exponents are 6-vectors (inside the ambient ring). -/
def supp6 (F : Poly) : Prop := ∀ m ∈ F, m.2.length = 6

theorem foldl_max_ge (l : List Mono) (b : Nat) :
    b ≤ l.foldl (fun acc m => Nat.max acc (expWeight m.2)) b := by
  induction l generalizing b with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldl_max_mono (l : List Mono) (b1 b2 : Nat) (h : b1 ≤ b2) :
    l.foldl (fun acc m => Nat.max acc (expWeight m.2)) b1 ≤
      l.foldl (fun acc m => Nat.max acc (expWeight m.2)) b2 := by
  induction l generalizing b1 b2 with
  | nil =>
    simpa using h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (Nat.max_le_of_le_of_le
      (Nat.le_trans h (Nat.le_max_left _ _)) (Nat.le_max_right _ _))

theorem foldl_max_mem (F : Poly) (m : Mono) (hm : m ∈ F) (b : Nat) :
    expWeight m.2 ≤ F.foldl (fun acc m => Nat.max acc (expWeight m.2)) b := by
  induction F with
  | nil => simp at hm
  | cons hd tl ih =>
    simp only [List.mem_cons] at hm
    cases hm with
    | inl heq =>
      rw [heq]
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_right b _) (foldl_max_ge tl _)
    | inr hmem =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (ih hmem)
        (foldl_max_mono tl b (Nat.max b (expWeight hd.2))
          (Nat.le_max_left _ _))

theorem wdeg_mem (F : Poly) (m : Mono) (hm : m ∈ F) :
    expWeight m.2 ≤ weightedDegree F := by
  unfold weightedDegree
  exact foldl_max_mem F m hm 0

-- Smul-compatibilities of the D building blocks (eval level).

theorem eval_map_sum (q : Poly) (G : Mono → Mono) (x : Exp) :
    evalCoeff (q.map G) x =
      (q.map fun m2 => evalCoeff [G m2] x).sum := by
  induction q with
  | nil => simp [evalCoeff_nil]
  | cons hd tl ih =>
    simp only [List.map_cons, evalCoeff_cons, evalCoeff_nil, List.sum_cons,
      Rat.add_zero, ih]

theorem eval_singleton (C : Rat) (E x : Exp) :
    evalCoeff [(C, E)] x = (if E = x then C else 0) := by
  rw [evalCoeff_cons, evalCoeff_nil, Rat.add_zero]

theorem evalsmulmap (a : Int) (q : Poly) (H : Mono → Mono) (x : Exp)
    (hH : ∀ m2 ∈ q, evalCoeff [H (((a : Rat) * m2.1), m2.2)] x =
      (a : Rat) * evalCoeff [H m2] x) :
    evalCoeff ((polySmulInt a q).map H) x =
      (a : Rat) * evalCoeff (q.map H) x := by
  rw [eval_map_sum, eval_map_sum, mul_sum_dist]
  unfold polySmulInt
  rw [List.map_map, List.map_map]
  apply congrArg
  apply List.map_inj_left.mpr
  intro m2 hm2
  exact hH m2 hm2

theorem evalsmulmulR (a : Int) (p q : Poly) (x : Exp) :
    evalCoeff (polyMul p (polySmulInt a q)) x =
      (a : Rat) * evalCoeff (polyMul p q) x := by
  rw [evalCoeff_polyMul, evalCoeff_polyMul, evalCoeff_flatMap,
    evalCoeff_flatMap, mul_sum_dist, List.map_map]
  apply congrArg
  apply List.map_inj_left.mpr
  intro m1 _
  obtain ⟨c1, e1⟩ := m1
  apply evalsmulmap
  intro m2 _
  obtain ⟨c2, e2⟩ := m2
  simp only [eval_singleton, mulMono_correct]
  by_cases hE : addExp e1 e2 = x
  · simp only [hE, if_true]
    rw [← Rat.mul_assoc, Rat.mul_comm (c1 : Rat) _, Rat.mul_assoc]
  · simp only [hE, if_false, Rat.mul_zero]

theorem derivMono_smul (a : Int) (i : Fin 6) (c : Rat) (e : Exp) :
    derivMono i (((a : Rat) * c), e) =
      ((derivMono i (c, e)).map fun m' => (((a : Rat)) * m'.1, m'.2)) := by
  unfold derivMono
  cases h : e[i.val]? with
  | none => rfl
  | some v =>
    cases v with
    | zero => rfl
    | succ n =>
      simp only [Option.map_some, Rat.mul_assoc]

theorem evalsmulpartial (a : Int) (i : Fin 6) (F : Poly) (x : Exp) :
    evalCoeff (partialDeriv i (polySmulInt a F)) x =
      (a : Rat) * evalCoeff (partialDeriv i F) x := by
  have e1 : evalCoeff (partialDeriv i (polySmulInt a F)) x =
      evalCoeff ((polySmulInt a F).filterMap (derivMono i)) x := by
    rw [partialDeriv_def, evalCoeff_normalize]
  have e2 : evalCoeff (partialDeriv i F) x =
      evalCoeff (F.filterMap (derivMono i)) x := by
    rw [partialDeriv_def, evalCoeff_normalize]
  rw [e1, e2, evalCoeff_filterMap, evalCoeff_filterMap, evalCoeff_flatMap,
    evalCoeff_flatMap, mul_sum_dist]
  unfold polySmulInt
  rw [List.map_map, List.map_map]
  apply congrArg
  apply List.map_inj_left.mpr
  intro m _
  obtain ⟨c, e⟩ := m
  simp only [Function.comp_apply]
  rw [derivMono_smul]
  cases h : derivMono i (c, e) with
  | none =>
    simp only [Option.map_none, Option.toList_none, evalCoeff_nil, Rat.mul_zero]
  | some m' =>
    obtain ⟨c', e'⟩ := m'
    simp only [Option.map_some, Option.toList_some, eval_singleton]
    by_cases hE : e' = x
    · rw [if_pos hE, if_pos hE]
    · rw [if_neg hE, if_neg hE, Rat.mul_zero]

-- Linchpin: evaluation through mapped normalization (mulMono shifts).

theorem eval_singleton_mulMono (ca : Rat) (ea : Exp) (c : Rat) (e x : Exp) :
    evalCoeff [mulMono (ca, ea) (c, e)] x =
      (if addExp ea e = x then ca * c else 0) := by
  rw [mulMono_correct, eval_singleton]

theorem eval_map_Go (ca : Rat) (ea : Exp) (m : Mono) (Q : Poly) (x : Exp) :
    evalCoeff ((insertCombineGo m Q).map (mulMono (ca, ea))) x =
      evalCoeff [mulMono (ca, ea) m] x +
        evalCoeff (Q.map (mulMono (ca, ea))) x := by
  induction Q with
  | nil =>
    simp only [insertCombineGo, List.map_cons, List.map_nil, evalCoeff_nil,
      Rat.add_zero]
  | cons hd tl ih =>
    obtain ⟨c', e'⟩ := hd
    obtain ⟨cm, em⟩ := m
    have econs : ∀ (a : Mono) (l : Poly),
        evalCoeff (((a :: l)).map (mulMono (ca, ea))) x =
          evalCoeff [mulMono (ca, ea) a] x +
            evalCoeff (l.map (mulMono (ca, ea))) x := by
      intro a l
      simp only [List.map_cons, evalCoeff_cons, evalCoeff_nil, Rat.add_zero]
    by_cases he : e' = em
    · by_cases hzero : c' + cm = 0
      · simp only [insertCombineGo, he, hzero, if_true]
        simp only [econs]
        have h0 : evalCoeff [mulMono (ca, ea) (cm, em)] x +
            evalCoeff [mulMono (ca, ea) (c', em)] x = 0 := by
          rw [eval_singleton_mulMono, eval_singleton_mulMono]
          by_cases hc : addExp ea em = x
          · rw [if_pos hc, if_pos hc, ← Rat.mul_add]
            have hz : cm + c' = 0 := by
              rw [Rat.add_comm]
              exact hzero
            rw [hz, Rat.mul_zero]
          · rw [if_neg hc, if_neg hc, Rat.add_zero]
        rw [← Rat.add_assoc, h0, Rat.zero_add]
      · simp only [insertCombineGo, he, hzero, if_true, if_false]
        simp only [econs]
        rw [eval_singleton_mulMono, eval_singleton_mulMono,
          eval_singleton_mulMono]
        by_cases hc : addExp ea em = x
        · rw [if_pos hc, if_pos hc, if_pos hc, Rat.mul_add]
          ac_rfl
        · rw [if_neg hc, if_neg hc, if_neg hc]
          simp only [Rat.zero_add]
    · simp only [insertCombineGo, he, if_false]
      simp only [econs]
      rw [ih]
      ac_rfl

theorem eval_map_insertCombine (ca : Rat) (ea : Exp) (m : Mono) (Q : Poly)
    (x : Exp) :
    evalCoeff ((insertCombine m Q).map (mulMono (ca, ea))) x =
      evalCoeff [mulMono (ca, ea) m] x +
        evalCoeff (Q.map (mulMono (ca, ea))) x := by
  obtain ⟨cm, em⟩ := m
  have econs : ∀ (a : Mono) (l : Poly),
      evalCoeff (((a :: l)).map (mulMono (ca, ea))) x =
        evalCoeff [mulMono (ca, ea) a] x +
          evalCoeff (l.map (mulMono (ca, ea))) x := by
    intro a l
    simp only [List.map_cons, evalCoeff_cons, evalCoeff_nil, Rat.add_zero]
  by_cases h0 : cm = 0
  · simp only [insertCombine, h0, if_true]
    have hz : evalCoeff [mulMono (ca, ea) ((0 : Rat), em)] x = 0 := by
      rw [eval_singleton_mulMono]
      by_cases hc : addExp ea em = x
      · rw [if_pos hc, Rat.mul_zero]
      · rw [if_neg hc]
    rw [hz, Rat.zero_add]
  · by_cases hmem : em ∈ Q.map (·.2)
    · simp only [insertCombine, h0, hmem, if_true, if_false]
      rw [eval_map_Go]
    · simp only [insertCombine, h0, hmem, if_false]
      exact econs _ _

theorem econs_combine (ca : Rat) (ea : Exp) (a : Mono) (l : Poly) (x : Exp) :
    evalCoeff [mulMono (ca, ea) a] x + evalCoeff (l.map (mulMono (ca, ea))) x =
      evalCoeff (((a :: l)).map (mulMono (ca, ea))) x := by
  simp only [List.map_cons, evalCoeff_cons, evalCoeff_nil, Rat.add_zero]

theorem eval_map_combine (ca : Rat) (ea : Exp) (Z : Poly) (x : Exp) :
    evalCoeff ((combine Z).map (mulMono (ca, ea))) x =
      evalCoeff (Z.map (mulMono (ca, ea))) x := by
  induction Z with
  | nil => rfl
  | cons hd tl ih =>
    simp only [combine]
    rw [eval_map_insertCombine, ih, econs_combine]

theorem eval_map_sortPoly (ca : Rat) (ea : Exp) (Z : Poly) (x : Exp) :
    evalCoeff ((sortPoly Z).map (mulMono (ca, ea))) x =
      evalCoeff (Z.map (mulMono (ca, ea))) x := by
  have hP := sortPoly_perm Z
  have hPm := List.Perm.map (mulMono (ca, ea)) hP
  exact evalCoeff_perm _ _ hPm _

theorem normalize_map_mulMono (ca : Rat) (ea : Exp) (Y : Poly) (x : Exp) :
    evalCoeff ((normalize Y).map (mulMono (ca, ea))) x =
      evalCoeff (Y.map (mulMono (ca, ea))) x := by
  have e1 : ((normalize Y).map (mulMono (ca, ea))) =
      ((sortPoly (combine Y)).map (mulMono (ca, ea))) := rfl
  rw [e1, eval_map_sortPoly, eval_map_combine]

theorem filterMap_smul_commute (a : Int) (i : Fin 6) (F : Poly) :
    (polySmulInt a F).filterMap (derivMono i) =
      ((F.filterMap (derivMono i)).map fun m' => (((a : Rat)) * m'.1, m'.2)) := by
  induction F with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨c, e⟩ := hd
    simp only [polySmulInt, List.map_cons]
    cases h : derivMono i (c, e) with
    | none =>
      have hf : derivMono i (((a : Rat) * c), e) = none := by
        rw [derivMono_smul]
        simp [h]
      simp only [List.filterMap, hf, h]
      exact ih
    | some m' =>
      obtain ⟨c', e'⟩ := m'
      have hf : derivMono i (((a : Rat) * c), e) =
          some ((((a : Rat)) * c'), e') := by
        rw [derivMono_smul, h]
        simp
      simp only [List.filterMap, hf, h, List.map_cons]
      exact congrArg (fun l => (((a : Rat) * c'), e') :: l) ih

theorem evalDterm_inner (a : Int) (caa : Rat) (eaa : Exp) (ji : Fin 6)
    (F : Poly) (x : Exp) :
    evalCoeff (((partialDeriv ji (polySmulInt a F))).map (mulMono (caa, eaa))) x =
      (a : Rat) * evalCoeff (((partialDeriv ji F)).map (mulMono (caa, eaa))) x := by
  simp only [partialDeriv_def]
  rw [normalize_map_mulMono, normalize_map_mulMono, filterMap_smul_commute,
    eval_map_sum, eval_map_sum, mul_sum_dist, List.map_map, List.map_map]
  apply congrArg
  apply List.map_inj_left.mpr
  intro t _
  obtain ⟨c', e'⟩ := t
  simp only [Function.comp_apply]
  rw [eval_singleton_mulMono, eval_singleton_mulMono]
  by_cases hc : addExp eaa e' = x
  · rw [if_pos hc, if_pos hc, ← Rat.mul_assoc, Rat.mul_comm (caa : Rat) _,
      Rat.mul_assoc]
  · rw [if_neg hc, if_neg hc, Rat.mul_zero]

theorem evalDterm_ti (a : Int) (Ai : Poly) (ji : Fin 6) (F : Poly) (x : Exp) :
    evalCoeff (polyMul Ai (partialDeriv ji (polySmulInt a F))) x =
      (a : Rat) * evalCoeff (polyMul Ai (partialDeriv ji F)) x := by
  simp only [evalCoeff_polyMul, evalCoeff_flatMap]
  rw [mul_sum_dist, List.map_map]
  apply congrArg
  apply List.map_inj_left.mpr
  intro am _
  obtain ⟨caa, eaa⟩ := am
  exact evalDterm_inner _ _ _ _ _ _

theorem evalDsmul (a : Int) (F : Poly) (x : Exp) :
    evalCoeff (D (polySmulInt a F)) x = (a : Rat) * evalCoeff (D F) x := by
  have hL := D_def (polySmulInt a F)
  have hR := D_def F
  rw [hL, hR]
  simp only [evalCoeff_polyAdd, evalDterm_ti, Rat.mul_add]

theorem sum_map_add (l : List α) (f g : α → Rat) :
    ((l.map fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, Rat.add_zero]
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ac_rfl

theorem evalDterm_add (Ai : Poly) (ji : Fin 6) (p q : Poly) (x : Exp) :
    evalCoeff (polyMul Ai (partialDeriv ji (p ++ q))) x =
      evalCoeff (polyMul Ai (partialDeriv ji p)) x +
        evalCoeff (polyMul Ai (partialDeriv ji q)) x := by
  simp only [partialDeriv_def, evalCoeff_polyMul, evalCoeff_flatMap]
  rw [← sum_map_add]
  apply congrArg
  apply List.map_inj_left.mpr
  intro am _
  obtain ⟨caa, eaa⟩ := am
  simp only [normalize_map_mulMono, List.filterMap_append, List.map_append,
    evalCoeff_append]

theorem evalD_add (p q : Poly) (x : Exp) :
    evalCoeff (D (p ++ q)) x = evalCoeff (D p) x + evalCoeff (D q) x := by
  have hL := D_def (p ++ q)
  have hR1 := D_def p
  have hR2 := D_def q
  rw [hL, hR1, hR2]
  simp only [evalCoeff_polyAdd, evalDterm_add]
  ac_rfl

theorem evalD_eq (F : Poly) (x : Exp) :
    evalCoeff (D F) x =
      ((F.map fun m => evalCoeff (D [m]) x)).sum := by
  induction F with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    rw [D_zero, evalCoeff_normalize, evalCoeff_nil]
  | cons hd tl ih =>
    rw [show (hd :: tl) = ([hd] ++ tl) from rfl, evalD_add, ih]
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil, Rat.add_zero]

theorem polyDsmul (a : Int) (ha : a ≠ 0) (F : Poly) :
    D (polySmulInt a F) = polySmulInt a (D F) := by
  have e : ∀ x, evalCoeff (D (polySmulInt a F)) x =
      evalCoeff (polySmulInt a (D F)) x := by
    intro x
    rw [evalCoeff_polySmulInt, evalDsmul]
  have hL0 : hasNoZeros (D (polySmulInt a F)) := by
    rw [D_def]
    exact normalize_noZeros _
  have hLd : hasNoDups (D (polySmulInt a F)) := by
    rw [D_def]
    exact normalize_nodup _
  have hLp : List.Pairwise (fun a b => monoLE a b = true)
      (D (polySmulInt a F)) := by
    rw [D_def]
    exact sortPoly_pairwise _
  have hR0 := smul_noZeros a ha (D F) (by rw [D_def]; exact normalize_noZeros _)
  have hRd := smul_nodup a (D F) (by rw [D_def]; exact normalize_nodup _)
  have hRp := smul_pairwise a (D F) (by rw [D_def]; exact sortPoly_pairwise _)
  exact normalized_eq_of_same_eval _ _ hL0 hR0 hLd hRd hLp hRp e

theorem Dweight_single (cc : Rat) (e : Exp) (h6 : e.length = 6) (m : Mono)
    (hm : m ∈ D [(cc, e)]) : expWeight m.2 = expWeight e :=
  dmono_weight cc e h6 m hm

theorem evalD_weight_zero (m : Mono) (hm6 : m.2.length = 6) (x : Exp)
    (hx : expWeight x ≠ expWeight m.2) : evalCoeff (D [m]) x = 0 := by
  obtain ⟨c, e⟩ := m
  apply evalCoeff_missing
  intro t ht hcon
  have hw := Dweight_single c e hm6 t ht
  rw [hcon] at hw
  exact hx (hw.trans rfl)

/-- Matrix times column vector (right-kernel convention for `dmat`). -/
def matVecMul (M : IMat) (v : List Int) : List Int :=
  (List.range (imatRows M)).map fun i =>
    (List.range v.length).foldl
      (fun acc j => acc + imatGet M i j * ((v[j]?).getD 0)) 0

theorem matVecMul_length (M : IMat) (v : List Int) :
    (matVecMul M v).length = imatRows M := by
  simp [matVecMul]

theorem mat_entry_cast (M : IMat) (v : List Int) (i : Nat)
    (hi : i < imatRows M) :
    ((((matVecMul M v)[i]?.getD 0 : Int)) : Rat) =
      ((List.range v.length).map fun j =>
        ((imatGet M i j : Int) : Rat) * ((v[j]?.getD 0 : Int) : Rat)).sum := by
  unfold matVecMul
  rw [map_range_get _ _ _ hi, Option.getD_some, intCast_foldl_range]
  apply congrArg
  apply List.map_inj_left.mpr
  intro j _
  simp only [Rat.intCast_mul]

theorem eval_intValued (p : Poly) (e : Exp)
    (h : ∀ m ∈ p, ∃ z : Int, m.1 = (z : Rat)) :
    ∃ z : Int, evalCoeff p e = (z : Rat) := by
  induction p with
  | nil => exact ⟨0, by simp [evalCoeff_nil, Rat.intCast_ofNat]⟩
  | cons hd tl ih =>
    obtain ⟨z1, hz1⟩ := h hd (by simp)
    obtain ⟨z2, hz2⟩ := ih (fun m hm => h m (List.mem_cons_of_mem _ hm))
    by_cases he : hd.2 = e
    · exact ⟨z1 + z2, by
        simp [evalCoeff_cons, he, hz1, hz2, Rat.intCast_add]⟩
    · exact ⟨z2, by
        simp [evalCoeff_cons, he, hz2, Rat.zero_add]⟩

theorem coord_cast_getD (dom : List Exp) (F' : Poly) (i : Nat)
    (hmem : i ∈ List.range dom.length)
    (hInt : ∀ m ∈ F', ∃ z : Int, m.1 = (z : Rat))
    (hnd : hasNoDups F') :
    ((((coordIn dom F')[i]?.getD 0 : Int)) : Rat) =
      evalCoeff F' (dom[i]?.getD []) := by
  have hii : i < dom.length := List.mem_range.mp hmem
  have hentry := coordIn_eval dom F' hInt hnd i hii
  have hget : dom[i]? = some (dom[i]'hii) := List.getElem?_eq_getElem hii
  have hint : ∃ z : Int, evalCoeff F' (dom[i]'hii) = (z : Rat) :=
    eval_intValued F' _ hInt
  rw [hentry]
  obtain ⟨z, hz⟩ := hint
  rw [hz, Rat.num_intCast, hget, Option.getD_some]
  exact hz.symm


theorem dmat_entry_cast_getD (w i j : Nat)
    (hmem : i ∈ List.range (monoW w).length) (hj : j < (monoW w).length)
    (hInt : ∀ e ∈ monoW w,
      ∀ m ∈ D [((1 : Rat), e)], ∃ z : Int, m.1 = (z : Rat)) :
    ((((imatGet (dmat w) i j : Int)) : Rat)) =
      evalCoeff (D (basisPoly ((monoW w)[j]'hj))) ((monoW w)[i]?.getD []) := by
  have hii : i < (monoW w).length := List.mem_range.mp hmem
  have hunfold : dmat w = imatTranspose (dmatCols w) := rfl
  have hiC : i < imatCols (dmatCols w) := by
    rw [imatCols_dmatCols]
    exact hii
  have hjR : j < imatRows (dmatCols w) := by
    show j < (dmatCols w).length
    rw [dmatCols_length]
    exact hj
  rw [hunfold, transpose_entry _ _ _ hiC hjR]
  -- imatGet (dmatCols w) j i, with j < n
  have hmem2 : ((monoW w)[j]'hj) ∈ monoW w := List.getElem_mem hj
  have hrow : ((dmatCols w)[j]?) =
      some (coordIn (monoW w)
        (D (basisPoly ((monoW w)[j]?.getD [0,0,0,0,0,0])))) := by
    unfold dmatCols
    rw [map_range_get _ _ _ hj]
  have hndD : hasNoDups (D (basisPoly ((monoW w)[j]'hj))) := by
    rw [D_def]
    exact normalize_nodup _
  simp only [imatGet, hrow, Option.bind_some]
  have hentry := coordIn_eval (monoW w)
    (D (basisPoly ((monoW w)[j]'hj)))
    (fun m hm => hInt _ hmem2 m hm) hndD i hii
  have hint : ∃ z : Int,
      evalCoeff (D (basisPoly ((monoW w)[j]'hj))) ((monoW w)[i]'hii) =
        (z : Rat) :=
    eval_intValued _ _ (fun m hm => hInt _ hmem2 m hm)
  have hg1 : ((monoW w)[i]?.getD []) = (monoW w)[i]'hii := by
    rw [List.getElem?_eq_getElem hii, Option.getD_some]
  have hg2 : ((monoW w)[j]?.getD [0,0,0,0,0,0]) = (monoW w)[j]'hj := by
    rw [List.getElem?_eq_getElem hj, Option.getD_some]
  rw [hg2, hentry]
  obtain ⟨z, hz⟩ := hint
  rw [hz, Rat.num_intCast, hg1]
  exact hz.symm

theorem eval_as_sum (L : Poly) (x : Exp) :
    evalCoeff L x = ((L.map fun t => evalCoeff [t] x)).sum := by
  induction L with
  | nil => simp [evalCoeff_nil]
  | cons hd tl ih =>
    simp only [evalCoeff_cons, List.map_cons, List.sum_cons, evalCoeff_nil,
      Rat.add_zero, ih]

theorem sum_partition (l : Poly) (P : Mono → Bool) (f : Mono → Rat) :
    (l.map f).sum =
      (((l.filter P).map f)).sum + (((l.filter (fun m => !P m)).map f)).sum := by
  induction l with
  | nil => simp [Rat.add_zero]
  | cons hd tl ih =>
    by_cases h : P hd = true
    · simp [h, ih, Rat.add_assoc]
    · simp [h, ih]
      ac_rfl

theorem eval_agree (F' : Poly) (m0 : Mono) (e : Exp) (hne : m0.2 ≠ e) :
    evalCoeff F' m0.2 =
      evalCoeff (F'.filter (fun m => !(m.2 == e))) m0.2 := by
  rw [eval_as_sum, eval_as_sum]
  have hsplit := sum_partition F' (fun m => m.2 == e)
    (fun t => evalCoeff [t] m0.2)
  have hzero : (((F'.filter (fun m => m.2 == e)).map
      fun t => evalCoeff [t] m0.2)).sum = 0 := by
    apply sum_zero_terms
    intro t ht
    have hte : t.2 = e := beq_iff_eq.mp (List.mem_filter.mp ht).2
    rw [eval_singleton]
    have hne' : t.2 ≠ m0.2 := by
      rw [hte]
      exact Ne.symm hne
    rw [if_neg hne']
  rw [hsplit, hzero, Rat.zero_add]

theorem filter_eq_nil (l : Poly) (P : Mono → Bool)
    (h : ∀ m ∈ l, P m = false) : l.filter P = [] := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : P hd = false := h _ (by simp)
    have hneg : ¬P hd := by simpa using hhd
    rw [List.filter_cons_of_neg (p := P) (a := hd) (l := tl) hneg]
    exact ih (fun m hm => h m (List.mem_cons_of_mem _ hm))

theorem filter_exp_singleton (l : Poly) (e : Exp)
    (hnd : (l.map (·.2)).Nodup) (hall : ∀ t ∈ l, t.2 = e) (hne : l ≠ []) :
    ∃ t₁, l = [t₁] := by
  cases l with
  | nil => exact absurd rfl hne
  | cons hd tl =>
    by_cases htl : tl = []
    · subst htl
      exact ⟨hd, rfl⟩
    · obtain ⟨t', ht'mem⟩ : ∃ t', t' ∈ tl := by
        cases tl with
        | nil => exact absurd rfl htl
        | cons t' _ => exact ⟨t', by simp⟩
      have h1 : hd.2 = e := hall hd (by simp)
      have h2 : t'.2 = e := hall t' (List.mem_cons_of_mem _ ht'mem)
      have hnd2 : (hd.2 :: (tl.map (·.2))).Nodup := hnd
      have hmem : e ∈ tl.map (·.2) := by
        rw [← h2]
        exact List.mem_map.mpr ⟨t', ht'mem, rfl⟩
      have hfin : hd.2 ∈ tl.map (·.2) := by
        rw [h1]
        exact hmem
      exact absurd hfin (List.nodup_cons.mp hnd2).1

theorem range_dom_sum (dom : List Exp) (H : Exp → Rat) :
    (((List.range dom.length).map fun i => H (dom[i]?.getD []))).sum =
      ((dom.map H)).sum := by
  induction dom with
  | nil => rfl
  | cons e es ih =>
    simp only [List.length_cons]
    rw [range_succ_head]
    simp only [List.map_cons, List.sum_cons, List.getElem?_cons_zero,
      Option.getD_some]
    rw [List.map_map]
    have htail : (((List.range es.length).map
        ((fun i => H ((e :: es)[i]?.getD [])) ∘ fun i => i + 1))).sum =
        (((List.range es.length).map fun i => H (es[i]?.getD []))).sum := by
      apply congrArg
      apply List.map_inj_left.mpr
      intro i _
      simp only [Function.comp_apply, List.getElem?_cons_succ]
    rw [htail, ih]

theorem map_filter_sublist (l : Poly) (P : Mono → Bool) (f : Mono → Exp) :
    (((l.filter P).map f)).Sublist ((l.map f)) := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons hd tl ih =>
    by_cases h : P hd = true
    · rw [List.filter_cons_of_pos (p := P) (a := hd) (l := tl) h]
      simp only [List.map_cons]
      exact List.Sublist.cons_cons _ ih
    · have hneg : ¬P hd := by simpa using h
      rw [List.filter_cons_of_neg (p := P) (a := hd) (l := tl) hneg]
      exact List.Sublist.cons _ ih

theorem eval_agree_exp (F' : Poly) (x e : Exp) (hne : x ≠ e) :
    evalCoeff F' x =
      evalCoeff (F'.filter (fun m => !(m.2 == e))) x := by
  rw [eval_as_sum, eval_as_sum]
  have hsplit := sum_partition F' (fun m => m.2 == e)
    (fun t => evalCoeff [t] x)
  have hzero : (((F'.filter (fun m => m.2 == e)).map
      fun t => evalCoeff [t] x)).sum = 0 := by
    apply sum_zero_terms
    intro t ht
    have hte : t.2 = e := beq_iff_eq.mp (List.mem_filter.mp ht).2
    rw [eval_singleton]
    have hne' : t.2 ≠ x := by
      rw [hte]
      exact Ne.symm hne
    rw [if_neg hne']
  rw [hsplit, hzero, Rat.zero_add]

theorem dom_sum (dom : List Exp) (F' : Poly) (B : Exp → Rat)
    (hdom : dom.Nodup) (hFnd : hasNoDups F')
    (hsub : ∀ m ∈ F', m.2 ∈ dom) :
    ((dom.map fun e => evalCoeff F' e * B e)).sum =
      ((F'.map fun m => evalCoeff F' m.2 * B m.2)).sum := by
  revert F' hFnd hsub
  induction dom with
  | nil =>
    intro F' hFnd hsub
    have hnil : F' = [] := by
      cases F' with
      | nil => rfl
      | cons hd tl =>
        have hcon := hsub hd (by simp)
        simp at hcon
    subst hnil
    rfl
  | cons e es ih =>
    intro F' hFnd hsub
    simp only [List.map_cons, List.sum_cons]
    have hsplit := sum_partition F' (fun m => m.2 == e)
      (fun m => evalCoeff F' m.2 * B m.2)
    by_cases hpres : e ∈ F'.map (·.2)
    · obtain ⟨t₀, ht₀mem, ht₀eq⟩ := List.mem_map.mp hpres
      have hFe_mem : t₀ ∈ F'.filter (fun m => m.2 == e) := by
        apply List.mem_filter.mpr
        refine ⟨ht₀mem, ?_⟩
        rw [ht₀eq]
        exact beq_self_eq_true _
      have hFe_nd : ((F'.filter (fun m => m.2 == e)).map (·.2)).Nodup :=
        List.Nodup.sublist (map_filter_sublist _ _ _) hFnd
      have hFe_all : ∀ t ∈ F'.filter (fun m => m.2 == e), t.2 = e := by
        intro t ht
        have hP := (List.mem_filter.mp ht).2
        exact beq_iff_eq.mp hP
      have hFe_ne : F'.filter (fun m => m.2 == e) ≠ [] :=
        List.ne_nil_of_mem hFe_mem
      obtain ⟨t₁, hsing⟩ := filter_exp_singleton _ _ hFe_nd hFe_all hFe_ne
      have ht1eq : t₁.2 = e := hFe_all t₁ (by rw [hsing]; simp)
      have hFee : (((F'.filter (fun m => m.2 == e)).map
          fun m => evalCoeff F' m.2 * B m.2)).sum =
          evalCoeff F' e * B e := by
        rw [hsing]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Rat.add_zero, ht1eq]
      have hFnd' : hasNoDups (F'.filter (fun m => !(m.2 == e))) :=
        List.Nodup.sublist (map_filter_sublist _ _ _) hFnd
      have hsub' : ∀ m ∈ F'.filter (fun m => !(m.2 == e)), m.2 ∈ es := by
        intro m hm
        have hmF := (List.mem_filter.mp hm).1
        have hme := hsub m hmF
        simp only [List.mem_cons] at hme
        cases hme with
        | inl heq =>
          have hP := (List.mem_filter.mp hm).2
          simp [heq] at hP
        | inr hmem => exact hmem
      have hFr : (((F'.filter (fun m => !(m.2 == e))).map
          fun m => evalCoeff F' m.2 * B m.2)).sum =
          (((es.map fun e => evalCoeff F' e * B e))).sum := by
        have hag : ∀ t ∈ F'.filter (fun m => !(m.2 == e)),
            evalCoeff F' t.2 * B t.2 =
              evalCoeff (F'.filter (fun m => !(m.2 == e))) t.2 * B t.2 := by
          intro t ht
          have hne : t.2 ≠ e := by
            have hnb : (t.2 == e) = false := by
              simpa using (List.mem_filter.mp ht).2
            exact ne_of_beq_false hnb
          rw [eval_agree_exp F' t.2 e hne]
        have hmap : (((F'.filter (fun m => !(m.2 == e))).map
            fun m => evalCoeff F' m.2 * B m.2)) =
            (((F'.filter (fun m => !(m.2 == e))).map
            fun m => evalCoeff (F'.filter (fun m => !(m.2 == e))) m.2 * B m.2)) := by
          apply List.map_inj_left.mpr
          intro t ht
          exact hag t ht
        have hes : (((es.map fun e_1 => evalCoeff F' e_1 * B e_1))).sum =
            (((es.map fun e_1 => evalCoeff (F'.filter (fun m => !(m.2 == e))) e_1 *
              B e_1))).sum := by
          apply congrArg
          apply List.map_inj_left.mpr
          intro eq heq
          have hne : eq ≠ e := by
            intro hcon
            have hmem : e ∈ es := by simpa [hcon] using heq
            exact (List.nodup_cons.mp hdom).1 hmem
          exact congrArg (· * B eq) (eval_agree_exp F' eq e hne)
        rw [hmap, hes]
        exact (ih ((List.nodup_cons.mp hdom).2) _ hFnd' hsub').symm
      rw [hsplit, hFee, hFr]
    · have hA0 : evalCoeff F' e = 0 :=
        evalCoeff_missing F' e (fun t ht => by
          intro hcon
          have hmem : e ∈ F'.map (·.2) := by
            rw [← hcon]
            exact List.mem_map.mpr ⟨t, ht, rfl⟩
          exact hpres hmem)
      have hsub' : ∀ m ∈ F', m.2 ∈ es := by
        intro m hm
        have hme := hsub m hm
        simp only [List.mem_cons] at hme
        cases hme with
        | inl heq =>
          have hcon : e ∈ F'.map (·.2) := by
            rw [← heq]
            exact List.mem_map.mpr ⟨m, hm, rfl⟩
          exact absurd hcon hpres
        | inr hmem => exact hmem
      rw [hA0, Rat.zero_mul, Rat.zero_add]
      exact ih ((List.nodup_cons.mp hdom).2) F' hFnd hsub'

theorem intCast_sum (l : List Rat) (h : ∀ c ∈ l, ∃ z : Int, c = (z : Rat)) :
    ∃ z : Int, l.sum = (z : Rat) := by
  induction l with
  | nil => exact ⟨0, by simp [Rat.intCast_ofNat]⟩
  | cons hd tl ih =>
    obtain ⟨z1, rfl⟩ := h hd (by simp)
    obtain ⟨z2, hz2⟩ := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    exact ⟨z1 + z2, by simp only [List.sum_cons]; rw [hz2, Rat.intCast_add]⟩


theorem evalDsmul_single (c : Rat) (e x : Exp) (hc : ∃ z : Int, c = (z : Rat)) :
    evalCoeff (D [(c, e)]) x = c * evalCoeff (D [((1 : Rat), e)]) x := by
  obtain ⟨z, rfl⟩ := hc
  have hsm : [((((z : Int)) : Rat), e)] = polySmulInt z [((1 : Rat), e)] := by
    simp [polySmulInt, Rat.mul_one]
  rw [hsm, evalDsmul]

theorem commondenom_ne_zero (F : Poly) (h0 : hasNoZeros F) :
    (F.map (fun m => m.1.den)).prod ≠ 0 := by
  apply prod_ne_zero
  intro n hn
  obtain ⟨m, hm, heq⟩ := List.mem_map.mp hn
  have heq2 : m.1.den = n := heq
  rw [← heq2]
  exact den_ne_zero _ (h0 m hm)

theorem eval_at_mem (F' : Poly) (m : Mono) (hm : m ∈ F')
    (hnd : hasNoDups F') (h0 : hasNoZeros F') :
    evalCoeff F' m.2 = m.1 := by
  induction F' with
  | nil => simp at hm
  | cons hd tl ih =>
    simp only [List.mem_cons] at hm
    cases hm with
    | inl heq =>
      rw [heq]
      have hnd2 : (hd.2 :: (tl.map (·.2))).Nodup := hnd
      have hmiss : ∀ t ∈ tl, t.2 ≠ hd.2 := by
        intro t ht hcon
        have hmem : hd.2 ∈ tl.map (·.2) := by
          rw [← hcon]
          exact List.mem_map.mpr ⟨t, ht, rfl⟩
        exact (List.nodup_cons.mp hnd2).1 hmem
      rw [evalCoeff_cons_pair, if_pos rfl]
      have h0t : evalCoeff tl hd.2 = 0 :=
        evalCoeff_missing tl hd.2 (fun t ht => by
          intro hcon
          exact hmiss t ht hcon)
      rw [h0t, Rat.add_zero]
    | inr hmem =>
      have hne : hd.2 ≠ m.2 := by
        intro hcon
        have hnd2 : (hd.2 :: (tl.map (·.2))).Nodup := hnd
        have hmem' : hd.2 ∈ tl.map (·.2) := by
          rw [hcon]
          exact List.mem_map.mpr ⟨m, hmem, rfl⟩
        exact (List.nodup_cons.mp hnd2).1 hmem'
      have h0t := h0 hd (by simp)
      have hndt : hasNoDups tl := (List.nodup_cons.mp hnd).2
      have h0tl : hasNoZeros tl :=
        fun t ht => h0 t (List.mem_cons_of_mem _ ht)
      rw [evalCoeff_cons, if_neg hne]
      simp only [Rat.zero_add]
      exact ih hmem hndt h0tl

def commondenom (F : Poly) : Nat := (F.map (fun m => m.1.den)).prod

theorem scaled_invariant (F : Poly) (w : Nat) (hnorm0 : hasNoZeros F)
    (hnormd : hasNoDups F)
    (hnormp : List.Pairwise (fun a b => monoLE a b = true) F)
    (hF : D F = []) (hhom : homogeneous F w) (hsupp : supp6 F) :
    ∃ (L : Nat) (F' : Poly), L ≠ 0 ∧ F' = polySmulInt ((L : Nat) : Int) F ∧
      (∀ m ∈ F', ∃ z : Int, m.1 = (z : Rat)) ∧ hasNoZeros F' ∧
      hasNoDups F' ∧ List.Pairwise (fun a b => monoLE a b = true) F' ∧
      D F' = [] ∧ homogeneous F' w ∧ supp6 F' := by
  refine ⟨commondenom F, polySmulInt ((commondenom F : Nat) : Int) F,
    commondenom_ne_zero F hnorm0, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
    have hmem : m'.1.den ∈ (F.map fun m => m.1.den) :=
      List.mem_map.mpr ⟨m', hm', rfl⟩
    have hdiv : m'.1.den ∣ commondenom F :=
      den_dvd_prod _ _ hmem
    have h1 : commondenom F / m'.1.den * m'.1.den = commondenom F :=
      Nat.div_mul_cancel hdiv
    have hLk : commondenom F = m'.1.den * (commondenom F / m'.1.den) := by
      rw [Nat.mul_comm]
      exact h1.symm
    obtain ⟨z, hz⟩ := smul_intValued _ _ _ hLk
    exact ⟨z, hz⟩
  · exact smul_noZeros _ (by
      have hL : (F.map (fun m => m.1.den)).prod ≠ 0 :=
        commondenom_ne_zero F hnorm0
      simp only [commondenom]
      omega) _ hnorm0
  · exact smul_nodup _ _ hnormd
  · exact smul_pairwise _ _ hnormp
  · rw [polyDsmul _ (by
      have hL : (F.map (fun m => m.1.den)).prod ≠ 0 :=
        commondenom_ne_zero F hnorm0
      simp only [commondenom]
      omega) _, hF]
    rfl
  · intro m hm
    obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
    exact hhom m' hm'
  · intro m hm
    obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
    exact hsupp m' hm'

theorem sum_filter (F : Poly) (P : Mono → Bool) (f : Mono → Rat) :
    ((F.filter P).map f).sum = ((F.map fun m => if P m then f m else 0)).sum := by
  induction F with
  | nil => simp
  | cons hd tl ih =>
    by_cases h : P hd = true
    · simp [h, ih, List.sum_cons]
    · simp [h, ih, List.sum_cons, Rat.zero_add]

theorem Dsplit (F : Poly) (u : Nat) (hsupp : supp6 F) (hF : D F = []) :
    D (F.filter (fun m => decide (expWeight m.2 = u))) = [] := by
  have e : ∀ x, evalCoeff (D (F.filter (fun m => decide (expWeight m.2 = u)))) x =
      evalCoeff ([] : Poly) x := by
    intro x
    rw [evalD_eq, sum_filter]
    by_cases hxu : expWeight x = u
    · have eF : ((F.map fun m => evalCoeff (D [m]) x)).sum = 0 := by
        rw [← evalD_eq, hF]
        exact evalCoeff_nil x
      have hcongr : ((F.map fun m => if decide (expWeight m.2 = u)
          then evalCoeff (D [m]) x else 0)).sum =
          ((F.map fun m => evalCoeff (D [m]) x)).sum := by
        apply congrArg
        apply List.map_inj_left.mpr
        intro m hm
        cases he : decide (expWeight m.2 = u) with
        | true => simp only [if_true]
        | false =>
          rw [if_neg Bool.false_ne_true]
          have hne := of_decide_eq_false he
          have hwx : expWeight x ≠ expWeight m.2 := by
            rw [hxu]
            exact Ne.symm hne
          have hz := evalD_weight_zero m (hsupp m hm) x hwx
          exact hz.symm
      exact hcongr.trans (eF.trans (evalCoeff_nil x).symm)
    · rw [sum_zero_terms _ _ (fun m hm => by
        cases he : decide (expWeight m.2 = u) with
        | true =>
          simp only [if_true]
          have huw : expWeight m.2 = u := of_decide_eq_true he
          have hwx : expWeight x ≠ expWeight m.2 :=
            fun hcon => hxu (hcon.trans huw)
          exact evalD_weight_zero m (hsupp m hm) x hwx
        | false => rw [if_neg Bool.false_ne_true])]
      simp [evalCoeff_nil]
  have hL0 : hasNoZeros (D (F.filter (fun m => decide (expWeight m.2 = u)))) := by
    rw [D_def]
    exact normalize_noZeros _
  have hLd : hasNoDups (D (F.filter (fun m => decide (expWeight m.2 = u)))) := by
    rw [D_def]
    exact normalize_nodup _
  have hLp : List.Pairwise (fun a b => monoLE a b = true)
      (D (F.filter (fun m => decide (expWeight m.2 = u)))) := by
    rw [D_def]
    exact sortPoly_pairwise _
  have hR0 : hasNoZeros ([] : Poly) := by intro m hm; simp at hm
  have hRd : hasNoDups ([] : Poly) := by unfold hasNoDups; simp
  have hRp : List.Pairwise (fun a b => monoLE a b = true) ([] : Poly) :=
    List.Pairwise.nil
  exact normalized_eq_of_same_eval _ _ hL0 hR0 hLd hRd hLp hRp e

theorem sum_update (F G : Nat → Rat) (H : Rat) (w u0 : Nat) (hu : u0 ≤ w)
    (h0 : G u0 = H + F u0) (hN : ∀ u, u ≤ w → u ≠ u0 → G u = F u) :
    ((List.range (w + 1)).map G).sum = H + ((List.range (w + 1)).map F).sum := by
  revert hu
  induction w with
  | zero =>
    intro hu
    have hz : u0 = 0 := by omega
    subst hz
    rw [show (List.range 1) = [0] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Rat.add_zero]
    exact h0
  | succ w ih =>
    intro hu
    by_cases heq : u0 = w + 1
    · subst heq
      rw [List.range_succ, List.map_append, List.map_append, List.sum_append,
        List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Rat.add_zero]
      have hinit : (((List.range (w + 1)).map G)).sum =
          (((List.range (w + 1)).map F)).sum := by
        apply congrArg
        apply List.map_inj_left.mpr
        intro i hi
        simp only [List.mem_range] at hi
        exact hN i (by omega) (by omega)
      rw [hinit, h0]
      ac_rfl
    · have hle : u0 ≤ w := by omega
      have ihw := ih (fun u hu hne => hN u (by omega) hne) hle
      have hlast : G (w + 1) = F (w + 1) := hN (w + 1) (by omega) (by omega)
      rw [List.range_succ, List.map_append, List.map_append, List.sum_append,
        List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Rat.add_zero]
      rw [ihw, hlast]
      ac_rfl

theorem eval_partition (F : Poly) (w : Nat)
    (hw : ∀ m ∈ F, expWeight m.2 ≤ w) (x : Exp) :
    evalCoeff F x =
      (((List.range (w + 1)).map fun u =>
        evalCoeff (F.filter (fun m => decide (expWeight m.2 = u))) x)).sum := by
  induction F with
  | nil =>
    rw [evalCoeff_nil]
    exact (sum_zero_terms _ _ (fun a _ => by
      simp [List.filter_nil, evalCoeff_nil])).symm
  | cons hd tl ih =>
    obtain ⟨c0, e0⟩ := hd
    have hu0 : expWeight e0 ≤ w := hw (c0, e0) (by simp)
    have hN : ∀ u, u ≤ w → u ≠ expWeight e0 →
        evalCoeff ((((c0, e0) :: tl).filter
          (fun m => decide (expWeight m.2 = u)))) x =
        evalCoeff ((tl.filter (fun m => decide (expWeight m.2 = u)))) x := by
      intro u _ hne
      cases he : decide (expWeight e0 = u) with
      | true => exact absurd (of_decide_eq_true he) (Ne.symm hne)
      | false =>
        have hneg2 : ¬((fun m => decide (expWeight m.2 = u)) (c0, e0)) := by
          simpa using he
        rw [List.filter_cons_of_neg (a := (c0, e0)) hneg2]
    have h0 : evalCoeff ((((c0, e0) :: tl).filter
          (fun m => decide (expWeight m.2 = expWeight e0)))) x =
        (if e0 = x then c0 else 0) +
          evalCoeff ((tl.filter
            (fun m => decide (expWeight m.2 = expWeight e0)))) x := by
      cases he : decide (expWeight e0 = expWeight e0) with
      | true =>
        have he' : (fun m => decide (expWeight m.2 = expWeight e0)) (c0, e0) =
            true := he
        simp only [List.filter_cons_of_pos
          (p := fun m => decide (expWeight m.2 = expWeight e0)) (a := (c0, e0))
          (l := tl) he', evalCoeff_cons]
      | false =>
        exact absurd rfl (of_decide_eq_false he)
    have hpart := sum_update
      (fun u => evalCoeff (tl.filter (fun m => decide (expWeight m.2 = u))) x)
      (fun u => evalCoeff ((((c0, e0) :: tl).filter
        (fun m => decide (expWeight m.2 = u)))) x)
      ((if e0 = x then c0 else 0)) w (expWeight e0) hu0 h0 hN
    rw [evalCoeff_cons, hpart, ih (fun m hm => hw m (List.mem_cons_of_mem _ hm))]
theorem membership_entry (w : Nat) (F' : Poly) (j : Nat)
    (hj : j < (monoW w).length)
    (hIntF' : ∀ m ∈ F', ∃ z : Int, m.1 = (z : Rat))
    (hnd : hasNoDups F') (h0 : hasNoZeros F')
    (hDF' : D F' = []) (hhom : homogeneous F' w) (hsupp : supp6 F')
    (hInt : ∀ e ∈ monoW w,
      ∀ m ∈ D [((1 : Rat), e)], ∃ z : Int, m.1 = (z : Rat)) :
    ((((matVecMul (dmat w) (coordIn (monoW w) F'))[j]?.getD 0 : Int)) : Rat) =
      0 := by
  have hjR : j < imatRows (dmat w) := by
    rw [imatRows_dmat]
    exact hj
  rw [mat_entry_cast _ _ _ hjR, coordIn_length]
  -- per-index cast agreements, then range/dom/F' sums, then D F' = []
  have hA : ∀ i, i ∈ List.range (monoW w).length →
      ((((coordIn (monoW w) F')[i]?.getD 0 : Int)) : Rat) =
        evalCoeff F' ((monoW w)[i]?.getD []) :=
    fun i hi => coord_cast_getD _ _ _ hi hIntF' hnd
  have hB : ∀ i, i ∈ List.range (monoW w).length →
      ((((imatGet (dmat w) j i : Int)) : Rat)) =
        evalCoeff (D (basisPoly ((monoW w)[i]?.getD [])))
          ((monoW w)[j]?.getD []) :=
    fun i hi => by
      have hlt : i < (monoW w).length := List.mem_range.mp hi
      rw [List.getElem?_eq_getElem hlt, Option.getD_some]
      exact dmat_entry_cast_getD w j i (List.mem_range.mpr hj) hlt hInt
  have hconv : (((List.range (monoW w).length).map fun i =>
      ((((imatGet (dmat w) j i : Int)) : Rat)) *
        ((((coordIn (monoW w) F')[i]?.getD 0 : Int)) : Rat))).sum =
      (((List.range (monoW w).length).map fun i =>
        evalCoeff F' ((monoW w)[i]?.getD []) *
          evalCoeff (D (basisPoly ((monoW w)[i]?.getD [])))
            ((monoW w)[j]?.getD []))).sum := by
    apply congrArg
    apply List.map_inj_left.mpr
    intro i hi
    rw [hA i hi, hB i hi, Rat.mul_comm]
  rw [hconv]
  have hrd := range_dom_sum (monoW w)
    (fun e => evalCoeff F' e *
      evalCoeff (D (basisPoly e)) ((monoW w)[j]?.getD []))
  rw [hrd]
  have hds := dom_sum (monoW w) F'
    (fun e => evalCoeff (D (basisPoly e)) ((monoW w)[j]?.getD []))
    (monoW_nodup w) hnd
    (fun m hm => by
      have hwgt := hhom m hm
      have hlen := hsupp m hm
      exact monoW_complete w _ hlen hwgt)
  rw [hds]
  -- F'-sum = eval (D F') (dom[j]) = 0
  have hev : ((F'.map fun m => evalCoeff F' m.2 *
      evalCoeff (D (basisPoly m.2)) ((monoW w)[j]?.getD []))).sum =
      evalCoeff (D F') ((monoW w)[j]?.getD []) := by
    have h1 : ((F'.map fun m => evalCoeff F' m.2 *
        evalCoeff (D (basisPoly m.2)) ((monoW w)[j]?.getD []))).sum =
        (((F'.map fun m => evalCoeff (D [m]) ((monoW w)[j]?.getD [])))).sum := by
      apply congrArg
      apply List.map_inj_left.mpr
      intro m hm
      have e1 : evalCoeff F' m.2 = m.1 :=
        eval_at_mem F' m hm hnd h0
      have e2 : evalCoeff (D [m]) ((monoW w)[j]?.getD []) = m.1 *
          evalCoeff (D (basisPoly m.2)) ((monoW w)[j]?.getD []) :=
        evalDsmul_single m.1 m.2 _ (hIntF' m hm)
      rw [e1]
      exact e2.symm
    rw [h1, ← evalD_eq]
  rw [hev]
  rw [hDF', evalCoeff_nil]

-- ======================================================================
-- Integer-coefficient machinery + `D_mono_int`.
-- Proves D of a monomial with an integral coefficient has integral
-- coefficients (the key side-lemma for the gselDecode entry bridge).
-- ======================================================================

/-- All coefficients of `F` are integral (integer-valued rationals). -/
def intCoeffs (F : Poly) : Prop := ∀ m ∈ F, ∃ z : Int, m.1 = (z : Rat)

/-- A single monomial with an integral coefficient. -/
theorem intCoeffs_mono (c : Rat) (e : Exp) (hc : ∃ z : Int, c = (z : Rat)) :
    intCoeffs [(c, e)] := by
  intro x hx
  obtain rfl := List.mem_singleton.mp hx
  exact hc

/-- A single generator `aᵢ = [((1 : Rat), varExp i)]` has an integral (1) coefficient. -/
theorem intCoeffs_gen (i : Fin 6) : intCoeffs [((1 : Rat), varExp i.val)] :=
  intCoeffs_mono _ _ ⟨1, by simp⟩

/-- Integer scalar multiplication preserves integrality. -/
theorem intCoeffs_polySmulInt (d : Int) (F : Poly) (h : intCoeffs F) :
    intCoeffs (polySmulInt d F) := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  obtain ⟨z, hz⟩ := h m hm
  exact ⟨d * z, by simp [hz]⟩

/-- Append preserves integrality. -/
theorem intCoeffs_append (p q : Poly) (hp : intCoeffs p) (hq : intCoeffs q) :
    intCoeffs (p ++ q) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hp x h
  · exact hq x h

/-- `insertCombineGo` preserves integrality. -/
theorem intCoeffs_insertCombineGo (m : Mono) (q : Poly)
    (hm : ∃ z : Int, m.1 = (z : Rat)) (hq : intCoeffs q) :
    intCoeffs (insertCombineGo m q) := by
  induction q with
  | nil =>
    simp [insertCombineGo, intCoeffs]
    exact hm
  | cons hd tl ih =>
    simp only [insertCombineGo, intCoeffs]
    intro x hx
    obtain ⟨c, e⟩ := hd
    have htl : intCoeffs tl := fun y hy => hq y (List.mem_cons_of_mem (c, e) hy)
    have ih' := ih htl
    by_cases heq : e = m.2
    · by_cases hzero : c + m.fst = 0
      · simp [heq, hzero] at hx
        exact htl x hx
      · simp [heq, hzero] at hx
        rcases hx with rfl | hmem
        · obtain ⟨z1, hz1⟩ := hq (c, e) List.mem_cons_self
          obtain ⟨z2, hz2⟩ := hm
          have hc : c = ↑z1 := by simpa [hz1]
          rw [hc, hz2]
          exact ⟨z1 + z2, by simp⟩
        · exact htl x hmem
    · simp [heq] at hx
      rcases hx with rfl | hmem
      · obtain ⟨z1, hz1⟩ := hq (c, e) List.mem_cons_self
        exact ⟨z1, by simpa using hz1⟩
      · exact ih' x hmem

/-- `insertCombine` preserves integrality. -/
theorem intCoeffs_insertCombine (m : Mono) (q : Poly)
    (hm : ∃ z : Int, m.1 = (z : Rat)) (hq : intCoeffs q) :
    intCoeffs (insertCombine m q) := by
  intro x hx
  simp only [insertCombine] at hx
  by_cases hm0 : m.1 = 0
  · simp [hm0] at hx
    exact hq x hx
  · by_cases hmem : m.2 ∈ q.map (·.2)
    · simp [hm0, hmem] at hx
      exact intCoeffs_insertCombineGo m q hm hq x hx
    · simp [hm0, hmem] at hx
      rcases hx with rfl | hmem
      · exact hm
      · exact hq x hmem

/-- `combine` preserves integrality. -/
theorem intCoeffs_combine (F : Poly) (h : intCoeffs F) : intCoeffs (combine F) := by
  induction F with
  | nil =>
    simp [combine, intCoeffs]
  | cons hd tl ih =>
    simp only [combine, intCoeffs]
    intro x hx
    have htl : intCoeffs (combine tl) := ih (fun y hy => h y (List.mem_cons_of_mem hd hy))
    exact (intCoeffs_insertCombine hd (combine tl) (h hd List.mem_cons_self) htl) x hx

/-- `sortPoly` preserves integrality (a permutation). -/
theorem intCoeffs_sortPoly (P : Poly) (h : intCoeffs P) : intCoeffs (sortPoly P) := by
  intro x hx
  have hperm := sortPoly_perm P
  have hmem : x ∈ P := (List.Perm.mem_iff hperm).mp hx
  exact h x hmem

/-- `normalize` preserves integrality. -/
theorem intCoeffs_normalize (F : Poly) (h : intCoeffs F) : intCoeffs (normalize F) := by
  intro x hx
  have hcomb := intCoeffs_combine F h
  have hsort := intCoeffs_sortPoly (combine F) hcomb
  have hnorm : normalize F = sortPoly (combine F) := rfl
  rw [hnorm] at hx
  exact hsort x hx

/-- `polyAdd` preserves integrality. -/
theorem intCoeffs_polyAdd (p q : Poly) (hp : intCoeffs p) (hq : intCoeffs q) :
    intCoeffs (polyAdd p q) := by
  have hcat := intCoeffs_append p q hp hq
  exact intCoeffs_normalize _ hcat

/-- `polyMul` preserves integrality. -/
theorem intCoeffs_polyMul (p q : Poly) (hp : intCoeffs p) (hq : intCoeffs q) :
    intCoeffs (polyMul p q) := by
  have hflat : intCoeffs (p.flatMap (fun m1 => q.map (fun m2 => mulMono m1 m2))) := by
    intro x hx
    obtain ⟨m1, hm1, hxmap⟩ := List.mem_flatMap.mp hx
    obtain ⟨m2, hm2, rfl⟩ := List.mem_map.mp hxmap
    obtain ⟨z1, hz1⟩ := hp m1 hm1
    obtain ⟨z2, hz2⟩ := hq m2 hm2
    dsimp [mulMono]
    rw [hz1, hz2]
    exact ⟨z1 * z2, by simp⟩
  exact intCoeffs_normalize _ hflat

/-- If `derivMono i (c, e) = some x`, then `x` has an integral coefficient. -/
theorem derivMono_some_int (c : Rat) (e : Exp) (i : Fin 6)
    (hc : ∃ z : Int, c = (z : Rat)) (x : Mono) :
    derivMono i (c, e) = some x → ∃ k : Int, x.1 = (k : Rat) := by
  intro hxsome
  obtain ⟨z, hz⟩ := hc
  cases he : e[i.val]? with
  | none =>
    have hnone : derivMono i (c, e) = none := by dsimp only [derivMono]; simp [he]
    rw [hnone] at hxsome
    cases hxsome
  | some k =>
    cases k with
    | zero =>
      have hnone : derivMono i (c, e) = none := by dsimp only [derivMono]; simp [he]
      rw [hnone] at hxsome
      cases hxsome
    | succ k' =>
      have hmatch : derivMono i (c, e) = some (c * ((k' + 1 : Nat) : Rat), e.set i.val k') := by
        dsimp only [derivMono]
        rw [he]
      rw [hmatch] at hxsome
      injection hxsome with h1
      rw [← h1, hz]
      exact ⟨z * ((k' + 1 : Nat) : Int), by norm_cast⟩

/-- `partialDeriv` of a single monomial with an integral coefficient. -/
theorem partialDeriv_mono_int (c : Rat) (e : Exp) (i : Fin 6)
    (hc : ∃ z : Int, c = (z : Rat)) : intCoeffs (partialDeriv i [(c, e)]) := by
  dsimp only [partialDeriv]
  intro x hx
  have hfm : intCoeffs ([(c, e)].filterMap (derivMono i)) := by
    intro y hy
    obtain ⟨m, hm, hym⟩ := List.mem_filterMap.mp hy
    obtain rfl := List.mem_singleton.mp hm
    exact derivMono_some_int c e i hc y hym
  exact intCoeffs_normalize _ hfm x hx

/-- **`D_mono_int`** — D of a monomial with an integral coefficient has
    integral coefficients. (Key side-lemma for the gselDecode entry bridge.) -/
theorem D_mono_int (c : Int) (e : Exp) :
    intCoeffs (D [((c : Rat), e)]) := by
  let M := [((c : Rat), e)]
  have hc : ∃ z : Int, (c : Rat) = (z : Rat) := ⟨c, rfl⟩
  have hA12 : intCoeffs (polyMul a1 a2) := by
    dsimp [a1, a2]
    exact intCoeffs_polyMul _ _ (intCoeffs_gen ⟨1, by decide⟩) (intCoeffs_gen ⟨2, by decide⟩)
  have hA23 : intCoeffs (polyMul a2 a3) := by
    dsimp [a2, a3]
    exact intCoeffs_polyMul _ _ (intCoeffs_gen ⟨2, by decide⟩) (intCoeffs_gen ⟨3, by decide⟩)
  have hA34 : intCoeffs (polyMul a3 a4) := by
    dsimp [a3, a4]
    exact intCoeffs_polyMul _ _ (intCoeffs_gen ⟨3, by decide⟩) (intCoeffs_gen ⟨4, by decide⟩)
  have hA45 : intCoeffs (polyMul a4 a5) := by
    dsimp [a4, a5]
    exact intCoeffs_polyMul _ _ (intCoeffs_gen ⟨4, by decide⟩) (intCoeffs_gen ⟨5, by decide⟩)
  have t0 : intCoeffs (polyMul (polyMul a1 a2) (partialDeriv ⟨0, by decide⟩ M)) :=
    intCoeffs_polyMul _ _ hA12 (partialDeriv_mono_int (c : Rat) e ⟨0, by decide⟩ hc)
  have t1 : intCoeffs (polyMul (polyMul a2 a3) (partialDeriv ⟨1, by decide⟩ M)) :=
    intCoeffs_polyMul _ _ hA23 (partialDeriv_mono_int (c : Rat) e ⟨1, by decide⟩ hc)
  have t2 : intCoeffs (polyMul (polyMul a3 a4) (partialDeriv ⟨2, by decide⟩ M)) :=
    intCoeffs_polyMul _ _ hA34 (partialDeriv_mono_int (c : Rat) e ⟨2, by decide⟩ hc)
  have t3 : intCoeffs (polyMul (polyMul a4 a5) (partialDeriv ⟨3, by decide⟩ M)) :=
    intCoeffs_polyMul _ _ hA45 (partialDeriv_mono_int (c : Rat) e ⟨3, by decide⟩ hc)
  rw [D_def M]
  have h01 : intCoeffs (polyAdd (polyMul (polyMul a1 a2) (partialDeriv ⟨0, by decide⟩ M))
                               (polyMul (polyMul a2 a3) (partialDeriv ⟨1, by decide⟩ M))) :=
    intCoeffs_polyAdd _ _ t0 t1
  have h23 : intCoeffs (polyAdd (polyMul (polyMul a3 a4) (partialDeriv ⟨2, by decide⟩ M))
                               (polyMul (polyMul a4 a5) (partialDeriv ⟨3, by decide⟩ M))) :=
    intCoeffs_polyAdd _ _ t2 t3
  exact intCoeffs_polyAdd _ _ h01 h23


/-! Entry bridge for `gselDecode`: the cross-multiplied matrix equality forces the
    individual (i, j) entry `Gsel[i][j] = D0 * c` over `Rat`, where `c` is the
    coefficient of the selected genmonomial at basis index `i`. -/

/-- Structural equality from the `gselDecode` BEq matrix test. -/
theorem beq_mat_eq_true (L R : IMat) (h : (L == R) = true) : L = R := by
  simpa using beq_iff_eq.mp h

/-- The (i, j)-entry cross-multiplication extracted from `gselDecode = true`. -/
theorem gselDecode_entry (w : Nat) (selIdx : List Nat) (Gsel : IMat) (D0 : Int)
    (hdec : gselDecode w selIdx Gsel D0 = true)
    (i j : Nat) (hi : i < (monoW w).length) (hj : j < selIdx.length) :
    (((Gsel[i]?).getD [])[j]?.getD 0) *
      (((evalCoeff (((genMonos w)[(selIdx[j]?).getD 0]?).getD [])
        ((monoW w)[i]?.getD [])).den : Int)) =
      D0 * ((evalCoeff (((genMonos w)[(selIdx[j]?).getD 0]?).getD [])
        ((monoW w)[i]?.getD [])).num) := by
  let g := ((genMonos w)[(selIdx[j]?).getD 0]?).getD []
  let c := evalCoeff g ((monoW w)[i]?.getD [])
  let e := ((Gsel[i]?).getD [])[j]?.getD 0
  simp only [gselDecode, Bool.and_eq_true] at hdec
  let L := (List.range (monoW w).length).map fun i =>
      (List.range selIdx.length).map fun j =>
        let g := ((genMonos w)[(selIdx[j]?).getD 0]?).getD []
        let c := evalCoeff g ((monoW w)[i]?.getD [])
        ((Gsel[i]?).getD [])[j]?.getD 0 * (c.den : Int)
  let R := (List.range (monoW w).length).map fun i =>
      (List.range selIdx.length).map fun j =>
        let g := ((genMonos w)[(selIdx[j]?).getD 0]?).getD []
        D0 * (evalCoeff g ((monoW w)[i]?.getD [])).num
  have hBEq : (L == R) = true := hdec.2
  have hmat : L = R := by simpa [beq_iff_eq] using hBEq
  -- entry (i, j) of L = Gsel[i][j] * c.den
  have hLentry : ((L[i]?).getD [])[j]?.getD 0 =
      (((Gsel[i]?).getD [])[j]?.getD 0) * (c.den : Int) := by
    simp only [L]
    rw [map_range_get _ _ _ hi]
    simp
    have hgt : (List.range selIdx.length)[j]? = some j := by simp [hj]
    rw [hgt, Option.map_some, Option.getD_some]
  -- entry (i, j) of R = D0 * c.num
  have hRentry : ((R[i]?).getD [])[j]?.getD 0 =
      D0 * (evalCoeff g ((monoW w)[i]?.getD [])).num := by
    simp only [R]
    rw [map_range_get _ _ _ hi]
    simp
    have hgt : (List.range selIdx.length)[j]? = some j := by simp [hj]
    rw [hgt, Option.map_some, Option.getD_some]
  -- L = R at the (i, j) entry
  have hLr : ((L[i]?).getD [])[j]?.getD 0 = ((R[i]?).getD [])[j]?.getD 0 := by
    rw [hmat]
  rw [← hLentry, hLr, hRentry]

/-- `gselDecode = true` forces `Gsel[i][j] = D0 * c` over `Rat`, where `c` is the
    coefficient of the selected genmonomial at basis index `i`. -/
theorem crossmul_decode (w : Nat) (selIdx : List Nat) (Gsel : IMat) (D0 : Int)
    (hdec : gselDecode w selIdx Gsel D0 = true)
    (i j : Nat) (hi : i < (monoW w).length) (hj : j < selIdx.length) :
    (((Gsel[i]?).getD [])[j]?.getD 0 : Rat) =
      D0 * evalCoeff (((genMonos w)[(selIdx[j]?).getD 0]?).getD [])
        ((monoW w)[i]?.getD []) := by
  let g := ((genMonos w)[(selIdx[j]?).getD 0]?).getD []
  let c := evalCoeff g ((monoW w)[i]?.getD [])
  let e := ((Gsel[i]?).getD [])[j]?.getD 0
  have hentry : e * (c.den : Int) = D0 * c.num := gselDecode_entry _ _ _ _ hdec _ _ hi hj
  have hdenI : (c.den : Int) ≠ 0 := by
    intro h
    exact (Nat.pos_iff_ne_zero.mp (Rat.den_pos c)) (Int.natCast_eq_zero.mp h)
  -- c = divInt (c.num) (c.den)
  have hnumden : c = Rat.divInt c.num (c.den : Int) := (Rat.num_divInt_den c).symm
  have hLHS : (D0 : Rat) * c = (D0 : Rat) * Rat.divInt c.num (c.den : Int) := congrArg _ hnumden
  have hRat : (D0 : Rat) * c = Rat.divInt (D0 * c.num) (c.den : Int) := by
    rw [hLHS, intCast_eq_divInt_one D0, Rat.divInt_mul_divInt D0 c.num, Int.one_mul]
  -- target: divInt e 1 = divInt (D0 * c.num) (c.den)
  rw [intCast_eq_divInt_one e]
  rw [hRat]
  rw [Rat.divInt_eq_divInt_iff (by decide : (1 : Int) ≠ 0) hdenI]
  simpa [Int.mul_one] using hentry

/-- Integral homogeneous invariants give actual column-kernel vectors. -/
theorem invariant_coord_kernel (w : Nat) (F : Poly)
    (hInt : intCoeffs F) (hnd : hasNoDups F) (h0 : hasNoZeros F)
    (hDF : D F = []) (hhom : homogeneous F w) (hsupp : supp6 F) :
    matVecMul (dmat w) (coordIn (monoW w) F) = zeroVec (monoW w).length := by
  apply List.ext_getElem
  · simp [matVecMul_length, imatRows_dmat, zeroVec]
  · intro i hi hj
    have hiw : i < (monoW w).length := by
      simpa [matVecMul_length, imatRows_dmat] using hi
    have he := membership_entry w F i hiw hInt hnd h0 hDF hhom hsupp
      (fun e _ => D_mono_int 1 e)
    have hz := Rat.intCast_eq_zero_iff.mp he
    simpa [List.getElem?_eq_getElem hi, zeroVec] using hz
