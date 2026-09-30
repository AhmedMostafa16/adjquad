import AdjQuad.Generation

/-- Normalization cannot introduce exponents of a different weight or length. -/
theorem homogeneous_supp6_normalize (P : Poly) (w : Nat)
    (hP : homogeneous P w ∧ supp6 P) :
    homogeneous (normalize P) w ∧ supp6 (normalize P) := by
  have hsource : ∀ m ∈ normalize P, ∃ t ∈ P, t.2 = m.2 := by
    intro m hm
    exact List.mem_map.mp (normalize_mem_exp P m.2 (List.mem_map.mpr ⟨m, hm, rfl⟩))
  constructor
  · intro m hm
    obtain ⟨t, ht, he⟩ := hsource m hm
    rw [← he]
    exact hP.1 t ht
  · intro m hm
    obtain ⟨t, ht, he⟩ := hsource m hm
    rw [← he]
    exact hP.2 t ht

/-- Multiplication adds homogeneous weights and preserves six-variable support. -/
theorem homogeneous_supp6_polyMul (P Q : Poly) (u v : Nat)
    (hP : homogeneous P u ∧ supp6 P) (hQ : homogeneous Q v ∧ supp6 Q) :
    homogeneous (polyMul P Q) (u + v) ∧ supp6 (polyMul P Q) := by
  have hterm : ∀ m ∈ polyMul P Q,
      expWeight m.2 = u + v ∧ m.2.length = 6 := by
    intro m hm
    obtain ⟨e1, he1, e2, he2, he⟩ :=
      polyMul_mem_exp P Q m.2 (List.mem_map.mpr ⟨m, hm, rfl⟩)
    obtain ⟨t1, ht1, rfl⟩ := List.mem_map.mp he1
    obtain ⟨t2, ht2, rfl⟩ := List.mem_map.mp he2
    rw [he]
    constructor
    · rw [addExp_weight _ _ (hP.2 t1 ht1) (hQ.2 t2 ht2),
        hP.1 t1 ht1, hQ.1 t2 ht2]
    · simp only [addExp, List.length_zipWith, hP.2 t1 ht1, hQ.2 t2 ht2]
      rfl
  exact ⟨fun m hm => (hterm m hm).1, fun m hm => (hterm m hm).2⟩

/-- Powers multiply homogeneous weights and preserve six-variable support. -/
theorem homogeneous_supp6_polyPow (P : Poly) (w n : Nat)
    (hP : homogeneous P w ∧ supp6 P) :
    homogeneous (polyPow P n) (w * n) ∧ supp6 (polyPow P n) := by
  induction n with
  | zero =>
    constructor
    · intro m hm
      have he : m = (1, zeroExp) := by simpa only [polyPow_zero, List.mem_singleton] using hm
      subst m
      rfl
    · intro m hm
      have he : m = (1, zeroExp) := by simpa only [polyPow_zero, List.mem_singleton] using hm
      subst m
      rfl
  | succ n ih =>
    simpa only [polyPow_succ, Nat.mul_succ, Nat.add_comm] using
      homogeneous_supp6_polyMul P (polyPow P n) w (w * n) hP ih


/-- `p = a4 = [(1, varExp 4)]`, weight 1. -/
theorem homogeneous_supp6_p : homogeneous p 1 ∧ supp6 p := by
  unfold homogeneous supp6
  decide

/-- `q = a5 = [(1, varExp 5)]`, weight 1. -/
theorem homogeneous_supp6_q : homogeneous q 1 ∧ supp6 q := by
  unfold homogeneous supp6
  decide

/-- `J1 = 2a1a4 - a2²`, weight 6. -/
theorem homogeneous_supp6_J1 : homogeneous J1 6 ∧ supp6 J1 := by
  apply homogeneous_supp6_normalize
  unfold homogeneous supp6
  decide

/-- `J2 = 2a2a5 - a3²`, weight 4. -/
theorem homogeneous_supp6_J2 : homogeneous J2 4 ∧ supp6 J2 := by
  apply homogeneous_supp6_normalize
  unfold homogeneous supp6
  decide

/-- `F0`, weight 14. -/
theorem homogeneous_supp6_F0 : homogeneous F0 14 ∧ supp6 F0 := by
  apply homogeneous_supp6_normalize
  unfold homogeneous supp6
  decide

/-- `H` (17-term literal), weight 24. -/
theorem homogeneous_supp6_H : homogeneous H 24 ∧ supp6 H := by
  apply homogeneous_supp6_normalize
  unfold homogeneous supp6
  decide

/-- The six fixed generators have the stated weights and six-variable support. -/
theorem generators_homogeneous_supp6 :
    (homogeneous p 1 ∧ supp6 p) ∧
    (homogeneous q 1 ∧ supp6 q) ∧
    (homogeneous J1 6 ∧ supp6 J1) ∧
    (homogeneous J2 4 ∧ supp6 J2) ∧
    (homogeneous F0 14 ∧ supp6 F0) ∧
    (homogeneous H 24 ∧ supp6 H) :=
  ⟨homogeneous_supp6_p, homogeneous_supp6_q, homogeneous_supp6_J1,
    homogeneous_supp6_J2, homogeneous_supp6_F0, homogeneous_supp6_H⟩

/-- Every generator monomial has its construction weight and six-variable support. -/
theorem genMono_homogeneous_supp6 (e : Nat × Nat × Nat × Nat × Nat × Nat) :
    homogeneous (genMono e) (genWt e) ∧ supp6 (genMono e) := by
  obtain ⟨ep, eq, ej1, ej2, ef, eh⟩ := e
  obtain ⟨hp, hq, hj1, hj2, hf, hh⟩ := generators_homogeneous_supp6
  have hpq := homogeneous_supp6_polyMul _ _ _ _
    (homogeneous_supp6_polyPow p 1 ep hp)
    (homogeneous_supp6_polyPow q 1 eq hq)
  have hj := homogeneous_supp6_polyMul _ _ _ _
    (homogeneous_supp6_polyPow J1 6 ej1 hj1)
    (homogeneous_supp6_polyPow J2 4 ej2 hj2)
  have hfh := homogeneous_supp6_polyMul _ _ _ _
    (homogeneous_supp6_polyPow F0 14 ef hf)
    (homogeneous_supp6_polyPow H 24 eh hh)
  simpa only [genMono, genWt, Nat.one_mul, Nat.add_assoc] using
    homogeneous_supp6_polyMul _ _ _ _
      (homogeneous_supp6_polyMul _ _ _ _ hpq hj) hfh

/-- Every enumerated generator monomial is homogeneous at its enumeration weight. -/
theorem genMonos_homogeneous (w : Nat) (g : Poly) (hg : g ∈ genMonos w) :
    homogeneous g w := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
  rw [← genWt_of_mem w e he]
  exact (genMono_homogeneous_supp6 e).1

/-- Every enumerated generator monomial is supported on six-variable exponents. -/
theorem genMonos_supp6 (w : Nat) (g : Poly) (hg : g ∈ genMonos w) : supp6 g := by
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hg
  exact (genMono_homogeneous_supp6 e).2

/-- The outer multiplication normalizes every generator monomial. -/
theorem genMono_normalized (e : Nat × Nat × Nat × Nat × Nat × Nat) :
    hasNoZeros (genMono e) ∧ hasNoDups (genMono e) ∧
      List.Pairwise (fun a b => monoLE a b = true) (genMono e) := by
  obtain ⟨ep, eq, ej1, ej2, ef, eh⟩ := e
  exact ⟨normalize_noZeros _, normalize_nodup _, sortPoly_pairwise _⟩

/-- Every enumerated generator monomial is a normalized representative. -/
theorem genMonos_normalized (w : Nat) (g : Poly) (hg : g ∈ genMonos w) :
    hasNoZeros g ∧ hasNoDups g ∧ List.Pairwise (fun a b => monoLE a b = true) g := by
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hg
  exact genMono_normalized e

/-- Homogeneous six-variable polynomials vanish off their weight basis. -/
theorem evalCoeff_homogeneous_off_basis (P : Poly) (w : Nat)
    (hP : homogeneous P w) (hs : supp6 P) (x : Exp) (hx : x ∉ monoW w) :
    evalCoeff P x = 0 := by
  apply evalCoeff_missing
  intro m hm he
  apply hx
  rw [← he]
  exact monoW_complete w m.2 (hs m hm) (hP m hm)

/-- Coefficients of an enumerated generator monomial vanish off `monoW w`. -/
theorem evalCoeff_genMonos_off_basis (w : Nat) (g : Poly) (hg : g ∈ genMonos w)
    (x : Exp) (hx : x ∉ monoW w) : evalCoeff g x = 0 :=
  evalCoeff_homogeneous_off_basis g w
    (genMonos_homogeneous w g hg) (genMonos_supp6 w g hg) x hx
