import AdjQuad.Hypersurface

/-
`H_B`: the transported hidden generator (N=6 B-level hypersurface).

Slot-reindexing dictionary (this is the whole formal content of the
shift `(B_6, D_6) ~= (A_5, D_5)`, `a_i |-> a_{i+1}`, at the level of
closed polynomial identities): N=6 variable `a_i` is formal slot
`a_{i-1}` of the 6-slot API. Under this reading
  * the N=6 derivation on slots IS the API operator `D`
    (`D(slot_0) = slot_1*slot_2, ..., D(slot_3) = slot_4*slot_5`,
    kills slot_4, slot_5 — syntactically identical to N=5);
  * the Fibonacci weights `[8,5,3,2,1,1]` coincide numerically;
  * `G_1, G_2, G_3, G_4` ARE `p, q, J1, J2` as formal polys
    (`2*slot_1*slot_4 - slot_2^2`, `2*slot_2*slot_5 - slot_3^2`);
  * `H_B` IS `H` as a formal poly (17 terms, content 1);
  * `G_5/105` IS `F0` as a formal poly (`F0_is_g5` below).
Hence every N=5 closed fact re-applies verbatim. New (proved here):
`g5` (the degree-7 generator in slot reading), the `inR` mirror of
the safety invariant (the `F0`-case becomes the `g5`-case; all
induction machinery is imported generic from Exclusion.lean),
`H_B` outside `R = k[G_1..G_5]`, and the transported relation
`S_B = a_6^4*H_B - G_5^2 - 105*a_6^2*G_4^5*G_3 - 9*G_4^7 = 0`
(`S_B` uses `F0_B = G_5/105`, so no seventh generator appears).

Explicitly OUT of scope (remain CAS-only): the full shift
isomorphism as a Lean theorem (needs substitution/equiv machinery
absent from the core-only API) and B-level uniqueness/series
(transferred CAS standard, `check_N6_shift.py`).

Standalone: `lake build AdjQuad.H_B`
(not imported by the root). Core-Lean only.
-/

/-- `H_B`: the transported hidden generator (slot-reindexed `H`). -/
def HB : Poly := H

/-- `HB` unfolds to `H` (same formal list). -/
theorem HB_eq_H : HB = H := rfl

/-- The degree-7 generator in slot reading (`G_5`). -/
def g5 : Poly := normalize
  [((105 : Rat), [1,0,0,0,2,4]),
   ((-105 : Rat), [0,1,1,1,1,3]),
   ((35 : Rat), [0,1,0,3,1,2]),
   ((35 : Rat), [0,0,2,3,0,2]),
   ((-21 : Rat), [0,0,1,5,0,1]),
   ((3 : Rat), [0,0,0,7,0,0])]

------------------------------------------------------------
-- 1. Transported H_B facts (rewrite along HB_eq_H)
------------------------------------------------------------

/-- `H_B` is D-invariant (the N=6 reading of `H_D_zero`). -/
theorem HB_D_zero : D HB = [] := HB_eq_H ▸ H_D_zero

/-- `H_B` has Fibonacci weight 24. -/
theorem HB_weight_24 : weightedDegree HB = 24 := HB_eq_H ▸ weightedDegree_H

/-- Every term of `H_B` weighs 24. -/
theorem HB_terms_24 : ∀ e ∈ HB.map (·.2), expWeight e = 24 :=
  HB_eq_H ▸ H_terms_have_weight_24

/-- `H_B` has the `a_1^2` term (`11025 a_1^2 a_5^4 a_6^4` in N=6 vars). -/
theorem HB_has_a1_sq : (11025, [2,0,0,0,4,4]) ∈ HB := H_has_a0_sq

/-- Every term of `H_B` is length-6. -/
theorem HB_len6 : ∀ e ∈ HB.map (·.2), e.length = 6 :=
  HB_eq_H ▸ H_len6

/-- N=6 `a_1`-degree (= slot-0 exponent) of `H_B` is at most 2. -/
theorem H_a1deg_le_2 : ∀ m ∈ H, a0degMono m ≤ 2 := by native_decide

/-- Same, stated for `HB`. -/
theorem HB_a1deg_le_2 : ∀ m ∈ HB, a0degMono m ≤ 2 :=
  HB_eq_H ▸ H_a1deg_le_2

------------------------------------------------------------
-- 2. The F0/G5 bridge + g5 base facts
------------------------------------------------------------

/-- Shift of `F0` is the degree-7 generator: `105 * F0 = g5`. -/
theorem F0_is_g5 : polyMul [(105, zeroExp)] F0 = g5 := by native_decide

/-- Length-6 facts for `g5`. -/
theorem g5_len6 : ∀ e ∈ g5.map (·.2), e.length = 6 := by native_decide

/-- `safety` base fact for `g5`: head-1 term weighs exactly 14. -/
theorem g5_base : ∀ e ∈ g5.map (·.2), 14 * a0deg e <= expWeight e := by
  native_decide

------------------------------------------------------------
-- 3. The subalgebra predicate + the `safety` invariant (mirror of
--    Exclusion.lean with the F0-case swapped for the g5-case)
------------------------------------------------------------

/-
 * `inR` is the smallest k-subalgebra of the slot ring containing
 * `{G_1, G_2, G_3, G_4, G_5}` read as formal polys, i.e. `{p, q, J1,
 * J2, g5}`. `inR y` reads `y in R` with `R := k[G_1..G_5]`.
 -/
inductive inR : Poly → Prop
  | mkZero : inR []
  | mkOne : inR [(1, zeroExp)]
  | mkG1 : inR p
  | mkG2 : inR q
  | mkG3 : inR J1
  | mkG4 : inR J2
  | mkG5 : inR g5
  | mkSum {x y} : inR x → inR y → inR (polyAdd x y)
  | mkProd {x y} : inR x → inR y → inR (polyMul x y)

/-- Every term of every `R` element has a length-6 exponent vector. -/
theorem inR_len6 {y} (h : inR y) : ∀ m ∈ y, m.2.length = 6 := by
  induction h with
  | mkZero =>
    intro m hm
    cases hm
  | mkOne =>
    intro m hm
    simp only [List.mem_cons] at hm
    rcases hm with heq | hnil
    · subst m
      simp [zeroExp]
    · cases hnil
  | mkG1 =>
    intro m hm
    have hexp : m.2 ∈ p.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact p_len6 m.2 hexp
  | mkG2 =>
    intro m hm
    have hexp : m.2 ∈ q.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact q_len6 m.2 hexp
  | mkG3 =>
    intro m hm
    have hexp : m.2 ∈ J1.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact J1_len6 m.2 hexp
  | mkG4 =>
    intro m hm
    have hexp : m.2 ∈ J2.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact J2_len6 m.2 hexp
  | mkG5 =>
    intro m hm
    have hexp : m.2 ∈ g5.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact g5_len6 m.2 hexp
  | mkSum hx hy ihx ihy =>
    rename_i u v
    intro m hm
    have hmap : m.2 ∈ (polyAdd u v).map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    rw [polyAdd_def] at hmap
    have hsup : m.2 ∈ (u ++ v).map (·.2) := normalize_mem_exp (u ++ v) m.2 hmap
    simp only [List.map_append] at hsup
    rcases List.mem_append.mp hsup with hu | hv
    · rcases List.exists_of_mem_map hu with ⟨n, hn, hne⟩
      have ih : n.2.length = 6 := ihx n hn
      rw [hne] at ih
      exact ih
    · rcases List.exists_of_mem_map hv with ⟨n, hn, hne⟩
      have ih : n.2.length = 6 := ihy n hn
      rw [hne] at ih
      exact ih
  | mkProd hx hy ihx ihy =>
    rename_i u v
    intro m hm
    rw [polyMul_def] at hm
    have hsup : m.2 ∈
      (u.flatMap (fun m1 => v.map (fun m2 => mulMono m1 m2))).map (·.2) :=
      normalize_mem_exp _ m.2 (List.mem_map.mpr ⟨m, hm, rfl⟩)
    rcases List.exists_of_mem_map hsup with ⟨n, hn, hne⟩
    rcases List.mem_flatMap.mp hn with ⟨m1, hm1, hm1m⟩
    rcases List.exists_of_mem_map hm1m with ⟨m2, hm2, hmn⟩
    have ih1 : m1.2.length = 6 := ihx m1 hm1
    have ih2 : m2.2.length = 6 := ihy m2 hm2
    have hadd : (addExp m1.2 m2.2).length = 6 := addExp_len6 m1.2 m2.2 ih1 ih2
    have hmono : m.2 = addExp m1.2 m2.2 := by rw [← hne, ← hmn]; simp [mulMono]
    rw [hmono]
    exact hadd

/--
 * The `safety` invariant for `R`: every monomial `m` of every element
 * satisfies `14 * a0degMono(m) <= wt(m)` (N=6 reading: `a_1`-degree).
 -/
theorem inR_weight_ge {y} (h : inR y) :
    ∀ m ∈ y, 14 * a0degMono m <= expWeight m.2 := by
  induction h with
  | mkZero =>
    intro m hm
    cases hm
  | mkOne =>
    intro m hm
    simp only [List.mem_cons] at hm
    rcases hm with heq | hnil
    · subst m
      exact one_base
    · cases hnil
  | mkG1 =>
    intro m hm
    have hexp : m.2 ∈ p.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact p_base m.2 hexp
  | mkG2 =>
    intro m hm
    have hexp : m.2 ∈ q.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact q_base m.2 hexp
  | mkG3 =>
    intro m hm
    have hexp : m.2 ∈ J1.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact J1_base m.2 hexp
  | mkG4 =>
    intro m hm
    have hexp : m.2 ∈ J2.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact J2_base m.2 hexp
  | mkG5 =>
    intro m hm
    have hexp : m.2 ∈ g5.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact g5_base m.2 hexp
  | mkSum hx hy ihx ihy =>
    rename_i u v
    intro m hm
    have hmap : m.2 ∈ (polyAdd u v).map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    rw [polyAdd_def] at hmap
    have hsup : m.2 ∈ (u ++ v).map (·.2) := normalize_mem_exp (u ++ v) m.2 hmap
    simp only [List.map_append] at hsup
    rcases List.mem_append.mp hsup with hu | hv
    · rcases List.exists_of_mem_map hu with ⟨n, hn, hne⟩
      have ih := ihx n hn
      simp only [a0degMono] at ih
      rw [hne] at ih
      simp only [a0degMono]
      exact ih
    · rcases List.exists_of_mem_map hv with ⟨n, hn, hne⟩
      have ih := ihy n hn
      simp only [a0degMono] at ih
      rw [hne] at ih
      simp only [a0degMono]
      exact ih
  | mkProd hx hy ihx ihy =>
    rename_i u v
    intro m hm
    rw [polyMul_def] at hm
    have hsup : m.2 ∈
      (u.flatMap (fun m1 => v.map (fun m2 => mulMono m1 m2))).map (·.2) :=
      normalize_mem_exp _ m.2 (List.mem_map.mpr ⟨m, hm, rfl⟩)
    rcases List.exists_of_mem_map hsup with ⟨n, hn, hne⟩
    rcases List.mem_flatMap.mp hn with ⟨m1, hm1, hm1m⟩
    rcases List.exists_of_mem_map hm1m with ⟨m2, hm2, hmn⟩
    have hmono : m.2 = addExp m1.2 m2.2 := by rw [← hne, ← hmn]; simp [mulMono]
    have ih1 : 14 * a0degMono m1 <= expWeight m1.2 := ihx m1 hm1
    have ih2 : 14 * a0degMono m2 <= expWeight m2.2 := ihy m2 hm2
    have hlen1 : m1.2.length = 6 := inR_len6 hx m1 hm1
    have hlen2 : m2.2.length = 6 := inR_len6 hy m2 hm2
    have ha2 : a0degMono m = a0degMono m1 + a0degMono m2 := by
      simp only [a0degMono]
      rw [hmono]
      exact a0degAddExpLen6 m1.2 m2.2 hlen1 hlen2
    have hw : expWeight m.2 = expWeight m1.2 + expWeight m2.2 := by
      rw [hmono]
      exact expWeightAddExpLen6 m1.2 m2.2 hlen1 hlen2
    calc
      14 * a0degMono m = 14 * (a0degMono m1 + a0degMono m2) := by rw [ha2]
      _ = 14 * a0degMono m1 + 14 * a0degMono m2 := by simp [Nat.mul_add]
      _ ≤ expWeight m1.2 + expWeight m2.2 := Nat.add_le_add ih1 ih2
      _ = expWeight m.2 := by rw [hw]

------------------------------------------------------------
-- 4. Exclusion: H_B outside R
------------------------------------------------------------

/--
 * `H_B notin R`: the `a_1^2` term (`11025`, weight 24) would have to
 * satisfy `14 * 2 <= 24`, i.e. `28 <= 24` -- contradiction.
 -/
theorem HB_notin_R : ¬ inR HB := by
  intro hk
  have hinv : ∀ m ∈ HB, 14 * a0degMono m <= expWeight m.2 :=
    inR_weight_ge hk
  have hterm : (11025, [2,0,0,0,4,4]) ∈ HB := HB_has_a1_sq
  have h14 : 14 * a0degMono (11025, [2,0,0,0,4,4])
      <= expWeight (11025, [2,0,0,0,4,4]).2 := hinv _ hterm
  have hwt : expWeight (11025, [2,0,0,0,4,4]).2 = 24 := by native_decide
  have ha0 : a0degMono (11025, [2,0,0,0,4,4]) = 2 := by native_decide
  rw [ha0, hwt] at h14
  exact (by decide : ¬ (28 <= 24)) h14

/--
 * The N=6 B-level strictness: a D-invariant polynomial outside
 * `k[G_1..G_5]` -- namely `H_B`.
 -/
theorem strict_R_witness : ∃ F, D F = [] ∧ ¬ inR F :=
  ⟨HB, HB_D_zero, HB_notin_R⟩

------------------------------------------------------------
-- 5. The transported relation S_B
------------------------------------------------------------

/-- The four summands of `S_B` (each uniform weight 28, certified below). -/
def SB1 : Poly := polyMul (polyPow a5 4) HB
def SB2 : Poly := polyPow g5 2
def SB3 : Poly := polyMul (smul 105 (polyMul (polyPow a5 2) (polyPow J2 5))) J1
def SB4 : Poly := smul 9 (polyPow J2 7)

/-- `S_B = a_6^4*H_B - G_5^2 - 105*a_6^2*G_4^5*G_3 - 9*G_4^7`
    (in slot reading: `a5` is N=6 `a_6`, `J1/J2` read as `G_3/G_4`). -/
def SB : Poly := polySub (polySub (polySub SB1 SB2) SB3) SB4

/-- **Main computation.** The transported weight-28 syzygy holds. -/
theorem SB_rel : SB = [] := by native_decide

/-- Mutated syzygy: `G_5^2` coefficient doubled (FALSE identity;
    kept regression test proving `SB_rel` is non-vacuous). -/
def SB_mut : Poly :=
  polySub (polySub (polySub SB1 (polyMul [(2, zeroExp)] SB2)) SB3) SB4

/-- Regression: the mutant does NOT vanish. -/
theorem SB_mut_nonzero : SB_mut ≠ [] := by native_decide

theorem SB1_weight_28 : weightedDegree SB1 = 28 := by native_decide

theorem SB2_weight_28 : weightedDegree SB2 = 28 := by native_decide

theorem SB3_weight_28 : weightedDegree SB3 = 28 := by native_decide

theorem SB4_weight_28 : weightedDegree SB4 = 28 := by native_decide

------------------------------------------------------------
-- 6. The certificate
------------------------------------------------------------

/--
 * **Certificate.** `H_B` sits in the N=6 B-hypersurface alongside the
 * five: it is invariant of weight 24 and `a_1`-degree 2, satisfies
 * the weight-28 syzygy `S_B = 0` with them, and lies strictly outside
 * `R = k[G_1..G_5]`.
 -/
theorem HB_certificate :
    D HB = [] ∧ weightedDegree HB = 24 ∧
    (∀ m ∈ HB, a0degMono m ≤ 2) ∧ SB = [] ∧ ¬ inR HB :=
  ⟨HB_D_zero, HB_weight_24, HB_a1deg_le_2, SB_rel, HB_notin_R⟩
