import AdjQuad.A6Poly

/-
`H_{20}`: hidden A6-generator (N=6 full-ring opening).

`A6 = k[a0..a6]` in one-to-one slot reading (no reindexing needed at
the A-level). `D6(a0) = a1a2`, `D6(a_i) = a_{i+1}a_{i+2}` for
`1 <= i <= 4`, `D6(a5) = D6(a6) = 0`; Fibonacci weights
`[13,8,5,3,2,1,1]` (all `A6.*` from `AdjQuad.A6Poly`).

Certifies: the six A6-generators `G_1..G_5, F0_6` are invariant with
weights `(1,1,6,4,14,25)`; `H20` (12 terms, weight 20, `a_0`-degree 1)
is invariant with `a_0`-coefficient `a_5^4 a_6^3` (split form); and
`H20` lies strictly outside `k[G_1..G_5,F0_6]` via the safety
invariant `25 * a0deg <= wt` (the `a_0`-term needs `25 <= 20`).

Explicitly OUT of scope: A6 relations/series/generation (unknown
mathematics, Phase 7+), the `a_0`-Dixmier game (paper-level, needs
UFD theory absent core-only).

Standalone: `lake build AdjQuad.A6H20`
(not imported by the root). Core-Lean only.
-/

namespace A6

/-- Variables `a0..a6` as single-monomial polys. -/
def a0 : Poly := [(1, varExp 0)]
def a1 : Poly := [(1, varExp 1)]
def a2 : Poly := [(1, varExp 2)]
def a3 : Poly := [(1, varExp 3)]
def a4 : Poly := [(1, varExp 4)]
def a5 : Poly := [(1, varExp 5)]
def a6 : Poly := [(1, varExp 6)]

/-- `D6` operator: `a1a2·∂₀ + a2a3·∂₁ + a3a4·∂₂ + a4a5·∂₃ + a5a6·∂₄`. -/
def D6 (F : Poly) : Poly :=
  let t0 := polyMul (polyMul a1 a2) (partialDeriv ⟨0, by decide⟩ F)
  let t1 := polyMul (polyMul a2 a3) (partialDeriv ⟨1, by decide⟩ F)
  let t2 := polyMul (polyMul a3 a4) (partialDeriv ⟨2, by decide⟩ F)
  let t3 := polyMul (polyMul a4 a5) (partialDeriv ⟨3, by decide⟩ F)
  let t4 := polyMul (polyMul a5 a6) (partialDeriv ⟨4, by decide⟩ F)
  polyAdd (polyAdd (polyAdd t0 t1) (polyAdd t2 t3)) t4

/-- `G_1 = a_5`, `G_2 = a_6`. -/
def G1 : Poly := [(1, varExp 5)]
def G2 : Poly := [(1, varExp 6)]

/-- `G_3 = 2a_2a_5 - a_3^2`, `G_4 = 2a_3a_6 - a_4^2`. -/
def G3 : Poly := normalize
  [((2 : Rat), addExp (varExp 2) (varExp 5)),
   ((-1 : Rat), addExp (varExp 3) (varExp 3))]
def G4 : Poly := normalize
  [((2 : Rat), addExp (varExp 3) (varExp 6)),
   ((-1 : Rat), addExp (varExp 4) (varExp 4))]

/-- `G_5`: degree-7 generator (a0-free, head-0 throughout). -/
def G5 : Poly := normalize
  [((105 : Rat), [0,1,0,0,0,2,4]),
   ((-105 : Rat), [0,0,1,1,1,1,3]),
   ((35 : Rat), [0,0,1,0,3,1,2]),
   ((35 : Rat), [0,0,0,2,3,0,2]),
   ((-21 : Rat), [0,0,0,1,5,0,1]),
   ((3 : Rat), [0,0,0,0,7,0,0])]

/-- `F0_6 = c_6^2*a_0 + G'` (13 terms, bidegree (13,25);
    `G'` a0-free; verbatim from `scripts/cas/check_N6_F0.py`). -/
def F0_6 : Poly := normalize
  [((1 : Rat), [1,0,0,0,0,4,8]),
   ((-1 : Rat), [0,1,1,0,1,3,7]),
   (((1 : Rat)/3), [0,1,0,1,3,2,6]),
   (((-1 : Rat)/15), [0,1,0,0,5,2,5]),
   (((1 : Rat)/2), [0,0,2,1,2,2,6]),
   (((-1 : Rat)/8), [0,0,2,0,4,2,5]),
   (((-1 : Rat)/3), [0,0,1,2,4,1,5]),
   (((59 : Rat)/360), [0,0,1,1,6,1,4]),
   (((-59 : Rat)/2880), [0,0,1,0,8,1,3]),
   (((1 : Rat)/18), [0,0,0,3,6,0,4]),
   (((-119 : Rat)/2880), [0,0,0,2,8,0,3]),
   (((33 : Rat)/3200), [0,0,0,1,10,0,2]),
   (((-11 : Rat)/12800), [0,0,0,0,12,0,1])]

/-- `H_{20}`: hidden A6-generator (12 terms, weight 20, a0-degree 1). -/
def H20 : Poly := normalize
  [((-19 : Rat)/480, [0,0,0,4,4,0,0]),
   ((293 : Rat)/1800, [0,0,0,5,2,0,1]),
   ((-49 : Rat)/450, [0,0,0,6,0,0,2]),
   ((19 : Rat)/120, [0,0,1,2,4,1,0]),
   ((-59 : Rat)/90, [0,0,1,3,2,1,1]),
   ((59 : Rat)/180, [0,0,1,4,0,1,2]),
   ((-1 : Rat)/8, [0,0,2,0,4,2,0]),
   (((1 : Rat))/2, [0,0,2,1,2,2,1]),
   ((-1 : Rat)/15, [0,1,0,0,5,2,0]),
   (((1 : Rat))/3, [0,1,0,1,3,2,1]),
   ((-1 : Rat), [0,1,1,0,1,3,2]),
   ((1 : Rat), [1,0,0,0,0,4,3])]

/-- `a_0`-coefficient part of `H20`: `a_5^4 a_6^3`. -/
def H20C : Poly := [(1, [0,0,0,0,0,4,3])]

/-- `a_0`-free part of `H20` (11 terms). -/
def H20R : Poly := normalize
  [((-19 : Rat)/480, [0,0,0,4,4,0,0]),
   ((293 : Rat)/1800, [0,0,0,5,2,0,1]),
   ((-49 : Rat)/450, [0,0,0,6,0,0,2]),
   ((19 : Rat)/120, [0,0,1,2,4,1,0]),
   ((-59 : Rat)/90, [0,0,1,3,2,1,1]),
   ((59 : Rat)/180, [0,0,1,4,0,1,2]),
   ((-1 : Rat)/8, [0,0,2,0,4,2,0]),
   (((1 : Rat))/2, [0,0,2,1,2,2,1]),
   ((-1 : Rat)/15, [0,1,0,0,5,2,0]),
   (((1 : Rat))/3, [0,1,0,1,3,2,1]),
   ((-1 : Rat), [0,1,1,0,1,3,2])]

------------------------------------------------------------
-- 1. Invariance of the six A6-generators + H20
------------------------------------------------------------

theorem D6_G1_zero : D6 G1 = [] := by native_decide

theorem D6_G2_zero : D6 G2 = [] := by native_decide

theorem D6_G3_zero : D6 G3 = [] := by native_decide

theorem D6_G4_zero : D6 G4 = [] := by native_decide

theorem D6_G5_zero : D6 G5 = [] := by native_decide

theorem D6_F0_6_zero : D6 F0_6 = [] := by native_decide

theorem D6_H20_zero : D6 H20 = [] := by native_decide

/-- All six A6-generators are invariant. -/
theorem A6_six_invariant :
    D6 G1 = [] ∧ D6 G2 = [] ∧ D6 G3 = [] ∧
    D6 G4 = [] ∧ D6 G5 = [] ∧ D6 F0_6 = [] :=
  ⟨D6_G1_zero, D6_G2_zero, D6_G3_zero,
   D6_G4_zero, D6_G5_zero, D6_F0_6_zero⟩

------------------------------------------------------------
-- 2. Weights
------------------------------------------------------------

theorem G1_weight_1 : weightedDegree G1 = 1 := by native_decide

theorem G2_weight_1 : weightedDegree G2 = 1 := by native_decide

theorem G3_weight_6 : weightedDegree G3 = 6 := by native_decide

theorem G4_weight_4 : weightedDegree G4 = 4 := by native_decide

theorem G5_weight_14 : weightedDegree G5 = 14 := by native_decide

theorem F0_6_weight_25 : weightedDegree F0_6 = 25 := by native_decide

theorem F0_6_terms_25 : ∀ e ∈ F0_6.map (·.2), expWeight e = 25 := by
  native_decide

theorem H20_weight_20 : weightedDegree H20 = 20 := by native_decide

theorem H20_terms_20 : ∀ e ∈ H20.map (·.2), expWeight e = 20 := by
  native_decide

theorem H20_ne_zero : H20 ≠ [] := by native_decide

/-- Exactly one `a_0`-term in `F0_6`: the `c_6^2*a_0` top (guards the
    `G'`-a0-free transcription). -/
theorem F0_6_a0_terms :
    F0_6.filter (fun m => decide (a0degMono m = 1)) =
      [((1 : Rat), [1,0,0,0,0,4,8])] := by native_decide

/-- Exactly one `a_0`-term in `H20`: the `a_0*a_5^4*a_6^3` top. -/
theorem H20_a0_terms :
    H20.filter (fun m => decide (a0degMono m = 1)) =
      [((1 : Rat), [1,0,0,0,0,4,3])] := by native_decide

------------------------------------------------------------
-- 3. The a0-split of H20
------------------------------------------------------------

/-- `H20 = a_0*C' + R'` with `C' = a_5^4 a_6^3`. -/
theorem H20_split : H20 = polyAdd (polyMul a0 H20C) H20R := by
  native_decide

/-- `R'` is a0-free. -/
theorem H20R_a0free : ∀ m ∈ H20R, a0degMono m = 0 := by native_decide

/-- `C'` is a0-free (so it is exactly the `a_0`-coefficient). -/
theorem H20C_a0free : ∀ m ∈ H20C, a0degMono m = 0 := by native_decide

------------------------------------------------------------
-- 4. Generator base facts (all a0-free except F0_6's top term)
------------------------------------------------------------

theorem G1_len7 : ∀ e ∈ G1.map (·.2), e.length = 7 := by native_decide

theorem G2_len7 : ∀ e ∈ G2.map (·.2), e.length = 7 := by native_decide

theorem G3_len7 : ∀ e ∈ G3.map (·.2), e.length = 7 := by native_decide

theorem G4_len7 : ∀ e ∈ G4.map (·.2), e.length = 7 := by native_decide

theorem G5_len7 : ∀ e ∈ G5.map (·.2), e.length = 7 := by native_decide

theorem F0_6_len7 : ∀ e ∈ F0_6.map (·.2), e.length = 7 := by native_decide

theorem H20_len7 : ∀ e ∈ H20.map (·.2), e.length = 7 := by native_decide

theorem G1_base : ∀ e ∈ G1.map (·.2), 25 * a0deg e <= expWeight e := by
  native_decide

theorem G2_base : ∀ e ∈ G2.map (·.2), 25 * a0deg e <= expWeight e := by
  native_decide

theorem G3_base : ∀ e ∈ G3.map (·.2), 25 * a0deg e <= expWeight e := by
  native_decide

theorem G4_base : ∀ e ∈ G4.map (·.2), 25 * a0deg e <= expWeight e := by
  native_decide

theorem G5_base : ∀ e ∈ G5.map (·.2), 25 * a0deg e <= expWeight e := by
  native_decide

theorem F0_6_base : ∀ e ∈ F0_6.map (·.2), 25 * a0deg e <= expWeight e := by
  native_decide

------------------------------------------------------------
-- 5. The subalgebra predicate + the `safety` invariant
------------------------------------------------------------

/-
 * `inR6` is the smallest k-subalgebra containing
 * `{G_1..G_5, F0_6}`. `inR6 y` reads `y in k[G,F0_6]`.
 -/
inductive inR6 : Poly → Prop
  | mkZero : inR6 []
  | mkOne : inR6 [(1, zeroExp)]
  | mkG1 : inR6 G1
  | mkG2 : inR6 G2
  | mkG3 : inR6 G3
  | mkG4 : inR6 G4
  | mkG5 : inR6 G5
  | mkF0 : inR6 F0_6
  | mkSum {x y} : inR6 x → inR6 y → inR6 (polyAdd x y)
  | mkProd {x y} : inR6 x → inR6 y → inR6 (polyMul x y)

/-- Every term of every `k[G,F0_6]` element is length-7. -/
theorem inR6_len7 {y} (h : inR6 y) : ∀ m ∈ y, m.2.length = 7 := by
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
    have hexp : m.2 ∈ G1.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact G1_len7 m.2 hexp
  | mkG2 =>
    intro m hm
    have hexp : m.2 ∈ G2.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact G2_len7 m.2 hexp
  | mkG3 =>
    intro m hm
    have hexp : m.2 ∈ G3.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact G3_len7 m.2 hexp
  | mkG4 =>
    intro m hm
    have hexp : m.2 ∈ G4.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact G4_len7 m.2 hexp
  | mkG5 =>
    intro m hm
    have hexp : m.2 ∈ G5.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact G5_len7 m.2 hexp
  | mkF0 =>
    intro m hm
    have hexp : m.2 ∈ F0_6.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact F0_6_len7 m.2 hexp
  | mkSum hx hy ihx ihy =>
    rename_i u v
    intro m hm
    have hmap : m.2 ∈ (polyAdd u v).map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    rw [polyAdd_def] at hmap
    have hsup : m.2 ∈ (u ++ v).map (·.2) := normalize_mem_exp (u ++ v) m.2 hmap
    simp only [List.map_append] at hsup
    rcases List.mem_append.mp hsup with hu | hv
    · rcases List.exists_of_mem_map hu with ⟨n, hn, hne⟩
      have ih : n.2.length = 7 := ihx n hn
      rw [hne] at ih
      exact ih
    · rcases List.exists_of_mem_map hv with ⟨n, hn, hne⟩
      have ih : n.2.length = 7 := ihy n hn
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
    have ih1 : m1.2.length = 7 := ihx m1 hm1
    have ih2 : m2.2.length = 7 := ihy m2 hm2
    have hadd : (addExp m1.2 m2.2).length = 7 := addExp_len7 m1.2 m2.2 ih1 ih2
    have hmono : m.2 = addExp m1.2 m2.2 := by rw [← hne, ← hmn]; simp [mulMono]
    rw [hmono]
    exact hadd

/--
 * The `safety` invariant: every monomial `m` of every element of
 * `k[G,F0_6]` satisfies `25 * a0degMono(m) <= wt(m)`.
 -/
theorem inR6_weight_ge {y} (h : inR6 y) :
    ∀ m ∈ y, 25 * a0degMono m <= expWeight m.2 := by
  induction h with
  | mkZero =>
    intro m hm
    cases hm
  | mkOne =>
    intro m hm
    simp only [List.mem_cons] at hm
    rcases hm with heq | hnil
    · subst m
      simp only [a0degMono, zeroExp]
      simp [a0deg, expWeight]
    · cases hnil
  | mkG1 =>
    intro m hm
    have hexp : m.2 ∈ G1.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact G1_base m.2 hexp
  | mkG2 =>
    intro m hm
    have hexp : m.2 ∈ G2.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact G2_base m.2 hexp
  | mkG3 =>
    intro m hm
    have hexp : m.2 ∈ G3.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact G3_base m.2 hexp
  | mkG4 =>
    intro m hm
    have hexp : m.2 ∈ G4.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact G4_base m.2 hexp
  | mkG5 =>
    intro m hm
    have hexp : m.2 ∈ G5.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact G5_base m.2 hexp
  | mkF0 =>
    intro m hm
    have hexp : m.2 ∈ F0_6.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact F0_6_base m.2 hexp
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
    have ih1 : 25 * a0degMono m1 <= expWeight m1.2 := ihx m1 hm1
    have ih2 : 25 * a0degMono m2 <= expWeight m2.2 := ihy m2 hm2
    have hlen1 : m1.2.length = 7 := inR6_len7 hx m1 hm1
    have hlen2 : m2.2.length = 7 := inR6_len7 hy m2 hm2
    have ha2 : a0degMono m = a0degMono m1 + a0degMono m2 := by
      simp only [a0degMono]
      rw [hmono]
      exact a0degAddExpLen7 m1.2 m2.2 hlen1 hlen2
    have hw : expWeight m.2 = expWeight m1.2 + expWeight m2.2 := by
      rw [hmono]
      exact expWeightAddExpLen7 m1.2 m2.2 hlen1 hlen2
    calc
      25 * a0degMono m = 25 * (a0degMono m1 + a0degMono m2) := by rw [ha2]
      _ = 25 * a0degMono m1 + 25 * a0degMono m2 := by simp [Nat.mul_add]
      _ ≤ expWeight m1.2 + expWeight m2.2 := Nat.add_le_add ih1 ih2
      _ = expWeight m.2 := by rw [hw]

------------------------------------------------------------
-- 6. Exclusion: H20 outside k[G,F0_6]
------------------------------------------------------------

/-- The `a_0`-term of `H20` is present. -/
theorem H20_has_a0_term : ((1 : Rat), [1,0,0,0,0,4,3]) ∈ H20 := by
  native_decide

/--
 * `H20 notin k[G,F0_6]`: the `a_0`-term (`a0deg` 1, weight 20)
 * would have to satisfy `25 * 1 <= 20` -- contradiction.
 -/
theorem H20_notin_R6 : ¬ inR6 H20 := by
  intro hk
  have hinv : ∀ m ∈ H20, 25 * a0degMono m <= expWeight m.2 :=
    inR6_weight_ge hk
  have hterm : ((1 : Rat), [1,0,0,0,0,4,3]) ∈ H20 := H20_has_a0_term
  have h25 : 25 * a0degMono ((1 : Rat), [1,0,0,0,0,4,3])
      <= expWeight ((1 : Rat), [1,0,0,0,0,4,3]).2 := hinv _ hterm
  have hwt : expWeight ((1 : Rat), [1,0,0,0,0,4,3]).2 = 20 := by native_decide
  have ha0 : a0degMono ((1 : Rat), [1,0,0,0,0,4,3]) = 1 := by native_decide
  rw [ha0, hwt] at h25
  exact (by decide : ¬ (25 <= 20)) h25

/--
 * Strictness at the A6-level: a D6-invariant polynomial outside
 * `k[G_1..G_5,F0_6]` -- namely H20.
 -/
theorem strict_R6_witness : ∃ F, D6 F = [] ∧ ¬ inR6 F :=
  ⟨H20, D6_H20_zero, H20_notin_R6⟩

------------------------------------------------------------
-- 7. The certificate
------------------------------------------------------------

/--
 * **Certificate.** `H20` sits outside `k[G_1..G_5,F0_6]` as a genuine
 * invariant: weight 20, `a_0`-split with coefficient `a_5^4 a_6^3`,
 * `D6`-invariant, and not in the six-generator ring.
 -/
theorem H20_certificate :
    D6 H20 = [] ∧ weightedDegree H20 = 20 ∧
    H20 = polyAdd (polyMul a0 H20C) H20R ∧ ¬ inR6 H20 :=
  ⟨D6_H20_zero, H20_weight_20, H20_split, H20_notin_R6⟩

end A6
