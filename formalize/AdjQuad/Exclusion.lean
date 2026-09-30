import AdjQuad.Counterexample

/-
H ∉ K[F0], `K[F0] = k[p, q, J1, J2, F0]`.

In `A = k[a0..a5]` only `F0` carries `a0` (each `F0` monomial has
a0-degree ≤ 1 with a0-part of weight 14; `p,q,J1,J2` have a0-degree 0).
Hence every monomial of `K[F0]` satisfies `14 * a0deg(m) ≤ wt(m)`
(by induction on the subalgebra predicate `inK_F0`); an a0-degree-2
monomial weighs at least 28. `H` has `D(H) = 0`, weight 24 throughout,
and the a0-degree-2 term `11025 a0^2 a4^4 a5^4` — impossible in `K[F0]`.

Provides `inK_F0`, `inK_F0_weight_ge_14_a0deg`, `H_notin_K_F0`.
Core-Lean only. Standalone: `lake build AdjQuad.Exclusion`.
-/

------------------------------------------------------------
-- 1. Local helpers: a0-degree
------------------------------------------------------------

/-- a0-exponent of an exponent vector (0 if empty). -/
def a0deg (e : Exp) : Nat :=
  match e with
  | [] => 0
  | x :: _ => x

/-- a0-degree of a monomial. -/
def a0degMono (m : Mono) : Nat := a0deg m.2

theorem weights_len6 : weights.length = 6 := by native_decide

------------------------------------------------------------
-- 2. Core Nat helper
------------------------------------------------------------

/-- `k.succ = 0` is impossible. -/
theorem nat_succ_not_zero {k : Nat} (h : k.succ = 0) : False :=
  Nat.succ_ne_zero k h

------------------------------------------------------------
-- 3. Equal-length list length lemmas
------------------------------------------------------------

/-- The length of a `zipWith` of two lists of common length `n` is `n`. -/
theorem zipWith_len_aux {α} (n : Nat) (f : α → α → α) :
    ∀ e1 e2 : List α, e1.length = n → e2.length = n →
      (List.zipWith f e1 e2).length = n := by
  intro e1 e2 h1 h2
  induction n generalizing e1 e2 with
  | zero =>
    have : e1 = [] := List.eq_nil_of_length_eq_zero h1
    have : e2 = [] := List.eq_nil_of_length_eq_zero h2
    subst e1 e2
    simp [List.zipWith, List.length_nil]
  | succ k ih =>
    cases e1 with
    | nil =>
      exfalso
      have : k.succ = 0 := by rw [List.length_nil] at h1; exact h1.symm
      exact nat_succ_not_zero this
    | cons x t1 =>
      cases e2 with
      | nil =>
        exfalso
        have : k.succ = 0 := by rw [List.length_nil] at h2; exact h2.symm
        exact nat_succ_not_zero this
      | cons y t2 =>
        have ht1 : t1.length = k := by
          have hc : (x :: t1).length = k.succ := by simpa using h1
          simp only [List.length_cons, Nat.succ_eq_add_one] at hc
          exact Nat.add_right_cancel hc
        have ht2 : t2.length = k := by
          have hc : (y :: t2).length = k.succ := by simpa using h2
          simp only [List.length_cons, Nat.succ_eq_add_one] at hc
          exact Nat.add_right_cancel hc
        have hih : (List.zipWith f t1 t2).length = k := ih t1 t2 ht1 ht2
        simp only [List.zipWith, List.length_cons]
        rw [hih]

/-- `addExp` of two length-6 exponent vectors is length-6. -/
theorem addExp_len6 (e1 e2 : Exp) (h1 : e1.length = 6) (h2 : e2.length = 6) :
    (addExp e1 e2).length = 6 :=
  zipWith_len_aux _ _ e1 e2 h1 h2

/-- a0-degree of the product of two length-6 exponent vectors adds. -/
theorem a0degAddExpLen6 (e1 e2 : Exp) (h1 : e1.length = 6) (h2 : e2.length = 6) :
    a0deg (addExp e1 e2) = a0deg e1 + a0deg e2 := by
  cases e1 with
  | nil =>
    exfalso
    rw [List.length_nil] at h1
    exact (by decide : 0 ≠ 6) h1
  | cons x1 t1 =>
    cases e2 with
    | nil =>
      exfalso
      rw [List.length_nil] at h2
      exact (by decide : 0 ≠ 6) h2
    | cons x2 t2 =>
      simp [a0deg, addExp, List.zipWith]

------------------------------------------------------------
-- 4. foldl / zipWith distributivity (length-induction)
------------------------------------------------------------

/-- For a list and any start `k`, folding `(·+·)` from `k` equals
    `k +` folding from `0`: `l.foldl (·+·) k = k + l.foldl (·+·) 0`. -/
theorem foldl_add_init (l : List Nat) (k : Nat) :
    l.foldl (· + ·) k = k + l.foldl (· + ·) 0 := by
  induction l generalizing k with
  | nil =>
    simp [List.foldl, Nat.add_zero]
  | cons a t ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (k + a), ih a]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/--
 * For equal-length lists (common length `n`), folding `(·+·)` from `0` over
 * the pointwise zip equals the sum of the individual folds.
 -/
theorem foldl_zip_plus_aux (n : Nat) :
    ∀ L M : List Nat, L.length = n → M.length = n →
      (L.zipWith (· + ·) M).foldl (· + ·) 0 = L.foldl (· + ·) 0 + M.foldl (· + ·) 0 := by
  induction n with
  | zero =>
    intro L M hL hM
    rw [List.eq_nil_of_length_eq_zero hL, List.eq_nil_of_length_eq_zero hM]
    simp [List.zipWith, List.foldl]
  | succ k ih =>
    intro L M hL hM
    cases L with
    | nil =>
      exfalso
      have : k.succ = 0 := by rw [List.length_nil] at hL; exact hL.symm
      exact nat_succ_not_zero this
    | cons a tL =>
      cases M with
      | nil =>
        exfalso
        have : k.succ = 0 := by rw [List.length_nil] at hM; exact hM.symm
        exact nat_succ_not_zero this
      | cons b tM =>
        have htL : tL.length = k := by
          have hc : (a :: tL).length = k.succ := by simpa using hL
          simp only [List.length_cons, Nat.succ_eq_add_one] at hc
          exact Nat.add_right_cancel hc
        have htM : tM.length = k := by
          have hc : (b :: tM).length = k.succ := by simpa using hM
          simp only [List.length_cons, Nat.succ_eq_add_one] at hc
          exact Nat.add_right_cancel hc
        simp only [List.zipWith, List.foldl_cons, Nat.zero_add]
        rw [foldl_add_init (tL.zipWith (· + ·) tM) (a + b),
            ih tL tM htL htM,
            foldl_add_init tL a, foldl_add_init tM b]
        simp [Nat.add_assoc, Nat.add_left_comm]

/-- Corollary of `foldl_zip_plus_aux` for two equal-length lists. -/
theorem foldl_zip_plus (L M : List Nat) (hLM : L.length = M.length) :
    (L.zipWith (· + ·) M).foldl (· + ·) 0 = L.foldl (· + ·) 0 + M.foldl (· + ·) 0 := by
  exact foldl_zip_plus_aux (L.length) L M (by rfl) hLM.symm

/--
 * Pointwise, for equal-length lists (common length `n`):
 * `w *.< (e1 +. e2) = (w *.< e1) +. (w *.< e2)`,
 * where `+.` = `zipWith (+)`, `*.<` = `zipWith (·*·)`.
 -/
theorem zipWith_mul_plus_aux (n : Nat) :
    ∀ w e1 e2 : List Nat,
      w.length = n → e1.length = n → e2.length = n →
      w.zipWith (· * ·) (e1.zipWith (· + ·) e2) =
        (w.zipWith (· * ·) e1).zipWith (· + ·) (w.zipWith (· * ·) e2) := by
  induction n with
  | zero =>
    intro w e1 e2 hw he1 he2
    rw [List.eq_nil_of_length_eq_zero hw, List.eq_nil_of_length_eq_zero he1,
        List.eq_nil_of_length_eq_zero he2]
    simp [List.zipWith]
  | succ k ih =>
    intro w e1 e2 hw he1 he2
    cases w with
    | nil =>
      exfalso
      have : k.succ = 0 := by rw [List.length_nil] at hw; exact hw.symm
      exact nat_succ_not_zero this
    | cons x1 t1 =>
      cases e1 with
      | nil =>
        exfalso
        have : k.succ = 0 := by rw [List.length_nil] at he1; exact he1.symm
        exact nat_succ_not_zero this
      | cons x2 t2 =>
        cases e2 with
        | nil =>
          exfalso
          have : k.succ = 0 := by rw [List.length_nil] at he2; exact he2.symm
          exact nat_succ_not_zero this
        | cons x3 t3 =>
          have ht1 : t1.length = k := by
            have hc : (x1 :: t1).length = k.succ := by simpa using hw
            simp only [List.length_cons, Nat.succ_eq_add_one] at hc
            exact Nat.add_right_cancel hc
          have ht2 : t2.length = k := by
            have hc : (x2 :: t2).length = k.succ := by simpa using he1
            simp only [List.length_cons, Nat.succ_eq_add_one] at hc
            exact Nat.add_right_cancel hc
          have ht3 : t3.length = k := by
            have hc : (x3 :: t3).length = k.succ := by simpa using he2
            simp only [List.length_cons, Nat.succ_eq_add_one] at hc
            exact Nat.add_right_cancel hc
          simp [List.zipWith, Nat.mul_add, ih t1 t2 t3 ht1 ht2 ht3]

/-- Corollary of `zipWith_mul_plus_aux` for three equal-length lists. -/
theorem zipWith_mul_plus (w e1 e2 : List Nat)
    (h1 : w.length = e1.length) (h2 : e1.length = e2.length) :
    w.zipWith (· * ·) (e1.zipWith (· + ·) e2) =
      (w.zipWith (· * ·) e1).zipWith (· + ·) (w.zipWith (· * ·) e2) := by
  exact zipWith_mul_plus_aux (e1.length) w e1 e2 h1 (by rfl) h2.symm

/--
 * Weighted weight of the product of two length-6 exponent vectors splits
 * additively: `wt(e1 +. e2) = wt(e1) + wt(e2)`.
 -/
theorem expWeightAddExpLen6 (e1 e2 : Exp) (h1 : e1.length = 6) (h2 : e2.length = 6) :
    expWeight (addExp e1 e2) = expWeight e1 + expWeight e2 := by
  unfold expWeight addExp
  rw [zipWith_mul_plus weights e1 e2 (by simp [weights_len6, h1]) (by simp [h1, h2])]
  have hL : (weights.zipWith (· * ·) e1).length = (weights.zipWith (· * ·) e2).length := by
    have l1 : (weights.zipWith (· * ·) e1).length = 6 :=
      zipWith_len_aux _ _ weights e1 weights_len6 h1
    have l2 : (weights.zipWith (· * ·) e2).length = 6 :=
      zipWith_len_aux _ _ weights e2 weights_len6 h2
    rw [l1, l2]
  rw [foldl_zip_plus _ _ hL]

------------------------------------------------------------
-- 5. Support-inclusion lemmas (reuse Poly.lean; no shared file changed)
------------------------------------------------------------

/-- `insertCombine` adds at most the exponent vector of the inserted monomial. -/
theorem insertCombine_mem (m : Mono) (q : Poly) (x : Exp) :
    x ∈ (insertCombine m q).map (·.2) → x ∈ q.map (·.2) ∨ x = m.2 := by
  intro h
  unfold insertCombine at h
  by_cases hm : m.1 = 0
  · rw [if_pos hm] at h
    exact Or.inl h
  · by_cases hmem : m.2 ∈ q.map (·.2)
    · rw [if_neg hm, if_pos hmem] at h
      rcases insertCombineGo_mem m q x h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr h2
    · rw [if_neg hm, if_neg hmem] at h
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with hx2 | hmem'
      · exact Or.inr hx2
      · exact Or.inl hmem'

/-- `combine` never introduces a new exponent vector. -/
theorem combine_mem (p : Poly) (x : Exp) :
    x ∈ (combine p).map (·.2) → x ∈ p.map (·.2) := by
  induction p with
  | nil =>
    intro h
    simpa [combine, List.map_nil] using h
  | cons m rest ih =>
    intro h
    simp only [combine] at h
    rcases insertCombine_mem m (combine rest) x h with h1 | h2
    · have hrest : x ∈ rest.map (·.2) := ih h1
      simp only [List.map_cons, List.mem_cons]
      exact Or.inr hrest
    · rw [h2]
      simp only [List.map_cons]
      exact List.mem_cons_self

/-- `normalize` = `sortPoly ∘ combine` never introduces a new exponent vector. -/
theorem normalize_mem_exp (p : Poly) (x : Exp) :
    x ∈ (normalize p).map (·.2) → x ∈ p.map (·.2) := by
  intro h
  unfold normalize at h
  have hcomb : x ∈ (combine p).map (·.2) := by
    have hperm : List.Perm (sortPoly (combine p)) (combine p) := sortPoly_perm (combine p)
    have hperm2 : List.Perm ((sortPoly (combine p)).map (·.2)) ((combine p).map (·.2)) :=
      List.Perm.map (·.2) hperm
    exact (List.Perm.mem_iff hperm2).mp h
  exact combine_mem p x hcomb

------------------------------------------------------------
-- 6. Concrete generator facts (closed; native_decide)
------------------------------------------------------------

/-- Length-6 facts for the generator (and counterexample) polynomials. -/
theorem p_len6 : ∀ e ∈ p.map (·.2), e.length = 6 := by native_decide

theorem q_len6 : ∀ e ∈ q.map (·.2), e.length = 6 := by native_decide

theorem J1_len6 : ∀ e ∈ J1.map (·.2), e.length = 6 := by native_decide

theorem J2_len6 : ∀ e ∈ J2.map (·.2), e.length = 6 := by native_decide

theorem F0_len6 : ∀ e ∈ F0.map (·.2), e.length = 6 := by native_decide

theorem H_len6 : ∀ e ∈ H.map (·.2), e.length = 6 := by native_decide

/-- `safety` base facts: `14 * a0deg(e) <= wt(e)` for each monomial of each
    base generator (and of the unit). All closed; `native_decide`. -/
theorem one_base : 14 * a0deg zeroExp <= expWeight zeroExp := by native_decide

theorem p_base : ∀ e ∈ p.map (·.2), 14 * a0deg e <= expWeight e := by native_decide

theorem q_base : ∀ e ∈ q.map (·.2), 14 * a0deg e <= expWeight e := by native_decide

theorem J1_base : ∀ e ∈ J1.map (·.2), 14 * a0deg e <= expWeight e := by native_decide

theorem J2_base : ∀ e ∈ J2.map (·.2), 14 * a0deg e <= expWeight e := by native_decide

theorem F0_base : ∀ e ∈ F0.map (·.2), 14 * a0deg e <= expWeight e := by native_decide

------------------------------------------------------------
-- 7. The subalgebra predicate + the `safety` invariant
------------------------------------------------------------

/-
 * `inK_F0` is, by construction, the smallest k-subalgebra of
 * A = k[a0..a5] containing `{p, q, J1, J2, F0}`: generated from 0, 1, the
 * five generators under addition and multiplication. `inK_F0 y` reads
 * `y in K[F0]` with `K[F0] := k[p, q, J1, J2, F0]`.
 -/
inductive inK_F0 : Poly → Prop
  | mkZero : inK_F0 []
  | mkOne : inK_F0 [(1, zeroExp)]
  | mkP : inK_F0 p
  | mkQ : inK_F0 q
  | mkJ1 : inK_F0 J1
  | mkJ2 : inK_F0 J2
  | mkF0 : inK_F0 F0
  | mkSum {x y} : inK_F0 x → inK_F0 y → inK_F0 (polyAdd x y)
  | mkProd {x y} : inK_F0 x → inK_F0 y → inK_F0 (polyMul x y)

/-- Every term of every `K[F0]` element has a length-6 exponent vector. -/
theorem inK_F0_len6 {y} (h : inK_F0 y) : ∀ m ∈ y, m.2.length = 6 := by
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
  | mkP =>
    intro m hm
    have hexp : m.2 ∈ p.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact p_len6 m.2 hexp
  | mkQ =>
    intro m hm
    have hexp : m.2 ∈ q.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact q_len6 m.2 hexp
  | mkJ1 =>
    intro m hm
    have hexp : m.2 ∈ J1.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact J1_len6 m.2 hexp
  | mkJ2 =>
    intro m hm
    have hexp : m.2 ∈ J2.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact J2_len6 m.2 hexp
  | mkF0 =>
    intro m hm
    have hexp : m.2 ∈ F0.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    exact F0_len6 m.2 hexp
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
 * The `safety` invariant: for every element of `K[F0]`, every monomial `m`
 * satisfies `14 * a0deg(m) <= wt(m)`.
 -/
theorem inK_F0_weight_ge_14_a0deg {y} (h : inK_F0 y) :
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
  | mkP =>
    intro m hm
    have hexp : m.2 ∈ p.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact p_base m.2 hexp
  | mkQ =>
    intro m hm
    have hexp : m.2 ∈ q.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact q_base m.2 hexp
  | mkJ1 =>
    intro m hm
    have hexp : m.2 ∈ J1.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact J1_base m.2 hexp
  | mkJ2 =>
    intro m hm
    have hexp : m.2 ∈ J2.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact J2_base m.2 hexp
  | mkF0 =>
    intro m hm
    have hexp : m.2 ∈ F0.map (·.2) := List.mem_map.mpr ⟨m, hm, rfl⟩
    simp only [a0degMono]
    exact F0_base m.2 hexp
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
    have hlen1 : m1.2.length = 6 := inK_F0_len6 hx m1 hm1
    have hlen2 : m2.2.length = 6 := inK_F0_len6 hy m2 hm2
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
-- 8. The refutation
------------------------------------------------------------

/--
 * `H notin K[F0]`: assume `inK_F0 H`. By the `safety` invariant, the
 * concrete term `(11025, [2,0,0,0,4,4])` of `H` (a0-degree 2, weight 24)
 * would have to satisfy `14 * 2 <= 24`, i.e. `28 <= 24` -- contradiction.
 -/
theorem H_notin_K_F0 : ¬ inK_F0 H := by
  intro hk
  have hinv : ∀ m ∈ H, 14 * a0degMono m <= expWeight m.2 := inK_F0_weight_ge_14_a0deg hk
  have hterm : (11025, [2,0,0,0,4,4]) ∈ H := H_has_a0_sq
  have h14 : 14 * a0degMono (11025, [2,0,0,0,4,4]) <= expWeight (11025, [2,0,0,0,4,4]).2 :=
    hinv _ hterm
  have hwt : expWeight (11025, [2,0,0,0,4,4]).2 = 24 := by native_decide
  have ha0 : a0degMono (11025, [2,0,0,0,4,4]) = 2 := by native_decide
  rw [ha0, hwt] at h14
  exact (by decide : ¬ (28 <= 24)) h14

/--
 * The formal content of `A_5^D properly contains K[F0]`: there exists a
 * D-invariant polynomial not in k[p, q, J1, J2, F0] -- namely H.
 -/
theorem strict_superset_witness : ∃ F, D F = [] ∧ ¬ inK_F0 F :=
  ⟨H, H_D_zero, H_notin_K_F0⟩