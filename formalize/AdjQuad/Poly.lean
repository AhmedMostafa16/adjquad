/-
Minimal certified multivariate polynomial library over Rat in 6 variables.

- monomial exponent vector: `Exp = List Nat` (length 6 by convention)
- poly: `Poly = List (Rat × Exp)` kept normalized via `normalize`
  (combine like terms by adding coefficients, drop zero coefficients, sorted
  by lexicographic exponent order using `List.mergeSort`).

Core-Lean only. All operations call `normalize`.
-/

abbrev Exp := List Nat
abbrev Mono := Rat × Exp
abbrev Poly := List Mono

/-- Zero exponent vector `[0,0,0,0,0,0]`. -/
def zeroExp : Exp := [0,0,0,0,0,0]

/-- Weights `[8,5,3,2,1,1]` for weighted degree. -/
def weights : List Nat := [8,5,3,2,1,1]

/-- Single-variable exponent: 1 at position `i`, 0 elsewhere (length 6). -/
def varExp (i : Nat) : Exp := (List.replicate 6 0).set i 1

/-- Pointwise addition of exponent vectors (monomial multiplication). -/
def addExp (e1 e2 : Exp) : Exp := List.zipWith (· + ·) e1 e2

/-- Weighted weight of a single exponent vector. -/
def expWeight (e : Exp) : Nat :=
  ((weights.zipWith (· * ·) e).foldl (· + ·) 0)

/-- Weighted degree of a poly: max over terms, 0 for empty. -/
def weightedDegree (p : Poly) : Nat :=
  p.foldl (fun acc m => Nat.max acc (expWeight m.2)) 0

theorem weightedDegree_nil : weightedDegree [] = 0 := rfl

theorem expWeight_a0 : expWeight [1,0,0,0,0,0] = 8 := by native_decide

/-- Monomial multiplication: multiply coeffs, add exps. -/
def mulMono (m1 m2 : Mono) : Mono := (m1.1 * m2.1, addExp m1.2 m2.2)

theorem mulMono_correct (c1 c2 : Rat) (e1 e2 : Exp) :
    mulMono (c1, e1) (c2, e2) = (c1 * c2, addExp e1 e2) := rfl

/-- Monomial partial derivative w.r.t. variable `i : Fin 6`.
Returns `none` when the term vanishes (exponent 0 or malformed). -/
def derivMono (i : Fin 6) (m : Mono) : Option Mono :=
  match m.2[i.val]? with
  | none => none
  | some 0 => none
  | some (n+1) =>
    let c' := m.1 * ((n+1 : Nat) : Rat)
    let e' := m.2.set i.val n
    some (c', e')

theorem derivMono_example :
    derivMono ⟨0, by decide⟩ ((2 : Rat), [3,0,0,0,0,0]) =
      some ((6 : Rat), [2,0,0,0,0,0]) := by native_decide

theorem derivMono_vanishes :
    derivMono ⟨0, by decide⟩ ((5 : Rat), [0,1,0,0,0,0]) = none := by native_decide

/-- Lexicographic comparison on monomials by exponent vector (Bool). -/
def monoLE (a b : Mono) : Bool := decide (a.2 ≤ b.2)

theorem monoLE_trans : ∀ (a b c : Mono), monoLE a b → monoLE b c → monoLE a c := by
  intro a b c hab hbc
  unfold monoLE at *
  simp at *
  exact Std.le_trans hab hbc

theorem monoLE_total : ∀ (a b : Mono), monoLE a b || monoLE b a := by
  intro a b
  unfold monoLE
  simp
  exact Std.le_total

/-- Combine helper: scan for equal exp, add coeffs, drop zeros created.
Appends `[m]` when not found (used only when membership holds in `insertCombine`). -/
def insertCombineGo (m : Mono) : Poly → Poly
  | [] => [m]
  | (c, e) :: rest =>
    if e = m.2 then
      if c + m.1 = 0 then rest else (c + m.1, e) :: rest
    else (c, e) :: insertCombineGo m rest

/-- Order-preserving insert with combining + zero-dropping.
Prepends when exp not present (preserves input order for distinct exps). -/
def insertCombine (m : Mono) (q : Poly) : Poly :=
  if m.1 = 0 then q
  else if m.2 ∈ q.map (·.2) then insertCombineGo m q else m :: q

/-- Combine like terms + drop zeros (order-preserving, no sorting). -/
def combine : Poly → Poly
  | [] => []
  | m :: rest => insertCombine m (combine rest)

theorem combine_nil : combine [] = [] := rfl

/-- No zero coefficients. -/
def hasNoZeros (p : Poly) : Prop := ∀ m ∈ p, m.1 ≠ 0

/-- No duplicate exps (`Nodup` on second components). -/
def hasNoDups (p : Poly) : Prop := List.Nodup (p.map (·.2))

theorem insertCombineGo_noZeros (m : Mono) (q : Poly)
    (hm : m.1 ≠ 0) (hq : hasNoZeros q) : hasNoZeros (insertCombineGo m q) := by
  unfold hasNoZeros at *
  induction q with
  | nil =>
    intro x hx
    simp [insertCombineGo] at hx
    obtain rfl := hx
    exact hm
  | cons hd tl ih =>
    obtain ⟨c, e⟩ := hd
    have htl : ∀ y ∈ tl, y.1 ≠ 0 := by
      intro y hy
      exact hq y (List.mem_cons_of_mem (c, e) hy)
    have ih' := ih htl
    simp only [insertCombineGo]
    split
    · next heq =>
      split
      · next hzero =>
        intro x hx
        exact hq x (List.mem_cons_of_mem (c, e) hx)
      · next hnonzero =>
        intro x hx
        simp at hx
        rcases hx with rfl | hmem
        · simp
          exact hnonzero
        · exact htl x hmem
    · next hne =>
      intro x hx
      simp at hx
      rcases hx with rfl | hmem
      · exact hq _ List.mem_cons_self
      · exact ih' x hmem

theorem insertCombineGo_mem (m : Mono) (q : Poly) (x : Exp) :
    x ∈ (insertCombineGo m q).map (·.2) → x ∈ q.map (·.2) ∨ x = m.2 := by
  induction q with
  | nil =>
    intro h
    have hmap : ([m].map (·.2)) = [m.2] := rfl
    rw [insertCombineGo] at h
    rw [hmap, List.mem_cons, List.mem_nil_iff] at h
    rcases h with rfl | hfalse
    · exact Or.inr rfl
    · exact False.elim hfalse
  | cons hd tl ih =>
    obtain ⟨c, e⟩ := hd
    have hmap_cons : (((c, e) :: tl).map (·.2)) = e :: tl.map (·.2) := rfl
    simp only [insertCombineGo]
    split
    · next heq =>
      split
      · next hzero =>
        intro h
        have hmem : x ∈ (((c, e) :: tl).map (·.2)) := by
          rw [hmap_cons]
          exact List.mem_cons_of_mem e h
        exact Or.inl hmem
      · next hnonzero =>
        intro h
        have hmap_out : ((((c + m.1, e) :: tl).map (·.2))) = e :: tl.map (·.2) := rfl
        rw [hmap_out, List.mem_cons] at h
        rcases h with heq2 | hmem
        · subst heq2
          exact Or.inl List.mem_cons_self
        · have hmem2 : x ∈ (((c, e) :: tl).map (·.2)) := by
            rw [hmap_cons]
            exact List.mem_cons_of_mem e hmem
          exact Or.inl hmem2
    · next hne =>
      intro h
      have hmap_out : ((((c, e) :: insertCombineGo m tl).map (·.2))) = e :: (insertCombineGo m tl).map (·.2) := rfl
      rw [hmap_out, List.mem_cons] at h
      rcases h with heq2 | hmem
      · subst heq2
        exact Or.inl List.mem_cons_self
      · rcases ih hmem with h1 | h2
        · have hmem2 : x ∈ (((c, e) :: tl).map (·.2)) := by
            rw [hmap_cons]
            exact List.mem_cons_of_mem e h1
          exact Or.inl hmem2
        · exact Or.inr h2

theorem insertCombineGo_nodup (m : Mono) (q : Poly)
    (hq : List.Nodup (q.map (·.2))) : List.Nodup ((insertCombineGo m q).map (·.2)) := by
  induction q with
  | nil =>
    simp [insertCombineGo]
  | cons hd tl ih =>
    obtain ⟨c, e⟩ := hd
    have hmap_cons : (((c, e) :: tl).map (·.2)) = e :: tl.map (·.2) := rfl
    rw [hmap_cons, List.nodup_cons] at hq
    obtain ⟨he_notin, htl_nodup⟩ := hq
    have ih' := ih htl_nodup
    simp only [insertCombineGo]
    split
    · next heq =>
      split
      · next hzero =>
        exact htl_nodup
      · next hnonzero =>
        have hmap_out : ((((c + m.1, e) :: tl).map (·.2))) = e :: tl.map (·.2) := rfl
        rw [hmap_out, List.nodup_cons]
        exact ⟨he_notin, htl_nodup⟩
    · next hne =>
      have hmap_out : ((((c, e) :: insertCombineGo m tl).map (·.2))) = e :: (insertCombineGo m tl).map (·.2) := rfl
      rw [hmap_out, List.nodup_cons]
      constructor
      · intro hcontra
        rcases insertCombineGo_mem m tl e hcontra with h1 | h2
        · exact he_notin h1
        · exact hne h2
      · exact ih'

theorem insertCombine_noZeros (m : Mono) (q : Poly)
    (hq : hasNoZeros q) : hasNoZeros (insertCombine m q) := by
  unfold insertCombine
  by_cases hm : m.1 = 0
  · simp [hm]
    exact hq
  · simp [hm]
    by_cases hmem : m.2 ∈ q.map (·.2)
    · simp [hmem]
      exact insertCombineGo_noZeros m q hm hq
    · simp [hmem]
      unfold hasNoZeros at *
      intro x hx
      simp at hx
      rcases hx with rfl | hmem'
      · exact hm
      · exact hq x hmem'

theorem insertCombine_nodup (m : Mono) (q : Poly)
    (hq : hasNoDups q) : hasNoDups (insertCombine m q) := by
  unfold hasNoDups insertCombine
  by_cases hm : m.1 = 0
  · rw [if_pos hm]
    exact hq
  · rw [if_neg hm]
    by_cases hmem : m.2 ∈ q.map (·.2)
    · rw [if_pos hmem]
      exact insertCombineGo_nodup m q hq
    · rw [if_neg hmem]
      have hmap : (((m :: q).map (·.2))) = m.2 :: q.map (·.2) := rfl
      rw [hmap]
      exact List.nodup_cons.mpr ⟨hmem, hq⟩

theorem combine_noZeros (p : Poly) : hasNoZeros (combine p) := by
  unfold hasNoZeros
  induction p with
  | nil =>
    intro x hx
    simp [combine] at hx
  | cons m rest ih =>
    unfold combine
    exact insertCombine_noZeros m (combine rest) ih

theorem combine_nodup (p : Poly) : hasNoDups (combine p) := by
  unfold hasNoDups
  induction p with
  | nil => simp [combine]
  | cons m rest ih =>
    unfold combine
    exact insertCombine_nodup m (combine rest) ih

/-- `combine` is identity on already-normalized (no zeros/dups) inputs. -/
theorem combine_fixed (q : Poly) (hz : hasNoZeros q) (hd : hasNoDups q) :
    combine q = q := by
  induction q with
  | nil => simp [combine]
  | cons m rest ih =>
    have hz_rest : hasNoZeros rest := by
      unfold hasNoZeros at *
      intro y hy
      exact hz y (List.mem_cons_of_mem m hy)
    have hd_rest : hasNoDups rest := by
      unfold hasNoDups at *
      have hmap : (((m :: rest).map (·.2))) = m.2 :: rest.map (·.2) := rfl
      rw [hmap, List.nodup_cons] at hd
      exact hd.2
    have ih' := ih hz_rest hd_rest
    have hm_ne : m.1 ≠ 0 := hz m List.mem_cons_self
    have hnotin : m.2 ∉ rest.map (·.2) := by
      unfold hasNoDups at hd
      have hmap : (((m :: rest).map (·.2))) = m.2 :: rest.map (·.2) := rfl
      rw [hmap, List.nodup_cons] at hd
      exact hd.1
    simp only [combine, ih']
    unfold insertCombine
    simp [hm_ne, hnotin]

/-- Sort by exponent lex order. -/
def sortPoly (p : Poly) : Poly := p.mergeSort monoLE

theorem sortPoly_pairwise (p : Poly) :
    List.Pairwise (fun a b => monoLE a b = true) (sortPoly p) :=
  List.pairwise_mergeSort monoLE_trans monoLE_total p

theorem sortPoly_perm (p : Poly) : List.Perm (sortPoly p) p :=
  List.mergeSort_perm p monoLE

theorem sortPoly_noZeros (p : Poly) (h : hasNoZeros p) : hasNoZeros (sortPoly p) := by
  unfold hasNoZeros at *
  intro m hm
  have hperm := sortPoly_perm p
  have hmem : m ∈ p := (List.Perm.mem_iff hperm).mp hm
  exact h m hmem

theorem sortPoly_nodup (p : Poly) (h : hasNoDups p) : hasNoDups (sortPoly p) := by
  unfold hasNoDups at *
  have hperm := sortPoly_perm p
  have hmap_perm : List.Perm ((sortPoly p).map (·.2)) (p.map (·.2)) :=
    List.Perm.map (·.2) hperm
  exact List.Nodup.perm h hmap_perm.symm

/-- Full normalization: combine + drop zeros + sort. -/
def normalize (p : Poly) : Poly := sortPoly (combine p)

theorem normalize_nil : normalize [] = [] := by
  exact List.Perm.eq_nil (sortPoly_perm [])

theorem normalize_noZeros (p : Poly) : hasNoZeros (normalize p) :=
  sortPoly_noZeros (combine p) (combine_noZeros p)

theorem normalize_nodup (p : Poly) : hasNoDups (normalize p) :=
  sortPoly_nodup (combine p) (combine_nodup p)

theorem sortPoly_idem (p : Poly) : sortPoly (sortPoly p) = sortPoly p := by
  unfold sortPoly
  exact List.mergeSort_of_pairwise (sortPoly_pairwise p)

/-- Normalization is idempotent. -/
theorem normalize_idem (p : Poly) : normalize (normalize p) = normalize p := by
  unfold normalize
  have h1 : hasNoZeros (sortPoly (combine p)) :=
    sortPoly_noZeros (combine p) (combine_noZeros p)
  have h2 : hasNoDups (sortPoly (combine p)) :=
    sortPoly_nodup (combine p) (combine_nodup p)
  have hcomb : combine (sortPoly (combine p)) = sortPoly (combine p) :=
    combine_fixed _ h1 h2
  rw [hcomb]
  exact sortPoly_idem (combine p)

/-- Addition: concat + normalize. -/
def polyAdd (p q : Poly) : Poly := normalize (p ++ q)

theorem polyAdd_def (p q : Poly) : polyAdd p q = normalize (p ++ q) := rfl

/-- Multiplication: distribute monomial mul + normalize. -/
def polyMul (p q : Poly) : Poly :=
  normalize (p.flatMap (fun m1 => q.map (fun m2 => mulMono m1 m2)))

theorem polyMul_def (p q : Poly) :
    polyMul p q = normalize (p.flatMap (fun m1 => q.map (fun m2 => mulMono m1 m2))) := rfl

theorem polyMul_single_single (c1 c2 : Rat) (e1 e2 : Exp) :
    polyMul [(c1, e1)] [(c2, e2)] = normalize [(c1 * c2, addExp e1 e2)] := rfl

/-- Power by repeated multiplication. `p^0 = 1` (one poly). -/
def polyPow : Poly → Nat → Poly
  | _, 0 => [(1, zeroExp)]
  | p, n+1 => polyMul p (polyPow p n)

theorem polyPow_zero (p : Poly) : polyPow p 0 = [(1, zeroExp)] := rfl

theorem polyPow_succ (p : Poly) (n : Nat) : polyPow p (n+1) = polyMul p (polyPow p n) := rfl

/-- Partial derivative w.r.t. variable `i`, then normalize. -/
def partialDeriv (i : Fin 6) (p : Poly) : Poly :=
  normalize (p.filterMap (derivMono i))

theorem partialDeriv_def (i : Fin 6) (p : Poly) :
    partialDeriv i p = normalize (p.filterMap (derivMono i)) := rfl

theorem partialDeriv_nil (i : Fin 6) : partialDeriv i [] = [] := normalize_nil
