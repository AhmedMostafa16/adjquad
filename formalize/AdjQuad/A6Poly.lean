/-
Minimal certified multivariate polynomial library over Rat in 7 variables,
for the N=6 A-level (`A6 = k[a0..a6]`).

Namespace `A6` (no imports from `AdjQuad`: every name below would clash
with the length-6 API, so all definitions and the lemmas the `inR6`
mirror needs are re-declared here with 6 -> 7 adaptations:
`varExp` replicates 7, `weights` gains the `13` for `a0`,
`derivMono`/`partialDeriv` use `Fin 7`, length facts conclude `7`).
Proof bodies otherwise follow `AdjQuad.Poly` verbatim. Only the chain
needed downstream is included: `normalize_mem_exp` (via
`sortPoly_perm`, `combine_mem`, `insertCombine_mem`,
`insertCombineGo_mem`), the length/arithmetic lemmas
(`zipWith_len_aux`, `addExp_len7`, `a0degAddExpLen6`,
`foldl_add_init`, `foldl_zip_plus_aux`, `foldl_zip_plus`,
`zipWith_mul_plus_aux`, `zipWith_mul_plus`,
`expWeightAddExpLen7`), and the `rfl` unfolding lemmas
`polyAdd_def`, `polyMul_def`, `partialDeriv_def`.

Core-Lean only.
-/

namespace A6

abbrev Exp := List Nat
abbrev Mono := Rat × Exp
abbrev Poly := List Mono

/-- Zero exponent vector (length 7). -/
def zeroExp : Exp := [0,0,0,0,0,0,0]

/-- Fibonacci weights `[13,8,5,3,2,1,1]` for `a0..a6`. -/
def weights : List Nat := [13,8,5,3,2,1,1]

/-- Single-variable exponent: 1 at position `i`, 0 elsewhere (length 7). -/
def varExp (i : Nat) : Exp := (List.replicate 7 0).set i 1

/-- Pointwise addition of exponent vectors (monomial multiplication). -/
def addExp (e1 e2 : Exp) : Exp := List.zipWith (· + ·) e1 e2

/-- Weighted weight of a single exponent vector. -/
def expWeight (e : Exp) : Nat :=
  ((weights.zipWith (· * ·) e).foldl (· + ·) 0)

/-- Weighted degree of a poly: max over terms, 0 for empty. -/
def weightedDegree (p : Poly) : Nat :=
  p.foldl (fun acc m => Nat.max acc (expWeight m.2)) 0

/-- Monomial multiplication: multiply coeffs, add exps. -/
def mulMono (m1 m2 : Mono) : Mono := (m1.1 * m2.1, addExp m1.2 m2.2)

/-- Monomial partial derivative w.r.t. variable `i : Fin 7`.
Returns `none` when the term vanishes (exponent 0 or malformed). -/
def derivMono (i : Fin 7) (m : Mono) : Option Mono :=
  match m.2[i.val]? with
  | none => none
  | some 0 => none
  | some (n+1) =>
    let c' := m.1 * ((n+1 : Nat) : Rat)
    let e' := m.2.set i.val n
    some (c', e')

/-- Lexicographic comparison on monomials by exponent vector (Bool). -/
def monoLE (a b : Mono) : Bool := decide (a.2 ≤ b.2)

/-- Combine helper: scan for equal exp, add coeffs, drop zeros created. -/
def insertCombineGo (m : Mono) : Poly → Poly
  | [] => [m]
  | (c, e) :: rest =>
    if e = m.2 then
      if c + m.1 = 0 then rest else (c + m.1, e) :: rest
    else (c, e) :: insertCombineGo m rest

/-- Order-preserving insert with combining + zero-dropping. -/
def insertCombine (m : Mono) (q : Poly) : Poly :=
  if m.1 = 0 then q
  else if m.2 ∈ q.map (·.2) then insertCombineGo m q else m :: q

/-- Combine like terms + drop zeros (order-preserving, no sorting). -/
def combine : Poly → Poly
  | [] => []
  | m :: rest => insertCombine m (combine rest)

/-- Sort by exponent lex order. -/
def sortPoly (p : Poly) : Poly := p.mergeSort monoLE

theorem sortPoly_perm (p : Poly) : List.Perm (sortPoly p) p :=
  List.mergeSort_perm p monoLE

/-- Full normalization: combine + drop zeros + sort. -/
def normalize (p : Poly) : Poly := sortPoly (combine p)

/-- Addition: concat + normalize. -/
def polyAdd (p q : Poly) : Poly := normalize (p ++ q)

theorem polyAdd_def (p q : Poly) : polyAdd p q = normalize (p ++ q) := rfl

/-- Multiplication: distribute monomial mul + normalize. -/
def polyMul (p q : Poly) : Poly :=
  normalize (p.flatMap (fun m1 => q.map (fun m2 => mulMono m1 m2)))

theorem polyMul_def (p q : Poly) :
    polyMul p q = normalize (p.flatMap (fun m1 => q.map (fun m2 => mulMono m1 m2))) := rfl

/-- Partial derivative w.r.t. variable `i`, then normalize. -/
def partialDeriv (i : Fin 7) (p : Poly) : Poly :=
  normalize (p.filterMap (derivMono i))

theorem partialDeriv_def (i : Fin 7) (p : Poly) :
    partialDeriv i p = normalize (p.filterMap (derivMono i)) := rfl

/-- a0-exponent of an exponent vector (0 if empty); doubles as the
    N=6 `a_0`-degree (head position). -/
def a0deg (e : Exp) : Nat :=
  match e with
  | [] => 0
  | x :: _ => x

/-- a0-degree of a monomial. -/
def a0degMono (m : Mono) : Nat := a0deg m.2

theorem weights_len7 : weights.length = 7 := by native_decide

/-- `k.succ = 0` is impossible. -/
theorem nat_succ_not_zero {k : Nat} (h : k.succ = 0) : False :=
  Nat.succ_ne_zero k h

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

/-- `addExp` of two length-7 exponent vectors is length-7. -/
theorem addExp_len7 (e1 e2 : Exp) (h1 : e1.length = 7) (h2 : e2.length = 7) :
    (addExp e1 e2).length = 7 :=
  zipWith_len_aux _ _ e1 e2 h1 h2

/-- a0-degree of the product of two length-7 exponent vectors adds. -/
theorem a0degAddExpLen7 (e1 e2 : Exp) (h1 : e1.length = 7) (h2 : e2.length = 7) :
    a0deg (addExp e1 e2) = a0deg e1 + a0deg e2 := by
  cases e1 with
  | nil =>
    exfalso
    rw [List.length_nil] at h1
    exact (by decide : 0 ≠ 7) h1
  | cons x1 t1 =>
    cases e2 with
    | nil =>
      exfalso
      rw [List.length_nil] at h2
      exact (by decide : 0 ≠ 7) h2
    | cons x2 t2 =>
      simp [a0deg, addExp, List.zipWith]

/-- For a list and any start `k`, folding `(·+·)` from `k` equals
    `k +` folding from `0`. -/
theorem foldl_add_init (l : List Nat) (k : Nat) :
    l.foldl (· + ·) k = k + l.foldl (· + ·) 0 := by
  induction l generalizing k with
  | nil =>
    simp [List.foldl, Nat.add_zero]
  | cons a t ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (k + a), ih a]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- For equal-length lists (common length `n`), folding `(·+·)` from `0`
    over the pointwise zip equals the sum of the individual folds. -/
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

/-- Corollary for two equal-length lists. -/
theorem foldl_zip_plus (L M : List Nat) (hLM : L.length = M.length) :
    (L.zipWith (· + ·) M).foldl (· + ·) 0 = L.foldl (· + ·) 0 + M.foldl (· + ·) 0 := by
  exact foldl_zip_plus_aux (L.length) L M (by rfl) hLM.symm

/-- Pointwise: `w *.< (e1 +. e2) = (w *.< e1) +. (w *.< e2)`. -/
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

/-- Corollary for three equal-length lists. -/
theorem zipWith_mul_plus (w e1 e2 : List Nat)
    (h1 : w.length = e1.length) (h2 : e1.length = e2.length) :
    w.zipWith (· * ·) (e1.zipWith (· + ·) e2) =
      (w.zipWith (· * ·) e1).zipWith (· + ·) (w.zipWith (· * ·) e2) := by
  exact zipWith_mul_plus_aux (e1.length) w e1 e2 h1 (by rfl) h2.symm

/-- Weighted weight splits additively over products of length-7 vectors. -/
theorem expWeightAddExpLen7 (e1 e2 : Exp) (h1 : e1.length = 7) (h2 : e2.length = 7) :
    expWeight (addExp e1 e2) = expWeight e1 + expWeight e2 := by
  unfold expWeight addExp
  rw [zipWith_mul_plus weights e1 e2 (by simp [weights_len7, h1]) (by simp [h1, h2])]
  have hL : (weights.zipWith (· * ·) e1).length = (weights.zipWith (· * ·) e2).length := by
    have l1 : (weights.zipWith (· * ·) e1).length = 7 :=
      zipWith_len_aux _ _ weights e1 weights_len7 h1
    have l2 : (weights.zipWith (· * ·) e2).length = 7 :=
      zipWith_len_aux _ _ weights e2 weights_len7 h2
    rw [l1, l2]
  rw [foldl_zip_plus _ _ hL]

/-- `insertCombineGo` adds at most the exponent vector of the inserted monomial. -/
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

/-- `normalize` never introduces a new exponent vector. -/
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

end A6
