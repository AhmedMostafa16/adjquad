import AdjQuad.Poly
import AdjQuad.Deriv

/-
Computational lemmas for the N=5 adjoint-quadratic formalization (Batch B).

All goals are proved by computation over the polynomial API of
`AdjQuad.Poly` / `AdjQuad.Deriv` (mostly `native_decide`; every stated
equality is a finite, closed computation over `Rat`/`List`). Zero `sorry`.

Parts:
  0. Missing poly constructors: `polyNeg`, `polySub` (needed for signs in the determinant).
  1. Invariance trio: `D J1 = 0`, `D J2 = 0`, `D F0 = 0`.
  2. Weighted homogeneity: `weightedDegree` of J1=6, J2=4, F0=14, plus
     per-term uniform-weight checks (each generator is exactly one weight).
  3. Jacobian minor: the 5x5 matrix of `partialDeriv` entries of
     (p, q, J1, J2, F0) along variables (a0, a1, a2, a4, a5) has determinant
     exactly the monomial `4*a4^3*a5^5` (hence nonzero). A second minor along
     (a1, a2, a3, a4, a5) equals `-4*a1*a2*a4^2*a5^4`.
     The determinant is given both as the full 120-term signed permutation sum
     (`detM5`) and as a hand-written Laplace/cofactor chain exploiting the
     triangular-ish sparsity (`detM5chain`), with the two shown computationally
     equal; the main theorem is derived through the chain.
  4. Coprime: `G0 mod p != 0` and `G0 mod q != 0`, via the substitution helper
     `modVar` (set one variable to 0). Since `p = a4` and `q = a5` are monomials,
     `modVar i G0 != []` is exactly the monomial division test `var ∤ G0`
     (equiv. `gcd(G0, var) = 1`, the variable being prime).
-/

------------------------------------------------------------
-- 0. Extra constructors
------------------------------------------------------------

/-- Unary minus on polynomials -/
def polyNeg (p : Poly) : Poly := normalize (p.map (fun m => (-m.1, m.2)))

/-- Difference `p - q` -/
def polySub (p q : Poly) : Poly := polyAdd p (polyNeg q)

------------------------------------------------------------
-- 1. Invariance trio: D J1 = D J2 = D F0 = 0
------------------------------------------------------------

theorem D_J1_zero : D J1 = [] := by native_decide

theorem D_J2_zero : D J2 = [] := by native_decide

theorem D_F0_zero : D F0 = [] := by native_decide

------------------------------------------------------------
-- 2. Weighted degrees and per-term uniform weights
------------------------------------------------------------

theorem weightedDegree_J1 : weightedDegree J1 = 6 := by native_decide

theorem weightedDegree_J2 : weightedDegree J2 = 4 := by native_decide

theorem weightedDegree_F0 : weightedDegree F0 = 14 := by native_decide

/-- G0 = F0 - c*a0 is also weighted-homogeneous of degree 14. -/
theorem weightedDegree_G0 : weightedDegree G0 = 14 := by native_decide

/-- The factor c = p^2 q^4 has weight 6. -/
theorem weightedDegree_c : weightedDegree c = 6 := by native_decide

/-- Every term of J1 has weight exactly 6, so `weightedDegree J1 = 6` is a
uniform weight, not a max of different weights -/
theorem J1_terms_have_weight_6 : ∀ e ∈ J1.map (·.2), expWeight e = 6 := by native_decide

/-- Every term of J2 has weight exactly 4 -/
theorem J2_terms_have_weight_4 : ∀ e ∈ J2.map (·.2), expWeight e = 4 := by native_decide

/-- Every term of F0 has weight exactly 14 -/
theorem F0_terms_have_weight_14 : ∀ e ∈ F0.map (·.2), expWeight e = 14 := by native_decide

/-- Every term of G0 has weight exactly 14 -/
theorem G0_terms_have_weight_14 : ∀ e ∈ G0.map (·.2), expWeight e = 14 := by native_decide

/-- Every term of c has weight exactly 6 -/
theorem c_term_has_weight_6 : ∀ e ∈ c.map (·.2), expWeight e = 6 := by native_decide

------------------------------------------------------------
-- 3. Jacobian minor (columns a0, a1, a2, a4, a5)
------------------------------------------------------------

/-- Rows of the Jacobian stack: (p, q, J1, J2, F0). -/
def jacRow5 (i : Nat) : Poly :=
  match i with
  | 0 => p
  | 1 => q
  | 2 => J1
  | 3 => J2
  | 4 => F0
  | _ => []

/-- Chosen columns: variables (a0, a1, a2, a4, a5), i.e. Fin 6 indices 0,1,2,4,5. -/
def jacCol5 (j : Nat) : Fin 6 :=
  match j with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨4, by decide⟩
  | 4 => ⟨5, by decide⟩
  | _ => ⟨0, by decide⟩

/-- Entry `M5 i j` = ∂(jacRow5 i)/∂var(jacCol5 j), derived via `partialDeriv`
(the only way matrix entries are obtained in this file). -/
def M5 (i j : Nat) : Poly := partialDeriv (jacCol5 j) (jacRow5 i)

/-- Alternative column choice (a1, a2, a3, a4, a5) for the second minor. -/
def jacCol5b (j : Nat) : Fin 6 :=
  match j with
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨2, by decide⟩
  | 2 => ⟨3, by decide⟩
  | 3 => ⟨4, by decide⟩
  | 4 => ⟨5, by decide⟩
  | _ => ⟨0, by decide⟩

def M5b (i j : Nat) : Poly := partialDeriv (jacCol5b j) (jacRow5 i)

/-- nth element of a list, 0 if out of range (every permutation below has length 5). -/
def nthOf (l : List Nat) (n : Nat) : Nat :=
  match n, l with
  | 0, x :: _ => x
  | n + 1, _ :: t => nthOf t n
  | _, [] => 0

/-- Number of inversions of a permutation of 0..4. -/
def invCount5 (σ : List Nat) : Nat :=
  (List.range 5).foldl (fun acc i =>
    acc + (List.range 5).foldl (fun acc2 j =>
      acc2 + if i < j ∧ nthOf σ i > nthOf σ j then 1 else 0) 0) 0

/-- Sign of a permutation, as a rational scalar. -/
def sgn5 (σ : List Nat) : Rat := if invCount5 σ % 2 = 0 then (1 : Rat) else (-1 : Rat)

/-- The permutation term for σ: product over i of M5(i, σ(i)). -/
def permTerm5 (σ : List Nat) : Poly :=
  (List.range 5).foldl (fun acc i => polyMul acc (M5 i (nthOf σ i))) [(1, zeroExp)]

def permTerm5b (σ : List Nat) : Poly :=
  (List.range 5).foldl (fun acc i => polyMul acc (M5b i (nthOf σ i))) [(1, zeroExp)]

/-
 * Insert `h` into list `r` in every possible position.
 -/
def inserts (h : Nat) (r : List Nat) : List (List Nat) :=
  match r with
  | [] => [[h]]
  | a :: t => (h :: a :: t) :: (inserts h t).map (a :: ·)

/-
 * All permutations of a list (recursive; gives 120 lists for `[0,1,2,3,4]`).
 -/
def perms (l : List Nat) : List (List Nat) :=
  match l with
  | [] => [[]]
  | h :: t => (perms t).flatMap (inserts h)

/-
 * **detM5**: the 5x5 determinant as the full signed 120-term permutation sum
 * `Σ_σ sign(σ) ∏_i M5(i, σ(i))`, folded over all 120 permutations of
 * `[0,1,2,3,4]`; each term is normalized via `polyMul`/`polyAdd`.
 -/
def detM5 : Poly :=
  (perms [0,1,2,3,4]).foldl
    (fun acc σ => polyAdd acc (polyMul [((sgn5 σ), zeroExp)] (permTerm5 σ))) []

def detM5b : Poly :=
  (perms [0,1,2,3,4]).foldl
    (fun acc σ => polyAdd acc (polyMul [((sgn5 σ), zeroExp)] (permTerm5b σ))) []

/-- Cofactor matrix K4: rows (q, J1, J2, F0), columns (a0, a1, a2, a5). -/
def cofRow4 (i : Nat) : Poly :=
  match i with
  | 0 => q
  | 1 => J1
  | 2 => J2
  | 3 => F0
  | _ => []

def cofCol4 (j : Nat) : Fin 6 :=
  match j with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨5, by decide⟩
  | _ => ⟨0, by decide⟩

def K4 (i j : Nat) : Poly := partialDeriv (cofCol4 j) (cofRow4 i)

/-- Cofactor matrix L3: rows (J1, J2, F0), columns (a0, a1, a2). -/
def cofRow3 (i : Nat) : Poly :=
  match i with
  | 0 => J1
  | 1 => J2
  | 2 => F0
  | _ => []

def cofCol3 (j : Nat) : Fin 6 :=
  match j with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def L3 (i j : Nat) : Poly := partialDeriv (cofCol3 j) (cofRow3 i)

/-- 2x2 corner X2: rows (J1, J2), columns (a1, a2). -/
def cofRow2 (i : Nat) : Poly :=
  match i with
  | 0 => J1
  | 1 => J2
  | _ => []

def cofCol2 (j : Nat) : Fin 6 :=
  match j with
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def X2 (i j : Nat) : Poly := partialDeriv (cofCol2 j) (cofRow2 i)

/-
 * Hand-written Laplace chain exploiting the sparsity (see entry lemmas below):
 *
 *   det M5 = - M5[0,3] · ( - K4[0,3] · ( L3[2,0] · (X2[0,0]·X2[1,1] - X2[0,1]·X2[1,0]) ) )
 *
 * Signs: (-1)^(0+3) for the p-row (only ∂a4 is nonzero), then (-1)^(0+3)
 * for the q-row (only ∂a5 is nonzero), then (-1)^(2+0) = +1 for the a0-column
 * of L3 (only ∂a0 F0 = a4^2 a5^4 is nonzero), then the standard 2x2 expansion.
 -/
def detX2 : Poly := polySub (polyMul (X2 0 0) (X2 1 1)) (polyMul (X2 0 1) (X2 1 0))

def detL3 : Poly := polyMul (L3 2 0) detX2

def detK4 : Poly := polyMul (polyNeg (K4 0 3)) detL3

def detM5chain : Poly := polyMul (polyNeg (M5 0 3)) detK4

-------------------------------------------------------------------
-- 3a. Matrix entries (finite checks of the derived partials)
-------------------------------------------------------------------

/-- p = a4: only ∂a4 p is 1; all other entries of the p-row vanish. -/
theorem M5_03_is_one : M5 0 3 = [(1, zeroExp)] := by native_decide

theorem M5_00_zero : M5 0 0 = [] := by native_decide

theorem M5_01_zero : M5 0 1 = [] := by native_decide

theorem M5_02_zero : M5 0 2 = [] := by native_decide

theorem M5_04_zero : M5 0 4 = [] := by native_decide

/-- q = a5: only ∂a5 q is 1; the q-row of K4 (columns a0,a1,a2,a5) has a single 1. -/
theorem K4_03_is_one : K4 0 3 = [(1, zeroExp)] := by native_decide

theorem K4_00_zero : K4 0 0 = [] := by native_decide

theorem K4_01_zero : K4 0 1 = [] := by native_decide

theorem K4_02_zero : K4 0 2 = [] := by native_decide

/-- J1, J2 have no a0-term: the a0-column of L3 is zero in rows J1, J2. -/
theorem L3_00_zero : L3 0 0 = [] := by native_decide

theorem L3_10_zero : L3 1 0 = [] := by native_decide

/-- ∂a0 F0 = a4^2 a5^4 (the only nonzero entry of the a0-column of L3). -/
theorem L3_20 : L3 2 0 = normalize [(1, [0,0,0,0,2,4])] := by native_decide

/-- X2 = [[∂a1 J1, ∂a2 J1], [∂a1 J2, ∂a2 J2]] = [[2a4, -2a2], [0, 2a5]]. -/
theorem X2_00 : X2 0 0 = [(2, [0,0,0,0,1,0])] := by native_decide

theorem X2_01 : X2 0 1 = [(-2, [0,0,1,0,0,0])] := by native_decide

theorem X2_10_zero : X2 1 0 = [] := by native_decide

theorem X2_11 : X2 1 1 = [(2, [0,0,0,0,0,1])] := by native_decide

/-
 * F0-row entries (full documentation of the derived matrix row):
 * M5 4 0 = ∂a0 F0 = a4^2 a5^4.
 * M5 4 1 = ∂a1 F0 = -a2 a3 a4 a5^3 + (1/3) a3^3 a4 a5^2.
 * M5 4 2 = ∂a2 F0 = -a1 a3 a4 a5^3 + (2/3) a2 a3^3 a5^2 - (1/5) a3^5 a5.
 * M5 4 3 = ∂a4 F0 = 2 a0 a4 a5^4 - a1 a2 a3 a5^3 + (1/3) a1 a3^3 a5^2.
 * M5 4 4 = ∂a5 F0 = 4 a0 a4^2 a5^3 - 3 a1 a2 a3 a4 a5^2
 *                   + (2/3) a1 a3^3 a4 a5 + (2/3) a2^2 a3^3 a5 - (1/5) a2 a3^5.
 -/
theorem M5_40 : M5 4 0 = normalize [(1, [0,0,0,0,2,4])] := by native_decide

theorem M5_41 : M5 4 1 = normalize
    [(-1, [0,0,1,1,1,3]), ((1 : Rat)/3, [0,0,0,3,1,2])] := by native_decide

theorem M5_42 : M5 4 2 = normalize
    [(-1, [0,1,0,1,1,3]), ((2 : Rat)/3, [0,0,1,3,0,2]),
     ((-1 : Rat)/5, [0,0,0,5,0,1])] := by native_decide

theorem M5_43 : M5 4 3 = normalize
    [(2, [1,0,0,0,1,4]), (-1, [0,1,1,1,0,3]), ((1 : Rat)/3, [0,1,0,3,0,2])] := by native_decide

theorem M5_44 : M5 4 4 = normalize
    [(4, [1,0,0,0,2,3]), (-3, [0,1,1,1,1,2]), ((2 : Rat)/3, [0,1,0,3,1,1]),
     ((2 : Rat)/3, [0,0,2,3,0,1]), ((-1 : Rat)/5, [0,0,1,5,0,0])] := by native_decide

-------------------------------------------------------------------
-- 3b. The minor itself
-------------------------------------------------------------------

/-- The hand-written Laplace chain evaluates to the monomial 4 a4^3 a5^5. -/
theorem laplace_minor_value : detM5chain = [(4, [0,0,0,0,3,5])] := by native_decide

/-- The Laplace chain agrees with the full 120-term permutation determinant
(both sides compute to the same normal form, so the sparsity exploitation
is verified exact, not assumed). -/
theorem laplace_chain_is_detM5 : detM5chain = detM5 := by native_decide

/-- **Main result.** The 5x5 Jacobian minor of (p, q, J1, J2, F0) along
(a0, a1, a2, a4, a5) is exactly the nonzero monomial 4 a4^3 a5^5. -/
theorem jacobian_minor : detM5 = [(4, [0,0,0,0,3,5])] := by
  rw [← laplace_chain_is_detM5]
  exact laplace_minor_value

theorem jacobian_minor_nonzero : detM5 ≠ [] := by native_decide

/-
 * Second choice of columns (a1,a2,a3,a4,a5): the minor is the nonzero
 * monomial -4 a1 a2 a4^2 a5^4 (computed the same way, full permutation sum).
 -/
theorem jacobian_minor_b : detM5b = [(-4, [0,1,1,0,2,4])] := by native_decide

theorem jacobian_minor_b_nonzero : detM5b ≠ [] := by native_decide

------------------------------------------------------------
-- 4. Coprime: G0 mod p != 0, G0 mod q != 0
------------------------------------------------------------

/-
 * `modVar i F` = F with variable `a_i` set to 0 (keep exactly the terms whose
 * exponent in position `i` is 0). Since `p = a4` and `q = a5` are single
 * monomials, `modVar 4 G0 ≠ []` is the monomial division test for
 * `a4 ∤ G0` (equivalently `gcd(G0, p) = 1`, `a4` being prime), and
 * likewise `modVar 5 G0 ≠ []` tests `a5 ∤ G0`.
 -/
def modVar (i : Fin 6) (F : Poly) : Poly :=
  normalize (F.filter (fun m => m.2[i.val]? = some 0))

/-- Sanity: p mod p = 0 (a monomial vanishes when its own variable is set to 0). -/
theorem p_mod_p_zero : modVar ⟨4, by decide⟩ p = [] := by native_decide

/-- Sanity: q mod q = 0. -/
theorem q_mod_q_zero : modVar ⟨5, by decide⟩ q = [] := by native_decide

/-- G0 with a4 := 0: exactly the three terms of G0 not containing a4 survive
(a2^2 a3^3 a5^2, a2 a3^5 a5, a3^7, with coeffs 1/3, -1/5, 1/35). -/
theorem G0_mod_p_value : modVar ⟨4, by decide⟩ G0 = normalize
    [((1 : Rat)/3, [0,0,2,3,0,2]), ((-1 : Rat)/5, [0,0,1,5,0,1]),
     ((1 : Rat)/35, [0,0,0,7,0,0])] := by native_decide

/-- G0 mod p ≠ 0: a4 does not divide G0, hence G0 and p are coprime. -/
theorem G0_mod_p_neq_zero : modVar ⟨4, by decide⟩ G0 ≠ [] := by native_decide

/-
 * G0 with a5 := 0: only the (1/35) a3^7 term survives.
 * Note: that single term has weight 14 (7·2), consistent with
 * `weightedDegree_G0` and the weighted-homogeneity of G0.
 -/
theorem G0_mod_q_value : modVar ⟨5, by decide⟩ G0 =
    normalize [((1 : Rat)/35, [0,0,0,7,0,0])] := by native_decide

/-- G0 mod q ≠ 0: a5 does not divide G0, hence G0 and q are coprime. -/
theorem G0_mod_q_neq_zero : modVar ⟨5, by decide⟩ G0 ≠ [] := by native_decide