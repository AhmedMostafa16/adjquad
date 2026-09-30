import AdjQuad.Deriv

/-
N=5 counterexample to `A_5^D = k[p, q, J1, J2, F0]`.

`H`: 17 terms, content 1, uniform Fibonacci weight 24, max `a0`-degree 2,
`D(H) = 0` (by computation below), hence `H ∈ A_5^D`. And
`H ∉ K[F0]` at weight 24: every monomial of `K[F0]_24` has `a0`-degree
≤ 1 (only `F0` carries `a0`, in degree 1, and `F0^2` already weighs
28 > 24), while `H` has the `a0^2` term `11025 a0^2 a4^4 a5^4`;
equivalently the 212 generator monomials of `K[F0]_24` span rank 212
and `H` is independent of them (rank 213). So `A_5^D ⊋ K[F0]` and the
five-generator Hilbert series fails from weight 24
(`dim ker(D|V_24) = 213` vs 212).

Standalone module: `lake build AdjQuad.Counterexample` (not imported by
the root). Core-Lean only.
-/

/-- The counterexample `H` (17 terms, content 1, weight 24). -/
def H : Poly := normalize
  [((11025 : Rat), [2,0,0,0,4,4]),
   ((-22050 : Rat), [1,1,1,1,3,3]),
   ((7350 : Rat), [1,1,0,3,3,2]),
   ((7350 : Rat), [1,0,2,3,2,2]),
   ((-4410 : Rat), [1,0,1,5,2,1]),
   ((630 : Rat), [1,0,0,7,2,0]),
   ((11025 : Rat), [0,2,2,2,2,2]),
   ((-7350 : Rat), [0,2,1,4,2,1]),
   ((1225 : Rat), [0,2,0,6,2,0]),
   ((6720 : Rat), [0,1,5,0,1,3]),
   ((-16800 : Rat), [0,1,4,2,1,2]),
   ((9450 : Rat), [0,1,3,4,1,1]),
   ((-1540 : Rat), [0,1,2,6,1,0]),
   ((-2208 : Rat), [0,0,7,0,0,3]),
   ((4368 : Rat), [0,0,6,2,0,2]),
   ((-2352 : Rat), [0,0,5,4,0,1]),
   ((385 : Rat), [0,0,4,6,0,0])]

/-- `H` is invariant: `D(H) = 0`, proved by computation. -/
theorem H_D_zero : D H = [] := by native_decide

/-- `H` is weighted-homogeneous of Fibonacci weight 24. -/
theorem weightedDegree_H : weightedDegree H = 24 := by native_decide

/-- Every term of `H` has weight exactly 24 (uniform weight). -/
theorem H_terms_have_weight_24 : ∀ e ∈ H.map (·.2), expWeight e = 24 := by native_decide

/-- `H` has an `a0^2` term (`11025 a0^2 a4^4 a5^4`), hence `a0`-degree 2;
    no weight-24 monomial of `K[F0]` can have `a0`-degree 2, so
    `H ∉ K[F0]` by the structural argument in the header comment. -/
theorem H_has_a0_sq : (11025, [2,0,0,0,4,4]) ∈ H := by native_decide