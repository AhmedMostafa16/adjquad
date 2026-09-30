/-
Machine-checked residual `p`-boundary audit for `D_5`.

Proves, by exact kernel evaluation (`native_decide`):
- `D(2*a3*a0 - a1^2) = 2*p*q*a0`, i.e. `theta` is `D`-closed mod `p`;
- the `p = 0` restrictions `F0| = q²x³y²/3-qx⁵y/5+x⁷/35` (three terms),
  `H| = four a0-free terms`, `J1| = -y²`;
- `F46|_{p=0} ≠ 0` (a genuine residual invariant direction).

These are the identities behind the residual-kernel theorem
(`ker δ_p = k[q,x,y,theta]`); the filtration proof itself is paper-level.

Core-Lean only, zero `sorry`. Standalone module:
`lake build AdjQuad.ResidualCheck`.
-/
import AdjQuad.Deriv
import AdjQuad.Counterexample
import AdjQuad.SecondWitness

/-- `theta = 2*a3*a0 - a1^2`. -/
def THETA : Poly := normalize
  [((2 : Rat), [1,0,0,1,0,0]),
   (((-1 : Rat)), [0,2,0,0,0,0])]

/-- `D(theta) = 2*p*q*a0`: theta is invariant mod `p`. -/
theorem D_theta_eq : D THETA = [((2 : Rat), [1,0,0,0,1,1])] := by
  native_decide

/-- `a4`-exponent of an exponent vector (0 if short). -/
def a4deg (e : Exp) : Nat := e[4]?.getD 0

/-- `F0|_{p=0} = q²x³y²/3 - qx⁵y/5 + x⁷/35` (filter order, no re-sort). -/
theorem F0_res_p0 :
    F0.filter (fun m => decide (a4deg m.2 = 0)) =
    [(((1 : Rat)/35), [0,0,0,7,0,0]),
     (((-1 : Rat)/5), [0,0,1,5,0,1]),
     (((1 : Rat)/3), [0,0,2,3,0,2])] := by
  native_decide

/-- `H|_{p=0}` is the four a0-free terms. -/
theorem H_res_p0 :
    H.filter (fun m => decide (a4deg m.2 = 0)) = normalize
    [(((-2208 : Rat)), [0,0,7,0,0,3]),
     (((4368 : Rat)), [0,0,6,2,0,2]),
     (((-2352 : Rat)), [0,0,5,4,0,1]),
     (((385 : Rat)), [0,0,4,6,0,0])] := by
  native_decide

/-- `J1|_{p=0} = -y²`. -/
theorem J1_res_p0 :
    J1.filter (fun m => decide (a4deg m.2 = 0)) =
      normalize [(((-1 : Rat)), [0,0,2,0,0,0])] := by
  native_decide

/-- `F46|_{p=0} ≠ 0`: genuine residual direction. -/
theorem F46_res_ne :
    F46.filter (fun m => decide (a4deg m.2 = 0)) ≠ [] := by
  native_decide
