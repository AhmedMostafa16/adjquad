/-
Machine-checked plinth audit for `D_5` (referee assessment verification).

Proves, by exact kernel evaluation (`native_decide`), the identities
behind the corrected plinth lemma:
- `D(pq) = 0` (pq is invariant, hence in the plinth);
- `D(px) = p^2*q ≠ 0` and `D(xy) = pqy + px^2 ≠ 0`
  (in the image but not invariant);
- `D(a3·a4·a5^3) = c = p^2*q^4` (the pole denominator lies in the
  image, hence in the plinth ideal);
- `D(F13) = 0` and `D(G13) = F13` for the weight-13 pair
  (`F13 = p*J2^3/35 + p*q^2*J1*J2`, `G13` five terms), plus the
  `q = 0` restriction `F13|_{q=0} = -p*x^6/35 ≠ 0`
  (a `q`-primitive plinth element: the plinth is not `(pq)`).

Core-Lean only, zero `sorry`. Standalone module:
`lake build AdjQuad.PlinthCheck`.
-/
import AdjQuad.Deriv

/-- `D(pq) = 0`: pq is invariant. -/
theorem D_pq_zero : D (polyMul p q) = [] := by native_decide

/-- `D(px) = p^2*q`. -/
theorem D_px_eq : D (polyMul p a3) = polyMul (polyMul p p) q := by
  native_decide

/-- `px` is not invariant. -/
theorem D_px_ne_zero : D (polyMul p a3) ≠ [] := by native_decide

/-- `D(xy) = pqy + px^2`. -/
theorem D_xy_eq :
    D (polyMul a3 a2)
      = polyAdd (polyMul p (polyMul q a2)) (polyMul p (polyMul a3 a3)) := by
  native_decide

/-- `xy` is not invariant. -/
theorem D_xy_ne_zero : D (polyMul a3 a2) ≠ [] := by native_decide

/-- `c = D(a3·a4·a5^3)`: the pole denominator is in the image. -/
theorem c_in_image :
    D (polyMul a3 (polyMul a4 (polyPow a5 3))) = c := by
  native_decide

/-- `F13 = p*J2^3/35 + p*q^2*J1*J2` (weight 13, `q`-primitive plinth element). -/
def F13 : Poly :=
  polyAdd
    (polyMul [(1 / 35, zeroExp)] (polyMul p (polyPow J2 3)))
    (polyMul [(1 / 4, zeroExp)]
      (polyMul p (polyMul (polyPow q 2) (polyMul J1 J2))))

/-- `G13`: five-term preimage with `D(G13) = F13`. -/
def G13 : Poly := normalize
  [((1 : Rat), [1,0,0,0,2,3]),
   (((-1 : Rat)/6), [0,1,0,3,1,1]),
   (((-19 : Rat)/70), [0,0,3,1,0,2]),
   (((101 : Rat)/420), [0,0,2,3,0,1]),
   (((-1 : Rat)/35), [0,0,1,5,0,0])]

/-- `D(F13) = 0`: the `q`-primitive element is invariant. -/
theorem D_F13_zero : D F13 = [] := by native_decide

/-- `D(G13) = F13`: the `q`-primitive element is in the image. -/
theorem D_G13_eq_F13 : D G13 = F13 := by native_decide

/-- `a5`-exponent of an exponent vector (0 if short). -/
def a5deg (e : Exp) : Nat := e[5]?.getD 0

/-- Restriction `F13|_{q=0}` (terms free of `a5`) is `-p*x^6/35`. -/
theorem F13_res_q0 :
    F13.filter (fun m => decide (a5deg m.2 = 0))
      = [(((-1 : Rat)/35), [0,0,0,6,1,0])] := by
  native_decide

/-- Hence `q ∤ F13`: the restriction is nonzero. -/
theorem F13_qfree :
    F13.filter (fun m => decide (a5deg m.2 = 0)) ≠ [] := by
  native_decide
