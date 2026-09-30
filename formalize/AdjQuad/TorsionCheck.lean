/-
Machine-checked torsion relation for `F46`: `p²·F46 = E` in `C_5`.

`E46` is the explicit seven-term `C_5`-expression of
Theorem `thm:quotient-4648` (integral cleared form, matching the
witness normalization of `F46`):
`40000q⁶J1⁷ + 193200q⁴J1⁶J2² + 325164q²J1⁵J2⁴ + 148225J1⁴J2⁶
  + 840q²J1³J2H + 770J1²J2³H + H²`.
Proved by exact kernel evaluation (`native_decide`).

Core-Lean only, zero `sorry`. Standalone module:
`lake build AdjQuad.TorsionCheck`.
-/
import AdjQuad.Deriv
import AdjQuad.Counterexample
import AdjQuad.SecondWitness

/-- `E46`: the `C_5`-expression with `p²·F46 = E46`. -/
def E46 : Poly :=
  polyAdd
    (polyMul [((40000 : Rat), zeroExp)]
      (polyMul (polyPow q 6) (polyPow J1 7)))
    (polyAdd
      (polyMul [((193200 : Rat), zeroExp)]
        (polyMul (polyPow q 4)
          (polyMul (polyPow J1 6) (polyPow J2 2))))
      (polyAdd
        (polyMul [((325164 : Rat), zeroExp)]
          (polyMul (polyPow q 2)
            (polyMul (polyPow J1 5) (polyPow J2 4))))
        (polyAdd
          (polyMul [((148225 : Rat), zeroExp)]
            (polyMul (polyPow J1 4) (polyPow J2 6)))
          (polyAdd
            (polyMul [((840 : Rat), zeroExp)]
              (polyMul (polyPow q 2)
                (polyMul (polyMul (polyPow J1 3) J2) H)))
            (polyAdd
              (polyMul [((770 : Rat), zeroExp)]
                (polyMul (polyPow J1 2)
                  (polyMul (polyPow J2 3) H)))
              (polyMul H H))))))

/-- `p²·F46 = E46`: the torsion relation, exactly. -/
theorem p2F46_eq_E46 : polyMul (polyMul p p) F46 = E46 := by
  native_decide

/-- `E46` is homogeneous of weight `48`. -/
theorem weightedDegree_E46 : weightedDegree E46 = 48 := by
  native_decide
