/-
D operator + invariants for N=5 (Batch A).

- `D(F) = a1a2·∂₀F + a2a3·∂₁F + a3a4·∂₂F + a4a5·∂₃F` via Poly API.
- `p = a4`, `q = a5`, `J1 = 2a1a4-a2²`, `J2 = 2a2a5-a3²`,
  `F0 = p²q⁴a0 -pq³a3a2a1 + (1/3)pq²a3³a1 + (1/3)q²a3³a2²
       -(1/5)qa3⁵a2 + (1/35)a3⁷` (6 terms),
  `c = p²q⁴`, `G0 = F0 - c·a0` (remaining five terms).

Core-Lean only. Definitions + trivial lemmas, fully proved.
-/
import AdjQuad.Poly

/-- Variables `a0..a5` as single-monomial polys. -/
def a0 : Poly := [(1, varExp 0)]
def a1 : Poly := [(1, varExp 1)]
def a2 : Poly := [(1, varExp 2)]
def a3 : Poly := [(1, varExp 3)]
def a4 : Poly := [(1, varExp 4)]
def a5 : Poly := [(1, varExp 5)]

/-- `p = a4`. -/
def p : Poly := a4
/-- `q = a5`. -/
def q : Poly := a5

/-- `J1 = 2a1a4 - a2²`. -/
def J1 : Poly := normalize
  [((2 : Rat), addExp (varExp 1) (varExp 4)),
   ((-1 : Rat), addExp (varExp 2) (varExp 2))]

/-- `J2 = 2a2a5 - a3²`. -/
def J2 : Poly := normalize
  [((2 : Rat), addExp (varExp 2) (varExp 5)),
   ((-1 : Rat), addExp (varExp 3) (varExp 3))]

/-- `F0 = p²q⁴a0 -pq³a3a2a1 + (1/3)pq²a3³a1 + (1/3)q²a3³a2²
        -(1/5)qa3⁵a2 + (1/35)a3⁷`. -/
def F0 : Poly := normalize
  [((1 : Rat), [1,0,0,0,2,4]),
   ((-1 : Rat), [0,1,1,1,1,3]),
   (((1 : Rat)/3), [0,1,0,3,1,2]),
   (((1 : Rat)/3), [0,0,2,3,0,2]),
   (((-1 : Rat)/5), [0,0,1,5,0,1]),
   (((1 : Rat)/35), [0,0,0,7,0,0])]

/-- `c = p²q⁴`. -/
def c : Poly := normalize [((1 : Rat), [0,0,0,0,2,4])]

/-- `G0 = F0 - c·a0` (remaining five terms). -/
def G0 : Poly := normalize
  [((-1 : Rat), [0,1,1,1,1,3]),
   (((1 : Rat)/3), [0,1,0,3,1,2]),
   (((1 : Rat)/3), [0,0,2,3,0,2]),
   (((-1 : Rat)/5), [0,0,1,5,0,1]),
   (((1 : Rat)/35), [0,0,0,7,0,0])]

/-- D operator: `a1a2·∂₀ + a2a3·∂₁ + a3a4·∂₂ + a4a5·∂₃` via Poly API. -/
def D (F : Poly) : Poly :=
  let t0 := polyMul (polyMul a1 a2) (partialDeriv ⟨0, by decide⟩ F)
  let t1 := polyMul (polyMul a2 a3) (partialDeriv ⟨1, by decide⟩ F)
  let t2 := polyMul (polyMul a3 a4) (partialDeriv ⟨2, by decide⟩ F)
  let t3 := polyMul (polyMul a4 a5) (partialDeriv ⟨3, by decide⟩ F)
  polyAdd (polyAdd t0 t1) (polyAdd t2 t3)

theorem p_def : p = a4 := rfl
theorem q_def : q = a5 := rfl
theorem D_def (F : Poly) :
    D F = polyAdd (polyAdd
      (polyMul (polyMul a1 a2) (partialDeriv ⟨0, by decide⟩ F))
      (polyMul (polyMul a2 a3) (partialDeriv ⟨1, by decide⟩ F)))
      (polyAdd
        (polyMul (polyMul a3 a4) (partialDeriv ⟨2, by decide⟩ F))
        (polyMul (polyMul a4 a5) (partialDeriv ⟨3, by decide⟩ F))) := rfl

theorem D_zero : D [] = normalize [] := by
  have hemp : ∀ P : Poly, P.flatMap (fun _ => ([] : Poly)) = [] := by
    intro P
    induction P with
    | nil => rfl
    | cons _ _ ih => simpa only [List.flatMap_cons, List.nil_append] using ih
  simp [D, partialDeriv, polyMul, polyAdd, normalize_nil, hemp]
