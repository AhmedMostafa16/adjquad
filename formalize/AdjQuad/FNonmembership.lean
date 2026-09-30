import AdjQuad.SecondWitness
import AdjQuad.Exclusion

/-
F46 ∉ C5 via the J4 top-ideal argument (paper Lemma lem:J4):
DOCUMENTED STOP (Task 7).

Goal: every C5-monomial of a0-degree 4 has its top a0-coefficient in
J4 = (p^8 q^8), while F46's top (18375/4) p^6 q^8 lies outside — hence F46 ∉ C5.

What IS machine-checked here (zero sorry):
- `a0top`: the top-a0-slice operator (filter on the a0-exponent);
- the concrete tops `a0top 4 F46`, `a0top 1 F0`, `a0top 2 H` (singletons,
  by native_decide) and the degree bound `∀ m ∈ F46, a0deg m.2 ≤ 4`;
- the C5-membership predicate `inC5` (mirror of `inK_F0` in Exclusion.lean).

BLOCKING LEMMA (attempt stopped here — see Task 7 report):
  `a0top_filter_combine : ∀ (d : Nat) (p : Poly),
    a0top d (combine p) = combine (a0top d p)`.
Every subsequent step (top-multiplication for `polyMul`, top-addition for
`polyAdd`, the C5 top induction, J4 ideal closure) depends on it, and its
proof needs a full filter-vs-`insertCombineGo` analysis (found/not-found ×
zero/nonzero-drop case splits) plus a filter-vs-`sortPoly`-permutation
lemma — estimated >150 lines of Poly-API scaffolding before the first real
lemma (top-multiplication for the F0/H instances). Per the Task 7 stop rule
the attempt stops here; non-membership stays paper-level + Sage-exact.

Standalone module: `lake build AdjQuad.FNonmembership`. Core-Lean only.
-/

/-- Top `a0`-slice of `P` at degree `d`: terms whose `a0`-exponent is `d`. -/
def a0top (d : Nat) (P : Poly) : Poly :=
  P.filter (fun m => decide (a0deg m.2 = d))

theorem a0top_nil (d : Nat) : a0top d [] = [] := rfl

theorem a0top_append (d : Nat) (p q : Poly) :
    a0top d (p ++ q) = a0top d p ++ a0top d q := by
  simp [a0top, List.filter_append]

/-- Every term of F46 has `a0`-exponent at most 4. -/
theorem F46_a0deg_le4 : ∀ m ∈ F46, a0deg m.2 ≤ 4 := by native_decide

/-- The `a0`-degree-4 top slice of F46 is the singleton top term. -/
theorem F46_top : a0top 4 F46 = [(121550625, [4,0,0,0,6,8])] := by native_decide

/-- The `a0`-degree-1 top slice of F0 is `c·a0` with `c = p^2q^4`. -/
theorem F0_top : a0top 1 F0 = [((1 : Rat), [1,0,0,0,2,4])] := by native_decide

/-- The `a0`-degree-2 top slice of H is `11025 a0^2a4^4a5^4`. -/
theorem H_top : a0top 2 H = [((11025 : Rat), [2,0,0,0,4,4])] := by native_decide

/-
`inC5` is, by construction, the smallest k-subalgebra of A = k[a0..a5]
containing `{p, q, J1, J2, F0, H}`: generated from 0, 1, the six generators
under addition and multiplication. `inC5 y` reads `y ∈ C5`.
The J4 top induction over this predicate is blocked on
`a0top_filter_combine` (see header); it is stated here so the obstruction
has a precise formal footprint.
-/
inductive inC5 : Poly → Prop
  | mkZero : inC5 []
  | mkOne : inC5 [(1, zeroExp)]
  | mkP : inC5 p
  | mkQ : inC5 q
  | mkJ1 : inC5 J1
  | mkJ2 : inC5 J2
  | mkF0 : inC5 F0
  | mkH : inC5 H
  | mkSum {x y} : inC5 x → inC5 y → inC5 (polyAdd x y)
  | mkProd {x y} : inC5 x → inC5 y → inC5 (polyMul x y)
