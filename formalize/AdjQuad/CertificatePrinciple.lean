import AdjQuad.KernelSpan
import AdjQuad.Generation

/-
Certification principle for graded kernel spanning (paper §1,
`paper/12-certification.tex`). General contract, N=5-independent:

1. `M` (n×n), `Gsel` (n×k, k > 0) with `M * Gsel = 0`;
2. `Kg` (k×n) with `Kg * Gsel = dg * I`, `dg ≠ 0`;
3. `Y`, `dY ≠ 0` with `Y * (rowsOf(M,S) ++ Kg) = dY * I`
   (`++` = vertical row-block concatenation, never matrix addition).

Conclusion (`KernelSpan.kernel_span_of_qLeftInv`): every integer `v`
with `M * v = 0` satisfies `dg * v = Gsel * (Kg * v)`.
Denominator contract (`crossmul_decode` from `gselDecode = true`):
`Gsel[i][j] = D0 * c` over `Rat`, rejecting truncation.
This file adds no new mathematics; it pins the interface.
-/

-- Interface pins: fail loudly if upstream renames or restructures.
#check @KernelSpan.kernel_span_of_qLeftInv
#check @crossmul_decode
#check @gselDecode_entry
