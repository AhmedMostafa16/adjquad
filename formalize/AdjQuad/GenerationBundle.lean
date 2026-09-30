import AdjQuad.KernelSpan
import AdjQuad.GenerationSpan
import AdjQuad.GenerationClosure

namespace GenerationBundle

/-- Multiplication-checkable certificate data, not a spanning assumption.
The extra `Y` certificate is the producer's `qLeftInv`; the shapes exclude
ragged or dimension-erased matrices admitted by the raw list representation. -/
structure CheckedBundle (w : Nat) where
  S : List Nat
  T : IMat
  C : IMat
  N : IMat
  K : IMat
  Gsel : IMat
  Kg : IMat
  Y : IMat
  d1 : Int
  d4 : Int
  d3 : Int
  dg : Int
  dY : Int
  D0 : Int
  r : Nat
  k : Nat
  selIdx : List Nat
  witness : checkWitness (dmat w) S T C N K Gsel Kg d1 d4 d3 dg r k = true
  decode : gselDecode w selIdx Gsel D0 = true
  positive : 0 < k
  selected : selIdx.length = k
  gRows : imatRows Gsel = (monoW w).length
  gCols : imatCols Gsel = k
  kgRows : imatRows Kg = k
  kgCols : imatCols Kg = (monoW w).length
  qCols : imatCols (imatRowsOf (dmat w) S ++ Kg) = (monoW w).length
  yCols : imatCols Y = imatRows (imatRowsOf (dmat w) S ++ Kg)
  pivotBounds : ∀ i ∈ S, i < (monoW w).length
  gKernel : imatMul (dmat w) Gsel = imatZero (monoW w).length k
  qLeftInv : imatMul Y (imatRowsOf (dmat w) S ++ Kg) =
    imatSmul dY (imatEye (monoW w).length)
  qNonzero : dY ≠ 0

/-- Actual checked data imply spanning of every integral kernel vector. -/
theorem kernel_span (w : Nat) (b : CheckedBundle w)
    (v : List Int) (hv : v.length = (monoW w).length)
    (hMv : matVecMul (dmat w) v = zeroVec (monoW w).length) :
    ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧ cs.length = b.selIdx.length ∧
      vecSmul d v = lincomb cs (imatTranspose b.Gsel) := by
  have hW := b.witness
  simp only [checkWitness, Bool.and_eq_true] at hW
  have hdg : b.dg ≠ 0 := of_decide_eq_true hW.1.1.1.1.1.1.2
  have hKG : imatMul b.Kg b.Gsel = imatSmul b.dg (imatEye b.k) :=
    beq_iff_eq.mp hW.1.2
  obtain ⟨cs, d, hd, hc, he⟩ := KernelSpan.kernel_span_of_qLeftInv
    (dmat w) b.Gsel b.Kg b.Y b.S (monoW w).length b.k b.dg b.dY
    b.positive (imatCols_dmat w) (imatRows_dmat w) b.gRows b.gCols
    b.kgRows b.kgCols b.qCols b.yCols b.pivotBounds hdg b.qNonzero
    b.gKernel hKG b.qLeftInv v hv hMv
  exact ⟨cs, d, hd, hc.trans b.selected.symm, he⟩

/-- Polynomial generation at one exact weight from the actual checked bundle.
No matrix or polynomial spanning statement occurs among the premises. -/
theorem span_of_bundle (w : Nat) (b : CheckedBundle w)
    (F : Poly) (h0 : hasNoZeros F) (hd : hasNoDups F)
    (hp : List.Pairwise (fun a b => monoLE a b = true) F)
    (hs : supp6 F) (hh : homogeneous F w) (hDF : D F = []) :
    ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧ cs.length = (genMonos w).length ∧
      polySmulInt d F = polyLincomb cs (genMonos w) :=
  GenerationSpan.span_of_kernel_span w b.selIdx b.Gsel b.D0 b.decode
    b.gRows (b.gCols.trans b.selected.symm) (by rw [b.selected]; exact b.positive)
    (kernel_span w b) F h0 hd hp hs hh hDF

/-- Exact-weight spanning through the verified bound. -/
theorem local_span_through_Wmax (Wmax : Nat)
    (hW : ∀ w, w ≤ Wmax → Nonempty (CheckedBundle w)) :
    GenerationClosure.LocalSpan Wmax := by
  intro w hw F h0 hd hp hs hh hDF
  obtain ⟨b⟩ := hW w hw
  exact span_of_bundle w b F h0 hd hp hs hh hDF

/-- Mixed-weight invariants of bounded degree are generated, with no
    algebraic premise beyond the checked bundles. -/
theorem span_through_Wmax (Wmax : Nat)
    (hW : ∀ w, w ≤ Wmax → Nonempty (CheckedBundle w))
    (F : Poly) (h0 : hasNoZeros F) (hd : hasNoDups F)
    (hp : List.Pairwise (fun a b => monoLE a b = true) F)
    (hs : supp6 F) (hDF : D F = [])
    (hw : weightedDegree F ≤ Wmax) :
    GenerationClosure.Generated F :=
  GenerationClosure.generated_bounded Wmax
    (local_span_through_Wmax Wmax hW) F h0 hd hp hs hDF hw
/-- The only non-certificate premise is the stated reduction to lower weights. -/
theorem generation_closed (B Wmax : Nat) (hle : B ≤ Wmax)
    (hW : ∀ w, w ≤ Wmax → Nonempty (CheckedBundle w))
    (h_bound : ∀ F : Poly, hasNoZeros F → hasNoDups F →
      List.Pairwise (fun a b => monoLE a b = true) F →
      supp6 F → D F = [] → B < weightedDegree F →
      ∃ parts : List Poly,
        (∀ G ∈ parts, hasNoZeros G ∧ hasNoDups G ∧
          List.Pairwise (fun a b => monoLE a b = true) G ∧
          supp6 G ∧ D G = [] ∧ weightedDegree G < weightedDegree F) ∧
        ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧
          polySmulInt d F = polyLincomb cs parts)
    (F : Poly) (h0 : hasNoZeros F) (hd : hasNoDups F)
    (hp : List.Pairwise (fun a b => monoLE a b = true) F)
    (hs : supp6 F) (hDF : D F = []) :
    ∃ monos : List (Poly × Nat), (∀ q ∈ monos, q.1 ∈ genMonos q.2) ∧
      ∃ cs : List Int, ∃ d : Int, d ≠ 0 ∧ cs.length = monos.length ∧
        polySmulInt d F = polyLincomb cs (monos.map Prod.fst) :=
  GenerationClosure.generation_closed_of_local_span B Wmax hle
    (local_span_through_Wmax Wmax hW) h_bound F h0 hd hp hs hDF

end GenerationBundle
