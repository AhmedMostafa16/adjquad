-- GENERATED (UNTRUSTED input for Lean checking). Do not edit.

-- Produced by scripts/cas/emit_witnesses.py; verified in Lean

-- by mats_match_*/witness_ok_*/gselKernel_*/gselDecode_*/leftInv_*/qLeftInv_*

import AdjQuad.Generation

-- Compute budgets raised for large-n kernel evaluation

-- (soundness-neutral: only timeout/recursion guards).

set_option maxHeartbeats 1000000

set_option maxRecDepth 100000

def W3S : List Nat := [1, 2, 5]
def W3T : IMat := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 0, 1]]
def W3C : IMat := [[0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 0, 0], [0, 0, 0], [0, 0, 1], [0, 0, 0]]
def W3N : IMat := [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
def W3K : IMat := [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0]]
def W3Gsel : IMat := [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
def W3Kg : IMat := [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0]]
def W3L : IMat := [[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]]
def W3Y : IMat := [[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]]
def W3X : IMat := [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
def W3B : IMat := [[0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0]]
def W3d1 : Int := 1
def W3d4 : Int := 1
def W3d3 : Int := 1
def W3dg : Int := 1
def W3D0 : Int := 1
def W3selIdx : List Nat := [0, 1, 2, 3]
def W3M : IMat := [[0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0]]
theorem mats_match_3 : dmat 3 = W3M := by native_decide
theorem witness_ok_3 : checkWitness (dmat 3) W3S W3T W3C W3N W3K W3Gsel W3Kg W3d1 W3d4 W3d3 W3dg 3 4 := by native_decide
theorem gselKernel_3 : imatMul (dmat 3) W3Gsel = imatZero 7 4 := by native_decide
theorem gselDecode_3 : gselDecode 3 W3selIdx W3Gsel W3D0 = true := by native_decide
def W3A : IMat := imatRowsOf (dmat 3) W3S
def W3Q : IMat := W3A ++ W3Kg
def W3dL : Int := 1
def W3dY : Int := 1
def W3dB : Int := 1
def W3dX : Int := 1
theorem leftInv_3 : imatMul W3L W3C = imatSmul W3dL (imatEye 3) := by native_decide
theorem qLeftInv_3 : imatMul W3Y W3Q = imatSmul W3dY (imatEye 7) := by native_decide
theorem leftInv_nz_3 : W3dL ≠ 0 := by decide
theorem qLeftInv_nz_3 : W3dY ≠ 0 := by decide
theorem shape_ok_3 : imatRows W3Gsel = 7 ∧ imatCols W3Gsel = 4 ∧ imatRows W3Kg = 4 ∧ imatCols W3Kg = 7 ∧ imatCols W3Q = 7 ∧ imatCols W3Y = imatRows W3Q ∧ (∀ i ∈ W3S, i < 7) := by native_decide
theorem kerFactor_3 : imatMul (imatTranspose (dmat 3)) W3B = imatSmul W3dB (imatSub (imatSmul W3d3 (imatEye 7)) (imatMul W3N W3K)) := by native_decide
theorem xGsel_3 : imatMul W3Gsel W3X = imatSmul W3dX W3N := by native_decide
theorem xGsel_nz_3 : W3dX ≠ 0 := by decide
theorem kerFactor_nz_3 : W3dB ≠ 0 := by decide
