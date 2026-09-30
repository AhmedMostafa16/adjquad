-- GENERATED (UNTRUSTED input for Lean checking). Do not edit.

-- Produced by scripts/cas/emit_witnesses.py; verified in Lean

-- by mats_match_*/witness_ok_*/gselKernel_*/gselDecode_*/leftInv_*/qLeftInv_*

import AdjQuad.Generation

-- Compute budgets raised for large-n kernel evaluation

-- (soundness-neutral: only timeout/recursion guards).

set_option maxHeartbeats 1000000

set_option maxRecDepth 100000

def W2S : List Nat := [1]
def W2T : IMat := [[0], [0], [0], [1]]
def W2C : IMat := [[0], [1], [0], [0]]
def W2N : IMat := [[1, 0, 0], [0, 1, 0], [0, 0, 1], [0, 0, 0]]
def W2K : IMat := [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]]
def W2Gsel : IMat := [[1, 0, 0], [0, 1, 0], [0, 0, 1], [0, 0, 0]]
def W2Kg : IMat := [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]]
def W2L : IMat := [[0, 1, 0, 0]]
def W2Y : IMat := [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0]]
def W2X : IMat := [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
def W2B : IMat := [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]]
def W2d1 : Int := 1
def W2d4 : Int := 1
def W2d3 : Int := 1
def W2dg : Int := 1
def W2D0 : Int := 1
def W2selIdx : List Nat := [0, 1, 2]
def W2M : IMat := [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]]
theorem mats_match_2 : dmat 2 = W2M := by native_decide
theorem witness_ok_2 : checkWitness (dmat 2) W2S W2T W2C W2N W2K W2Gsel W2Kg W2d1 W2d4 W2d3 W2dg 1 3 := by native_decide
theorem gselKernel_2 : imatMul (dmat 2) W2Gsel = imatZero 4 3 := by native_decide
theorem gselDecode_2 : gselDecode 2 W2selIdx W2Gsel W2D0 = true := by native_decide
def W2A : IMat := imatRowsOf (dmat 2) W2S
def W2Q : IMat := W2A ++ W2Kg
def W2dL : Int := 1
def W2dY : Int := 1
def W2dB : Int := 1
def W2dX : Int := 1
theorem leftInv_2 : imatMul W2L W2C = imatSmul W2dL (imatEye 1) := by native_decide
theorem qLeftInv_2 : imatMul W2Y W2Q = imatSmul W2dY (imatEye 4) := by native_decide
theorem leftInv_nz_2 : W2dL ≠ 0 := by decide
theorem qLeftInv_nz_2 : W2dY ≠ 0 := by decide
theorem shape_ok_2 : imatRows W2Gsel = 4 ∧ imatCols W2Gsel = 3 ∧ imatRows W2Kg = 3 ∧ imatCols W2Kg = 4 ∧ imatCols W2Q = 4 ∧ imatCols W2Y = imatRows W2Q ∧ (∀ i ∈ W2S, i < 4) := by native_decide
theorem kerFactor_2 : imatMul (imatTranspose (dmat 2)) W2B = imatSmul W2dB (imatSub (imatSmul W2d3 (imatEye 4)) (imatMul W2N W2K)) := by native_decide
theorem xGsel_2 : imatMul W2Gsel W2X = imatSmul W2dX W2N := by native_decide
theorem xGsel_nz_2 : W2dX ≠ 0 := by decide
theorem kerFactor_nz_2 : W2dB ≠ 0 := by decide
