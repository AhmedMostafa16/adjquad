import AdjQuad.GenerationBundle
import AdjQuad.WitnessDataB1
import AdjQuad.WitnessDataB2_2
import AdjQuad.WitnessDataB2_3
import AdjQuad.WitnessDataB2_5
import AdjQuad.WitnessDataB2_7
import AdjQuad.WitnessDataB2_8
import AdjQuad.WitnessDataB2_9
import AdjQuad.WitnessDataB2_10
import AdjQuad.WitnessDataB2_11
import AdjQuad.WitnessDataB2_12
import AdjQuad.WitnessDataB2_13
import AdjQuad.WitnessDataB2_14

namespace GenerationVerified
open GenerationBundle

def checkedBundle_0 : CheckedBundle 0 := by
  have hn : (monoW 0).length = 1 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_0
  exact {
    S := W0S
    T := W0T
    C := W0C
    N := W0N
    K := W0K
    Gsel := W0Gsel
    Kg := W0Kg
    Y := W0Y
    d1 := W0d1
    d4 := W0d4
    d3 := W0d3
    dg := W0dg
    dY := W0dY
    D0 := W0D0
    selIdx := W0selIdx
    r := 0
    k := 1
    witness := witness_ok_0
    decode := gselDecode_0
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W0Q, W0A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_0
    qLeftInv := by simpa only [hn, W0Q, W0A] using qLeftInv_0
    qNonzero := qLeftInv_nz_0 }

def checkedBundle_1 : CheckedBundle 1 := by
  have hn : (monoW 1).length = 2 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_1
  exact {
    S := W1S
    T := W1T
    C := W1C
    N := W1N
    K := W1K
    Gsel := W1Gsel
    Kg := W1Kg
    Y := W1Y
    d1 := W1d1
    d4 := W1d4
    d3 := W1d3
    dg := W1dg
    dY := W1dY
    D0 := W1D0
    selIdx := W1selIdx
    r := 0
    k := 2
    witness := witness_ok_1
    decode := gselDecode_1
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W1Q, W1A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_1
    qLeftInv := by simpa only [hn, W1Q, W1A] using qLeftInv_1
    qNonzero := qLeftInv_nz_1 }

def checkedBundle_2 : CheckedBundle 2 := by
  have hn : (monoW 2).length = 4 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_2
  exact {
    S := W2S
    T := W2T
    C := W2C
    N := W2N
    K := W2K
    Gsel := W2Gsel
    Kg := W2Kg
    Y := W2Y
    d1 := W2d1
    d4 := W2d4
    d3 := W2d3
    dg := W2dg
    dY := W2dY
    D0 := W2D0
    selIdx := W2selIdx
    r := 1
    k := 3
    witness := witness_ok_2
    decode := gselDecode_2
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W2Q, W2A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_2
    qLeftInv := by simpa only [hn, W2Q, W2A] using qLeftInv_2
    qNonzero := qLeftInv_nz_2 }

def checkedBundle_3 : CheckedBundle 3 := by
  have hn : (monoW 3).length = 7 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_3
  exact {
    S := W3S
    T := W3T
    C := W3C
    N := W3N
    K := W3K
    Gsel := W3Gsel
    Kg := W3Kg
    Y := W3Y
    d1 := W3d1
    d4 := W3d4
    d3 := W3d3
    dg := W3dg
    dY := W3dY
    D0 := W3D0
    selIdx := W3selIdx
    r := 3
    k := 4
    witness := witness_ok_3
    decode := gselDecode_3
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W3Q, W3A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_3
    qLeftInv := by simpa only [hn, W3Q, W3A] using qLeftInv_3
    qNonzero := qLeftInv_nz_3 }

def checkedBundle_4 : CheckedBundle 4 := by
  have hn : (monoW 4).length = 11 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_4
  exact {
    S := W4S
    T := W4T
    C := W4C
    N := W4N
    K := W4K
    Gsel := W4Gsel
    Kg := W4Kg
    Y := W4Y
    d1 := W4d1
    d4 := W4d4
    d3 := W4d3
    dg := W4dg
    dY := W4dY
    D0 := W4D0
    selIdx := W4selIdx
    r := 5
    k := 6
    witness := witness_ok_4
    decode := gselDecode_4
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W4Q, W4A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_4
    qLeftInv := by simpa only [hn, W4Q, W4A] using qLeftInv_4
    qNonzero := qLeftInv_nz_4 }

def checkedBundle_5 : CheckedBundle 5 := by
  have hn : (monoW 5).length = 17 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_5
  exact {
    S := W5S
    T := W5T
    C := W5C
    N := W5N
    K := W5K
    Gsel := W5Gsel
    Kg := W5Kg
    Y := W5Y
    d1 := W5d1
    d4 := W5d4
    d3 := W5d3
    dg := W5dg
    dY := W5dY
    D0 := W5D0
    selIdx := W5selIdx
    r := 9
    k := 8
    witness := witness_ok_5
    decode := gselDecode_5
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W5Q, W5A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_5
    qLeftInv := by simpa only [hn, W5Q, W5A] using qLeftInv_5
    qNonzero := qLeftInv_nz_5 }

def checkedBundle_6 : CheckedBundle 6 := by
  have hn : (monoW 6).length = 25 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_6
  exact {
    S := W6S
    T := W6T
    C := W6C
    N := W6N
    K := W6K
    Gsel := W6Gsel
    Kg := W6Kg
    Y := W6Y
    d1 := W6d1
    d4 := W6d4
    d3 := W6d3
    dg := W6dg
    dY := W6dY
    D0 := W6D0
    selIdx := W6selIdx
    r := 14
    k := 11
    witness := witness_ok_6
    decode := gselDecode_6
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W6Q, W6A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_6
    qLeftInv := by simpa only [hn, W6Q, W6A] using qLeftInv_6
    qNonzero := qLeftInv_nz_6 }

def checkedBundle_7 : CheckedBundle 7 := by
  have hn : (monoW 7).length = 35 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_7
  exact {
    S := W7S
    T := W7T
    C := W7C
    N := W7N
    K := W7K
    Gsel := W7Gsel
    Kg := W7Kg
    Y := W7Y
    d1 := W7d1
    d4 := W7d4
    d3 := W7d3
    dg := W7dg
    dY := W7dY
    D0 := W7D0
    selIdx := W7selIdx
    r := 21
    k := 14
    witness := witness_ok_7
    decode := gselDecode_7
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W7Q, W7A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_7
    qLeftInv := by simpa only [hn, W7Q, W7A] using qLeftInv_7
    qNonzero := qLeftInv_nz_7 }

def checkedBundle_8 : CheckedBundle 8 := by
  have hn : (monoW 8).length = 49 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_8
  exact {
    S := W8S
    T := W8T
    C := W8C
    N := W8N
    K := W8K
    Gsel := W8Gsel
    Kg := W8Kg
    Y := W8Y
    d1 := W8d1
    d4 := W8d4
    d3 := W8d3
    dg := W8dg
    dY := W8dY
    D0 := W8D0
    selIdx := W8selIdx
    r := 31
    k := 18
    witness := witness_ok_8
    decode := gselDecode_8
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W8Q, W8A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_8
    qLeftInv := by simpa only [hn, W8Q, W8A] using qLeftInv_8
    qNonzero := qLeftInv_nz_8 }

def checkedBundle_9 : CheckedBundle 9 := by
  have hn : (monoW 9).length = 66 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_9
  exact {
    S := W9S
    T := W9T
    C := W9C
    N := W9N
    K := W9K
    Gsel := W9Gsel
    Kg := W9Kg
    Y := W9Y
    d1 := W9d1
    d4 := W9d4
    d3 := W9d3
    dg := W9dg
    dY := W9dY
    D0 := W9D0
    selIdx := W9selIdx
    r := 44
    k := 22
    witness := witness_ok_9
    decode := gselDecode_9
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W9Q, W9A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_9
    qLeftInv := by simpa only [hn, W9Q, W9A] using qLeftInv_9
    qNonzero := qLeftInv_nz_9 }

def checkedBundle_10 : CheckedBundle 10 := by
  have hn : (monoW 10).length = 88 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_10
  exact {
    S := W10S
    T := W10T
    C := W10C
    N := W10N
    K := W10K
    Gsel := W10Gsel
    Kg := W10Kg
    Y := W10Y
    d1 := W10d1
    d4 := W10d4
    d3 := W10d3
    dg := W10dg
    dY := W10dY
    D0 := W10D0
    selIdx := W10selIdx
    r := 61
    k := 27
    witness := witness_ok_10
    decode := gselDecode_10
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W10Q, W10A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_10
    qLeftInv := by simpa only [hn, W10Q, W10A] using qLeftInv_10
    qNonzero := qLeftInv_nz_10 }

def checkedBundle_11 : CheckedBundle 11 := by
  have hn : (monoW 11).length = 115 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_11
  exact {
    S := W11S
    T := W11T
    C := W11C
    N := W11N
    K := W11K
    Gsel := W11Gsel
    Kg := W11Kg
    Y := W11Y
    d1 := W11d1
    d4 := W11d4
    d3 := W11d3
    dg := W11dg
    dY := W11dY
    D0 := W11D0
    selIdx := W11selIdx
    r := 83
    k := 32
    witness := witness_ok_11
    decode := gselDecode_11
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W11Q, W11A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_11
    qLeftInv := by simpa only [hn, W11Q, W11A] using qLeftInv_11
    qNonzero := qLeftInv_nz_11 }

def checkedBundle_12 : CheckedBundle 12 := by
  have hn : (monoW 12).length = 148 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_12
  exact {
    S := W12S
    T := W12T
    C := W12C
    N := W12N
    K := W12K
    Gsel := W12Gsel
    Kg := W12Kg
    Y := W12Y
    d1 := W12d1
    d4 := W12d4
    d3 := W12d3
    dg := W12dg
    dY := W12dY
    D0 := W12D0
    selIdx := W12selIdx
    r := 109
    k := 39
    witness := witness_ok_12
    decode := gselDecode_12
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W12Q, W12A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_12
    qLeftInv := by simpa only [hn, W12Q, W12A] using qLeftInv_12
    qNonzero := qLeftInv_nz_12 }

def checkedBundle_13 : CheckedBundle 13 := by
  have hn : (monoW 13).length = 188 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_13
  exact {
    S := W13S
    T := W13T
    C := W13C
    N := W13N
    K := W13K
    Gsel := W13Gsel
    Kg := W13Kg
    Y := W13Y
    d1 := W13d1
    d4 := W13d4
    d3 := W13d3
    dg := W13dg
    dY := W13dY
    D0 := W13D0
    selIdx := W13selIdx
    r := 142
    k := 46
    witness := witness_ok_13
    decode := gselDecode_13
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W13Q, W13A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_13
    qLeftInv := by simpa only [hn, W13Q, W13A] using qLeftInv_13
    qNonzero := qLeftInv_nz_13 }

def checkedBundle_14 : CheckedBundle 14 := by
  have hn : (monoW 14).length = 236 := by native_decide
  obtain ⟨hGr, hGc, hKr, hKc, hQc, hYc, hS⟩ := shape_ok_14
  exact {
    S := W14S
    T := W14T
    C := W14C
    N := W14N
    K := W14K
    Gsel := W14Gsel
    Kg := W14Kg
    Y := W14Y
    d1 := W14d1
    d4 := W14d4
    d3 := W14d3
    dg := W14dg
    dY := W14dY
    D0 := W14D0
    selIdx := W14selIdx
    r := 181
    k := 55
    witness := witness_ok_14
    decode := gselDecode_14
    positive := by decide
    selected := by decide
    gRows := by simpa only [hn] using hGr
    gCols := hGc
    kgRows := hKr
    kgCols := by simpa only [hn] using hKc
    qCols := by simpa only [hn, W14Q, W14A] using hQc
    yCols := hYc
    pivotBounds := by simpa only [hn] using hS
    gKernel := by simpa only [hn] using gselKernel_14
    qLeftInv := by simpa only [hn, W14Q, W14A] using qLeftInv_14
    qNonzero := qLeftInv_nz_14 }

theorem checked_through_14 : ∀ w, w ≤ 14 → Nonempty (CheckedBundle w) := by
  intro w hw
  match w with
  | 0 => exact ⟨checkedBundle_0⟩
  | 1 => exact ⟨checkedBundle_1⟩
  | 2 => exact ⟨checkedBundle_2⟩
  | 3 => exact ⟨checkedBundle_3⟩
  | 4 => exact ⟨checkedBundle_4⟩
  | 5 => exact ⟨checkedBundle_5⟩
  | 6 => exact ⟨checkedBundle_6⟩
  | 7 => exact ⟨checkedBundle_7⟩
  | 8 => exact ⟨checkedBundle_8⟩
  | 9 => exact ⟨checkedBundle_9⟩
  | 10 => exact ⟨checkedBundle_10⟩
  | 11 => exact ⟨checkedBundle_11⟩
  | 12 => exact ⟨checkedBundle_12⟩
  | 13 => exact ⟨checkedBundle_13⟩
  | 14 => exact ⟨checkedBundle_14⟩
  | n + 15 => omega

theorem local_span_through_14 : GenerationClosure.LocalSpan 14 :=
  local_span_through_Wmax 14 checked_through_14

theorem span_through_14 (F : Poly)
    (h0 : hasNoZeros F) (hd : hasNoDups F)
    (hp : List.Pairwise (fun a b => monoLE a b = true) F)
    (hs : supp6 F) (hDF : D F = []) (hw : weightedDegree F ≤ 14) :
    GenerationClosure.Generated F :=
  span_through_Wmax 14 checked_through_14 F h0 hd hp hs hDF hw

end GenerationVerified
