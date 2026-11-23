import QuarticBinBounds
import QuarticShellBins
import QuarticCertificateFromCells

open QuarticFixed MeasureTheory Set

namespace QuarticKernel

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

private def scaleLower : ℚ := 1638902.544018973241
private def scaleUpper : ℚ := 1638902.544018973243

private theorem scale_cert : (scaleLower:ℝ) ≤ scale ∧ scale ≤ (scaleUpper:ℝ) := by
  have hD : (26509772707289:ℝ) = conductorNorm := by norm_num [conductorNorm]
  have hs : (5148764.19223962906863:ℝ) ≤ Real.sqrt (conductorNorm:ℝ) ∧
      Real.sqrt (conductorNorm:ℝ) ≤ 5148764.19223962906865 := by
    rw [← hD]
    constructor
    · exact ((Real.lt_sqrt (by norm_num)).2 (by norm_num)).le
    · exact ((Real.sqrt_lt (by norm_num : (0:ℝ) ≤ 26509772707289)
        (by norm_num : (0:ℝ) ≤ 5148764.19223962906865)).2 (by norm_num)).le
  have hp : 0 < Real.pi := Real.pi_pos
  unfold scale
  norm_num [scaleLower, scaleUpper]
  constructor
  · apply (le_div_iff₀ hp).2
    linarith only [Real.pi_lt_d20, hs.1]
  · apply (div_le_iff₀ hp).2
    linarith only [Real.pi_gt_d20, hs.2]

private def xBox (j : ℕ) : Box :=
  expBox (QuarticGrid.node j)

private def uLo (j : ℕ) : ℚ := (xBox j).lo / precision / scaleUpper
private def uHi (j : ℕ) : ℚ := (xBox j).hi / precision / scaleLower

private def rBox (j : ℕ) : Box :=
  ⟨(expNegBox (uHi (j+1))).lo, (expNegBox (uLo j)).hi⟩

private def eHalfBox (j : ℕ) : Box :=
  ⟨(expBox (QuarticGrid.node j / 2)).lo, (expBox (QuarticGrid.node (j+1) / 2)).hi⟩

private def checkCell (j : ℕ) : Bool :=
  let rb := rBox j
  let eb := eHalfBox j
  let tb := thetaBox rb actualBins
  decide (uLo j ≤ 64 ∧ uHi (j+1) ≤ 64 ∧ (rb.hi:ℚ)/precision < 1 ∧
    0 ≤ tb.1 ∧ QuarticGrid.lowerK j ≤ ((eb.lo:ℚ)/precision)*tb.1 ∧
      ((eb.hi:ℚ)/precision)*tb.2 ≤ QuarticGrid.upperK j)

private theorem node_nonneg (j : ℕ) : 0 ≤ QuarticGrid.node j := by
  unfold QuarticGrid.node
  positivity

private theorem node_le {j : ℕ} (hj : j ≤ 1051) : QuarticGrid.node j ≤ 64 := by
  have hh : (j:ℚ) ≤ 1051 := by exact_mod_cast hj
  unfold QuarticGrid.node
  linarith only [hh]

private theorem uLo_nonneg (j : ℕ) : 0 ≤ uLo j := by
  unfold uLo scaleUpper
  positivity

private theorem uHi_nonneg (j : ℕ) : 0 ≤ uHi j := by
  unfold uHi scaleLower
  positivity

private theorem uLow_sound {j : ℕ} (hj : j ≤ 1051) {x : ℝ}
    (hx : (QuarticGrid.node j : ℝ) ≤ x) :
    (uLo j:ℝ) ≤ Real.exp x/scale := by
  have hb := contains_lo (expBox_spec (node_nonneg j) (node_le hj))
  have he := hb.trans (Real.exp_le_exp.mpr hx)
  simp only [uLo, Rat.cast_div, Rat.cast_natCast]
  apply div_le_div₀ (by positivity) he scale_pos scale_cert.2

private theorem uHigh_sound {j : ℕ} (hj : j ≤ 1051) {x : ℝ}
    (hx : x ≤ (QuarticGrid.node j : ℝ)) :
    Real.exp x/scale ≤ (uHi j:ℝ) := by
  have hb := contains_hi (expBox_spec (node_nonneg j) (node_le hj))
  have he := (Real.exp_le_exp.mpr hx).trans hb
  simp only [uHi, Rat.cast_div, Rat.cast_natCast]
  exact div_le_div₀ (by positivity) he (by norm_num [scaleLower]) scale_cert.1

private theorem rBox_sound {j : ℕ} (hj : j < 1051) {x : ℝ}
    (hx : x ∈ Icc (QuarticGrid.node j:ℝ) (QuarticGrid.node (j+1):ℝ))
    (hl : uLo j ≤ 64) (hu : uHi (j+1) ≤ 64) :
    Contains (rBox j) (Real.exp (-(Real.exp x/scale))) := by
  have eL := expNegBox_spec (uHi_nonneg (j+1)) hu
  have eH := expNegBox_spec (uLo_nonneg j) hl
  have el := contains_lo eL
  have eh := contains_hi eH
  have hL := Real.exp_le_exp.mpr (neg_le_neg (uHigh_sound (Nat.succ_le_of_lt hj) hx.2))
  have hH := Real.exp_le_exp.mpr (neg_le_neg (uLow_sound hj.le hx.1))
  exact ⟨el.trans hL, hH.trans eh⟩

private theorem eHalfBox_sound {j : ℕ} (hj : j < 1051) {x : ℝ}
    (hx : x ∈ Icc (QuarticGrid.node j:ℝ) (QuarticGrid.node (j+1):ℝ)) :
    Contains (eHalfBox j) (Real.exp (x/2)) := by
  have he (i : ℕ) (hi : i ≤ 1051) : Contains (expBox (QuarticGrid.node i/2))
      (Real.exp ((QuarticGrid.node i:ℝ)/2)) := by
    have h := expBox_spec (q := QuarticGrid.node i/2) (by
      exact div_nonneg (node_nonneg i) (by norm_num)) (by linarith only [node_le hi])
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hL := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hx.1 h2)
  have hH := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hx.2 h2)
  have el := contains_lo (he j hj.le)
  have eh := contains_hi (he (j+1) (Nat.succ_le_of_lt hj))
  exact ⟨el.trans hL, hH.trans eh⟩

theorem checkCell_sound {j : ℕ} (hj : j < 1051) (hc : checkCell j = true)
    (hcount : binCount actualBins = 33554431) (hbins : BinsCorrect 0 actualBins)
    (hfinal : prefixSum 33554432 = 17505)
    (hprefix : ∀ j, 0 < j → j ≤ 33554432 → 1 ≤ prefixSum j) {x : ℝ}
    (hx : x ∈ Icc (QuarticGrid.node j:ℝ) (QuarticGrid.node (j+1):ℝ)) :
    (QuarticGrid.lowerK j:ℝ) ≤ kernel x ∧ kernel x ≤ (QuarticGrid.upperK j:ℝ) := by
  simp only [checkCell, decide_eq_true_eq] at hc
  obtain ⟨huLo,huHi,hr,ht,hkLo,hkHi⟩ := hc
  have hb := rBox_sound hj hx huLo huHi
  have he := eHalfBox_sound hj hx
  have hd := thetaBox_sound (div_pos (Real.exp_pos _) scale_pos) hb hr actualBins hcount
    hbins hfinal hprefix
  have htn : 0 ≤ ((thetaBox (rBox j) actualBins).1:ℝ) := by exact_mod_cast ht
  have hL : (QuarticGrid.lowerK j:ℝ) ≤
      ((eHalfBox j).lo:ℝ)/precision * ((thetaBox (rBox j) actualBins).1:ℝ) := by
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).mpr hkLo
  have hH : ((eHalfBox j).hi:ℝ)/precision * ((thetaBox (rBox j) actualBins).2:ℝ) ≤
      (QuarticGrid.upperK j:ℝ) := by
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).mpr hkHi
  unfold kernel
  exact ⟨hL.trans (mul_le_mul (contains_lo he) hd.1 htn (Real.exp_pos _).le),
    (mul_le_mul (contains_hi he) hd.2 (htn.trans hd.1) (by positivity)).trans hH⟩

def checkCoreCells : Bool :=
  (List.range 1051).all checkCell

def checkCoreCellRange (first count : ℕ) : Bool :=
  (List.range count).all (fun i => checkCell (first+i))

theorem checkCoreCellRange_succ (first count : ℕ)
    (hprefix : checkCoreCellRange first count = true)
    (hlast : checkCoreCellRange (first+count) 1 = true) :
    checkCoreCellRange first (count+1) = true := by
  unfold checkCoreCellRange at *
  rw [List.range_succ, List.all_append, Bool.and_eq_true]
  exact ⟨hprefix, by simpa using hlast⟩

theorem checkCoreCells_of_ranges
    (h : ∀ k < 66, checkCoreCellRange (16*k) (min 16 (1051-16*k)) = true) :
    checkCoreCells = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hj' := List.mem_range.mp hj
  have hq : j/16 < 66 := by omega
  have hr : j % 16 < min 16 (1051-16*(j/16)) := by omega
  have hc := List.all_eq_true.mp (h (j/16) hq) (j%16) (List.mem_range.mpr hr)
  simpa only [show 16*(j/16)+j%16 = j by omega] using hc

theorem checkCoreCells_sound (h : checkCoreCells = true)
    (hcount : binCount actualBins = 33554431) (hbins : BinsCorrect 0 actualBins)
    (hfinal : prefixSum 33554432 = 17505)
    (hprefix : ∀ j, 0 < j → j ≤ 33554432 → 1 ≤ prefixSum j) :
    GaussianSideSign.Certificate (mellin (fun x : ℝ => (theta (x/scale) : ℂ))) kernel := by
  apply assemble_mellin_from_cells
  intro j hj x hx
  have hc := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  exact checkCell_sound hj hc hcount hbins hfinal hprefix hx

#print axioms checkCoreCells_sound
#print axioms checkCoreCells_of_ranges

end QuarticKernel
