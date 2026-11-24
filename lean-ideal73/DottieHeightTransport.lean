import DottieModulusStrip

/-! Inversion of the archived one-turn height rule at fixed positive `y`.
The horizontal interval is an input. An orbit certificate can supply it
after establishing the marked return period and winding on that interval. -/

namespace SuperZeta.StirlingCorrection

open Real
noncomputable section

def dottieFlankHeight (y x : ℝ) : ℝ :=
  2 * π / (160 * log (1 + (x / y) ^ 2))

def dottieFlankAtHeight (y T : ℝ) : ℝ :=
  y * sqrt (exp (2 * π / (160 * T)) - 1)

theorem dottieFlankHeight_archived :
    dottieFlankHeight 0.509892982511772 0.00000004749479070945369 = dottieHeight := rfl

theorem dottieFlankAtHeight_pos {y T : ℝ} (hy : 0 < y) (hT : 0 < T) :
    0 < dottieFlankAtHeight y T := by
  have hr : 0 < 2 * π / (160 * T) := div_pos (by positivity) (by positivity)
  unfold dottieFlankAtHeight
  exact mul_pos hy (sqrt_pos.2 (sub_pos.mpr (Real.one_lt_exp_iff.2 hr)))

theorem dottieFlankHeight_inverse {y T : ℝ} (hy : 0 < y) (hT : 0 < T) :
    dottieFlankHeight y (dottieFlankAtHeight y T) = T := by
  have hr : 0 < 2 * π / (160 * T) := div_pos (by positivity) (by positivity)
  have hs : 0 ≤ exp (2 * π / (160 * T)) - 1 :=
    sub_nonneg.mpr (Real.one_lt_exp_iff.2 hr).le
  unfold dottieFlankHeight dottieFlankAtHeight
  rw [show y * sqrt (exp (2 * π / (160 * T)) - 1) / y =
      sqrt (exp (2 * π / (160 * T)) - 1) by field_simp [hy.ne'],
    sq_sqrt hs, show ∀ a : ℝ, 1 + (a - 1) = a by intro a; ring, log_exp]
  field_simp [hT.ne', Real.pi_ne_zero]

theorem dottieFlankHeight_strictAntiOn {y : ℝ} (hy : 0 < y) :
    StrictAntiOn (dottieFlankHeight y) (Set.Ioi 0) := by
  intro a ha b _ hab
  have ha' : 0 < a := ha
  have hq : 0 < a / y := div_pos ha' hy
  have hq' : a / y < b / y := (div_lt_div_iff_of_pos_right hy).2 hab
  have hs : (a / y) ^ 2 < (b / y) ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hq') (add_pos hq (hq.trans hq'))]
  have hlogPos : 0 < log (1 + (a / y) ^ 2) :=
    log_pos (by linarith only [pow_pos hq 2])
  have hlogLt : log (1 + (a / y) ^ 2) < log (1 + (b / y) ^ 2) :=
    log_lt_log (by positivity) (by linarith only [hs])
  exact div_lt_div_of_pos_left (mul_pos (by norm_num) pi_pos)
    (mul_pos (by norm_num) hlogPos) (mul_lt_mul_of_pos_left hlogLt (by norm_num))

/-- A certified positive interval of flank coordinates covers precisely the
height interval with reversed endpoints. -/
theorem dottieFlankAtHeight_mem_iff {y lo hi T : ℝ}
    (hy : 0 < y) (hlo : 0 < lo) (hhi : 0 < hi) (hT : 0 < T) :
    dottieFlankAtHeight y T ∈ Set.Icc lo hi ↔
      T ∈ Set.Icc (dottieFlankHeight y hi) (dottieFlankHeight y lo) := by
  have hanti := dottieFlankHeight_strictAntiOn hy
  have hx := dottieFlankAtHeight_pos hy hT
  have hleft := hanti.le_iff_ge (a := hi) (b := dottieFlankAtHeight y T) hhi hx
  have hright := hanti.le_iff_ge (a := dottieFlankAtHeight y T) (b := lo) hx hlo
  rw [dottieFlankHeight_inverse hy hT] at hleft hright
  exact ⟨fun h => ⟨hleft.mpr h.2, hright.mpr h.1⟩,
    fun h => ⟨hright.mp h.2, hleft.mp h.1⟩⟩

abbrev dottieFlankWitnessY : ℝ := archivedDottieMidIm
abbrev dottieFlankWitnessX : ℝ := archivedDottieFlank
def dottieFlankWidth : ℝ := 1/10^12

private theorem log_one_add_enclosure {z : ℝ} (hz : 0 ≤ z) :
    z/(1+z) ≤ log (1+z) ∧ log (1+z) ≤ z := by
  have h : 0 < 1+z := by linarith
  rw [show z/(1+z) = 1-(1+z)⁻¹ by field_simp [h.ne']; ring]
  exact ⟨one_sub_inv_le_log_of_pos h, by linarith [log_le_sub_one_of_pos h]⟩

private theorem dottieFlankHeight_right_endpoint :
    dottieFlankHeight dottieFlankWitnessY (dottieFlankWitnessX+dottieFlankWidth) <
      4526019322477 := by
  let z := ((dottieFlankWitnessX+dottieFlankWidth)/dottieFlankWitnessY)^2
  have hp : 0 < z := by norm_num [z,dottieFlankWitnessX,dottieFlankWitnessY,dottieFlankWidth]
  have hl := (log_one_add_enclosure hp.le).1
  have hlog : 0 < log (1+z) := log_pos (by linarith)
  change 2*π/(160*log (1+z)) < _
  apply (div_lt_iff₀ (mul_pos (by norm_num) hlog)).2
  calc
    2*π < 2*3.14159265358979323847 := by linarith [Real.pi_lt_d20]
    _ < 4526019322477*(160*(z/(1+z))) := by
      norm_num [z,dottieFlankWitnessX,dottieFlankWitnessY,dottieFlankWidth]
    _ ≤ _ := by gcongr

private theorem dottieFlankHeight_left_endpoint :
    4526219322478 <
      dottieFlankHeight dottieFlankWitnessY (dottieFlankWitnessX-dottieFlankWidth) := by
  let z := ((dottieFlankWitnessX-dottieFlankWidth)/dottieFlankWitnessY)^2
  have hp : 0 < z := by norm_num [z,dottieFlankWitnessX,dottieFlankWitnessY,dottieFlankWidth]
  have hh := (log_one_add_enclosure hp.le).2
  have hlog : 0 < log (1+z) := log_pos (by linarith)
  change _ < 2*π/(160*log (1+z))
  apply (lt_div_iff₀ (mul_pos (by norm_num) hlog)).2
  calc
    _ ≤ 4526219322478*(160*z) := by gcongr
    _ < 2*3.14159265358979323846 := by
      norm_num [z,dottieFlankWitnessX,dottieFlankWitnessY,dottieFlankWidth]
    _ < 2*π := by linarith [Real.pi_gt_d20]

/-- This horizontal flank interval covers a closed height band of radius
one hundred million around the original reference height. -/
theorem dottieFlankAtHeight_witness_band {T : ℝ}
    (hT : T ∈ Set.Icc (dottieHeight-10^8) (dottieHeight+10^8)) :
    dottieFlankAtHeight dottieFlankWitnessY T ∈
      Set.Icc (dottieFlankWitnessX-dottieFlankWidth)
        (dottieFlankWitnessX+dottieFlankWidth) := by
  obtain ⟨hlo,hhi⟩ := hT
  obtain ⟨hDlo,hDhi⟩ := dottieHeight_enclosure
  have hTpos : 0 < T := by linarith only [hlo,hDlo]
  apply (dottieFlankAtHeight_mem_iff (by norm_num [dottieFlankWitnessY])
    (by norm_num [dottieFlankWitnessX,dottieFlankWidth])
    (by norm_num [dottieFlankWitnessX,dottieFlankWidth]) hTpos).2
  exact ⟨by linarith only [hlo,hDlo,dottieFlankHeight_right_endpoint],
    by linarith only [hhi,hDhi,dottieFlankHeight_left_endpoint]⟩

#print axioms dottieFlankHeight_archived
#print axioms dottieFlankHeight_inverse
#print axioms dottieFlankHeight_strictAntiOn
#print axioms dottieFlankAtHeight_mem_iff
#print axioms dottieFlankAtHeight_witness_band

end
end SuperZeta.StirlingCorrection
