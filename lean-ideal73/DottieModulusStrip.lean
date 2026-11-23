import DottieHeightCalibration

/-! The log-modulus coordinate for a marked return's Mellin phase. The
period and absolute winding are supplied by the orbit certificate. -/

namespace SuperZeta.StirlingCorrection

open Real
noncomputable section

def dottieLogModulus (x y : ℝ) : ℝ := log (1+(x/y)^2)/2

theorem dottie_log_modulus_eq_log_ratio (x : ℝ) {y : ℝ} (hy : 0 < y) :
    dottieLogModulus x y = log (‖(⟨x,y⟩ : ℂ)‖/y) := by
  have hs : (‖(⟨x,y⟩ : ℂ)‖/y)^2 = 1+(x/y)^2 := by
    rw [div_pow, Complex.sq_norm, Complex.normSq_apply]
    change (x*x+y*y)/y^2 = 1+(x/y)^2
    field_simp
    ring
  rw [dottieLogModulus, ← hs, Real.log_pow]
  push_cast
  ring

def dottieModulusHeight (p k : ℕ) (d : ℝ) : ℝ :=
  (2*π*(k:ℝ)/(p:ℝ))/d

theorem dottie_archived_height_from_modulus (x : ℝ) :
    dottieModulusHeight 320 1 (dottieLogModulus x archivedDottieMidIm) =
      dottieHeightAtFlank x := by
  unfold dottieModulusHeight dottieLogModulus dottieHeightAtFlank dottieFlankRatio
  norm_num
  ring

/-- A closed height window is exactly an interval in the log-modulus
coordinate, with reversed endpoints. -/
theorem dottie_height_mem_iff_modulus_strip {p k : ℕ} {d a b : ℝ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) :
    dottieModulusHeight p k d ∈ Set.Icc a b ↔
      d ∈ Set.Icc ((2*π*(k:ℝ)/(p:ℝ))/b) ((2*π*(k:ℝ)/(p:ℝ))/a) := by
  rw [Set.mem_Icc, Set.mem_Icc, dottieModulusHeight,
    le_div_iff₀ hd, div_le_iff₀ hd, div_le_iff₀ hb, le_div_iff₀ ha]
  constructor <;> rintro ⟨hl,hu⟩ <;> exact ⟨by linarith [mul_comm b d], by linarith [mul_comm a d]⟩

/-- At fixed period and winding the inverse-square zoom estimate has a
uniform additive error smaller than 2π per marked arrow. -/
theorem dottie_modulus_height_zoom_bounds {p k : ℕ} {x y : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hx : x ≠ 0) (hy : 0 < y) :
    let q := (x/y)^2
    let H₀ := 4*π*(k:ℝ)/(p:ℝ)/q
    H₀ ≤ dottieModulusHeight p k (dottieLogModulus x y) ∧
      dottieModulusHeight p k (dottieLogModulus x y) < H₀ + 2*π*(k:ℝ)/(p:ℝ) := by
  intro q H₀
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hq : 0 < q := sq_pos_of_ne_zero (div_ne_zero hx hy.ne')
  have hlog : 0 < log (1+q) := log_pos (by linarith)
  have hupper : log (1+q) ≤ q := by
    linarith [log_le_sub_one_of_pos (show 0 < 1+q by linarith)]
  have hlower := lt_log_one_add_of_pos hq
  let c := 4*π*(k:ℝ)/(p:ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have he : dottieModulusHeight p k (dottieLogModulus x y) = c/log (1+q) := by
    dsimp [dottieModulusHeight, dottieLogModulus, c, q]
    ring
  rw [he]
  change c/q ≤ c/log (1+q) ∧ c/log (1+q) < c/q + 2*π*(k:ℝ)/(p:ℝ)
  constructor
  · exact div_le_div_of_nonneg_left hc.le hlog hupper
  · have hpos : 0 < 2*q/(q+2) := by positivity
    calc
      c/log (1+q) < c/(2*q/(q+2)) := div_lt_div_of_pos_left hc hpos hlower
      _ = c/q + 2*π*(k:ℝ)/(p:ℝ) := by
        dsimp [c]
        have hq2 : q+2 ≠ 0 := by positivity
        field_simp
        ring

#print axioms dottie_log_modulus_eq_log_ratio
#print axioms dottie_archived_height_from_modulus
#print axioms dottie_height_mem_iff_modulus_strip
#print axioms dottie_modulus_height_zoom_bounds

end
end SuperZeta.StirlingCorrection
