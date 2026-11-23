import DottieHighGammaTail
import DottieLeftGammaLocal
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The tilted Gamma bound on the horizontal edges of the finite left shift. -/

namespace QuarticModel

open Complex Set SuperZeta.StirlingCorrection
open private norm_gamma_mul_le norm_Gamma_half_le norm_real_add_imag_le
  norm_gamma_add_nat_le from DottieHighGammaTail

private theorem gamma_shift_comparison {q : ℝ} (hlo : 1 ≤ q) (hhi : q ≤ 10) (v : ℝ) :
    ‖Gamma (⟨q,v⟩ : ℂ)‖ ≤ 3*(11+|v|)^10*Real.exp (-(Real.pi/2*|v|)) := by
  let z : ℂ := ⟨q,v⟩
  let h : ℂ := 1/2+(v : ℂ)*I
  have hz : 0 < z.re := (by norm_num : (0 : ℝ) < 1).trans_le hlo
  have hh : 0 < h.re := by norm_num [h, Complex.mul_re, Complex.div_ofNat_re]
  have hGammaHalf : 1 ≤ Real.Gamma (21/2) := by
    have hm : Real.Gamma 2 ≤ Real.Gamma (21/2) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp) (by norm_num [mem_Ici]) (by norm_num)
    simpa only [Real.Gamma_two] using hm
  have hGammaQ : Real.Gamma q ≤ Real.Gamma (21/2) := by
    have hg := Real.convexOn_Gamma.le_max_of_mem_Icc
      (by norm_num [mem_Ioi] : (1 : ℝ) ∈ Ioi 0)
      (by norm_num [mem_Ioi] : (21/2 : ℝ) ∈ Ioi 0)
      (show q ∈ Icc 1 (21/2) from ⟨hlo, by linarith only [hhi]⟩)
    simpa only [Real.Gamma_one, max_eq_right hGammaHalf] using hg
  have hmatch : z + ((21/2-q : ℝ) : ℂ) = h+10 := by
    apply Complex.ext
    · norm_num [z, h, Complex.mul_re, Complex.div_ofNat_re]
    · norm_num [z, h, Complex.mul_im, Complex.div_ofNat_im]
  have hcomp : ‖Gamma z‖ ≤ ‖Gamma (h+10)‖ := by
    have hb := norm_gamma_mul_le hz (d := 21/2-q) (by linarith only [hhi])
    rw [show z.re = q from rfl, show q+(21/2-q) = (21/2 : ℝ) by ring, hmatch] at hb
    have hp : 0 < Real.Gamma (21/2) := (by norm_num : (0 : ℝ) < 1).trans_le hGammaHalf
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      _ ≤ Real.Gamma q * ‖Gamma (h+10)‖ := hb
      _ ≤ Real.Gamma (21/2) * ‖Gamma (h+10)‖ :=
        mul_le_mul_of_nonneg_right hGammaQ (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hnorm : ‖h‖ ≤ 1/2+|v| := by
    simpa [h, ofReal_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)] using
      norm_real_add_imag_le (1/2) v
  have hshift : ‖Gamma (h+10)‖ ≤ (11+|v|)^10*‖Gamma h‖ :=
    norm_gamma_add_nat_le h hh (11+|v|) 10 (by push_cast; linarith only [hnorm])
  calc
    _ ≤ ‖Gamma (h+10)‖ := hcomp
    _ ≤ (11+|v|)^10*‖Gamma h‖ := hshift
    _ ≤ (11+|v|)^10*(3*Real.exp (-(Real.pi/2*|v|))) :=
      mul_le_mul_of_nonneg_left (norm_Gamma_half_le v) (by positivity)
    _ = _ := by ring

/-- A uniform bound for the normalized, tilted Gamma factor along both
horizontal edges of the finite Dottie contour. -/
theorem dottie_lower_gamma_horizontal {σ t x u : ℝ}
    (hσ : σ ∈ Icc (1/2-63/2048 : ℝ) (1/2+63/2048))
    (ht : |t-dottieHeight| ≤ 35/2048) (hx : x ∈ Icc (-7 : ℝ) 1) (hu : |u| ≤ 20) :
    ‖Gamma (⟨σ+x,t+u⟩ : ℂ)‖ * Real.exp (Real.pi*u/2) /
      ‖Gamma (2+(dottieHeight : ℂ)*I)‖ ≤ 4*10^35 := by
  let T := dottieHeight
  let v := t+u
  let z : ℂ := ⟨σ+x,v⟩
  let G := ‖Gamma (2+(T : ℂ)*I)‖
  let C : ℝ := 3*(2^8*(6*10^12)^2)
  have hTlo : 4*10^12 < T := by dsimp only [T]; linarith only [dottieHeight_enclosure.1]
  have hThi : T < 5*10^12 := by dsimp only [T]; linarith only [dottieHeight_enclosure.2]
  have hT : 0 < T := by linarith only [hTlo]
  have hvDiff : |v-T| ≤ 21 := by
    dsimp only [v, T]
    rw [show t+u-dottieHeight = (t-dottieHeight)+u by ring]
    exact (abs_add_le _ _).trans (by linarith only [ht, hu])
  have hvBig : 3*10^12 ≤ v := by linarith only [hTlo, (abs_le.mp hvDiff).1]
  have hvSum : 11+v ≤ 6*10^12 := by linarith only [hThi, (abs_le.mp hvDiff).2]
  have hv : 0 < v := by linarith only [hvBig]
  have hden : Real.exp (-(Real.pi/2*T)) ≤ G := by
    simpa only [abs_of_pos hT] using dottie_exp_neg_le_norm_Gamma_two T
  have hG : 0 < G := (Real.exp_pos _).trans_le hden
  have hrec := dottie_gamma_norm_recurrence z hv.ne' 8
  have he : z+(8 : ℕ) = (⟨σ+x+8,v⟩ : ℂ) := by
    apply Complex.ext <;> norm_num [z, Complex.add_re, Complex.add_im]
  rw [he, show z.im = v from rfl, abs_of_pos hv] at hrec
  have hshift := gamma_shift_comparison (q := σ+x+8)
    (by linarith only [hσ.1, hx.1]) (by linarith only [hσ.2, hx.2]) v
  rw [abs_of_pos hv] at hshift
  have hraw : ‖Gamma z‖ ≤ 3*(11+v)^10*Real.exp (-(Real.pi/2*v))/v^8 := by
    apply (le_div_iff₀ (pow_pos hv _)).2
    rw [mul_comm]
    exact hrec.trans hshift
  have hpoly : (11+v)^10/v^8 ≤ (2 : ℝ)^8*(6*10^12)^2 := by
    apply (div_le_iff₀ (pow_pos hv _)).2
    calc
      _ = (11+v)^8*(11+v)^2 := by ring
      _ ≤ (2*v)^8*(6*10^12)^2 := by
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith only [hvBig]) 8)
          (pow_le_pow_left₀ (by positivity) hvSum 2) (by positivity) (by positivity)
      _ = _ := by ring
  have hraw' : ‖Gamma z‖ ≤ C*Real.exp (-(Real.pi/2*v)) := by
    calc
      _ ≤ _ := hraw
      _ = 3*((11+v)^10/v^8)*Real.exp (-(Real.pi/2*v)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly (by norm_num)) (Real.exp_pos _).le
  have htilt : Real.exp (-(Real.pi/2*v))*Real.exp (Real.pi*u/2)/G ≤ 3 := by
    apply (div_le_iff₀ hG).2
    rw [← Real.exp_add]
    have hgap : T-t ≤ 35/2048 := by dsimp only [T]; linarith only [(abs_le.mp ht).1]
    have hgap' : Real.pi/2*(T-t) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hgap (by positivity)).trans (by linarith only [Real.pi_lt_four])
    calc
      _ = Real.exp (-(Real.pi/2*T)+Real.pi/2*(T-t)) := by congr 1; dsimp only [v]; ring
      _ ≤ Real.exp (-(Real.pi/2*T)+1) := Real.exp_le_exp.mpr (by linarith only [hgap'])
      _ = Real.exp 1*Real.exp (-(Real.pi/2*T)) := by rw [add_comm, Real.exp_add]
      _ ≤ 3*G := mul_le_mul Real.exp_one_lt_three.le hden (Real.exp_pos _).le (by norm_num)
  change ‖Gamma z‖ * Real.exp (Real.pi*u/2) / G ≤ _
  calc
    _ ≤ (C*Real.exp (-(Real.pi/2*v)))*Real.exp (Real.pi*u/2)/G :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hraw' (Real.exp_pos _).le) hG.le
    _ = C*(Real.exp (-(Real.pi/2*v))*Real.exp (Real.pi*u/2)/G) := by ring
    _ ≤ C*3 := mul_le_mul_of_nonneg_left htilt (by dsimp only [C]; positivity)
    _ ≤ _ := by norm_num [C]

#print axioms dottie_lower_gamma_horizontal

end QuarticModel
