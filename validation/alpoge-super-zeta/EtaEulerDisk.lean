import EtaEulerSum
import EtaGammaBound
import NativeDottieEtaContour
import Mathlib.Analysis.Complex.Liouville

/-! Explicit uniform errors for both finite eta readings on the original disk. -/

noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex Metric Set

private theorem eta_rectangle_error {w : ℂ} (hlo : 1/4 ≤ w.re) (hhi : w.re ≤ 3/4)
    (hi : 0 < w.im) (hmax : w.im ≤ 15) :
    ‖EtaMellin.eta w - EtaMellin.etaEulerSum 128 w‖ ≤ 1/10^14 := by
  have hr : 0 < w.re := by linarith
  have hg := EtaMellin.gamma_real_le_four hlo (hhi.trans (by norm_num))
  have hm := EtaMellin.gamma_inv_norm_le hlo hhi
  have he : Real.exp (Real.pi*|w.im|) ≤ (3:ℝ)^48 := by
    have ht : Real.pi*|w.im| ≤ 48 := by
      rw [abs_of_pos hi]
      have hmul := mul_le_mul Real.pi_lt_d4.le hmax hi.le (by norm_num : (0:ℝ) ≤ 3.1416)
      linarith only [hmul]
    calc
      _ ≤ Real.exp 48 := Real.exp_le_exp.mpr ht
      _ = (Real.exp 1)^48 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le
        (Real.exp_one_lt_d9.le.trans (by norm_num)) _
  have hg0 := (Real.Gamma_pos_of_pos hr).le
  have hcases := EtaMellin.eta_eulerSum_error 128 hr hi
  rw [div_eq_mul_inv] at hcases
  calc
    _ ≤ (1/2:ℝ)^128 * Real.Gamma w.re * ‖Complex.Gamma w‖⁻¹ := hcases
    _ ≤ (1/2:ℝ)^128 * 4 * (4 * (3:ℝ)^48) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hg (by positivity)) ?_ (by positivity) (by positivity)
      exact hm.trans (mul_le_mul_of_nonneg_left he (by norm_num))
    _ ≤ _ := by norm_num

def etaDiskApprox (s : ℂ) : ℂ := EtaMellin.etaEulerSum 128 (2*s)

theorem etaDiskApprox_entire : Differentiable ℂ etaDiskApprox :=
  (EtaMellin.etaEulerSum_entire 128).comp (by fun_prop)

private theorem enlarged_disk_coordinates {s : ℂ} (hs : ‖s-firstCenter‖ ≤ 1/32) :
    1/4 ≤ (2*s).re ∧ (2*s).re ≤ 3/4 ∧ 0 < (2*s).im ∧ (2*s).im ≤ 15 := by
  have hR := (Complex.abs_re_le_norm (s-firstCenter)).trans hs
  have hI := (Complex.abs_im_le_norm (s-firstCenter)).trans hs
  change |s.re-1/4| ≤ 1/32 at hR
  change |s.im-7067363/1000000| ≤ 1/32 at hI
  obtain ⟨hRl,hRu⟩ := abs_le.mp hR
  obtain ⟨hIl,hIu⟩ := abs_le.mp hI
  simp only [show ∀ z : ℂ, ((2:ℂ)*z).re = 2*z.re by intro z; simp,
    show ∀ z : ℂ, ((2:ℂ)*z).im = 2*z.im by intro z; simp]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem etaDiskApprox_error {s : ℂ} (hs : ‖s-firstCenter‖ ≤ 1/32) :
    ‖doubledEta s - etaDiskApprox s‖ ≤ 1/10^14 := by
  obtain ⟨hlo,hhi,hi,ht⟩ := enlarged_disk_coordinates hs
  exact eta_rectangle_error hlo hhi hi ht

theorem etaDiskApprox_deriv_error {s : ℂ} (hs : s ∈ closedBall firstCenter firstRadius) :
    ‖deriv doubledEta s - deriv etaDiskApprox s‖ ≤ 1/10^12 := by
  let F := fun z => doubledEta z - etaDiskApprox z
  have hdiff : DifferentiableOn ℂ F openSpectralStrip :=
    doubledEta_diff_on_strip.sub etaDiskApprox_entire.differentiableOn
  have hnear {z : ℂ} (hz : z ∈ closedBall s (1/64)) : ‖z-firstCenter‖ ≤ 1/32 := by
    have hzc := dist_triangle z s firstCenter
    rw [← dist_eq_norm]
    have h1 := mem_closedBall.mp hz
    have h2 := mem_closedBall.mp hs
    change dist s firstCenter ≤ 1/4096 at h2
    linarith only [hzc,h1,h2]
  have hD : closedBall s (1/64) ⊆ openSpectralStrip := by
    intro z hz
    have hp := enlarged_disk_coordinates (hnear hz)
    simp only [show ((2:ℂ)*z).re = 2*z.re by simp] at hp
    exact ⟨by linarith only [hp.1], by linarith only [hp.2.1]⟩
  have hd : DiffContOnCl ℂ F (ball s (1/64)) :=
    hdiff.diffContOnCl_ball hD
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0:ℝ) < 1/64) hd
    (fun z hz => etaDiskApprox_error (hnear (sphere_subset_closedBall hz)))
  change ‖deriv (fun z => doubledEta z - etaDiskApprox z) s‖ ≤ _ at h
  rw [deriv_sub (doubledEta_diff_on_strip.differentiableAt
    (openSpectralStrip_open.mem_nhds (firstDisk_in_strip hs))) etaDiskApprox_entire.differentiableAt] at h
  exact h.trans (by norm_num)

#print axioms etaDiskApprox_error
#print axioms etaDiskApprox_deriv_error

end DottieOriented.NativeSpectrum
end
