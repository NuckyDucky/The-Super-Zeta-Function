import QuarticIntegrable
import QuarticPrefix
import QuarticMellin

open MeasureTheory Set

namespace QuarticKernel

private theorem tail_in_full : Ioi (18 : ℝ) ⊆ Ici 0 := fun x hx => by
  rw [mem_Ici]
  linarith [mem_Ioi.mp hx]

private theorem bounded_in_full : Icc (0 : ℝ) 18 ⊆ Ici 0 := fun _ hx => hx.1

private theorem split_integral {f : ℝ → ℝ} (hf : IntegrableOn f (Ici 0)) :
    (∫ x in Ici 0, f x) = (∫ x in Icc (0 : ℝ) 18, f x) + ∫ x in Ioi (18 : ℝ), f x := by
  have hdis : Disjoint (Icc (0:ℝ) 18) (Ioi 18) :=
    Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy)
  rw [← Icc_union_Ioi_eq_Ici (by norm_num : (0:ℝ) ≤ 18)]
  exact setIntegral_union hdis measurableSet_Ioi (hf.mono_set bounded_in_full)
    (hf.mono_set tail_in_full)

private theorem dominate_tail {f : ℝ → ℝ} (hf : IntegrableOn f (Ici 0))
    (hm : ∀ x ∈ Ioi (18 : ℝ), ‖f x‖ ≤ mass x * Real.exp (x/20)) :
    |∫ x in Ioi (18 : ℝ), f x| < (1 : ℝ)/10^10 := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm f).trans_lt ?_
  exact (setIntegral_mono_on (hf.mono_set tail_in_full).norm weighted_tail.1 measurableSet_Ioi
    hm).trans_lt weighted_tail.2

private theorem mass_nonneg_on_tail {x : ℝ} (hx : x ∈ Ioi (18 : ℝ)) : 0 ≤ mass x := by
  have hh : 18 ≤ x := (mem_Ioi.mp hx).le
  have hk := kernel_pos_on_tail hh
  unfold mass
  positivity

private theorem tail_exp_ge_one {x : ℝ} (hx : x ∈ Ioi (18 : ℝ)) : 1 ≤ Real.exp (x/20) :=
  Real.one_le_exp_iff.mpr (by linarith [mem_Ioi.mp hx])

theorem mass_tail_lt : |∫ x in Ioi (18 : ℝ), mass x| < (1 : ℝ)/10^10 := by
  refine dominate_tail mass_integrable fun x hx => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mass_nonneg_on_tail hx)]
  simpa using mul_le_mul_of_nonneg_left (tail_exp_ge_one hx) (mass_nonneg_on_tail hx)

theorem line_tail_lt (t : ℝ) :
    |∫ x in Ioi (18 : ℝ), mass x * GaussianSideIntegral.sinc (t*x)| < (1 : ℝ)/10^10 := by
  refine dominate_tail (sinc_mass_integrable t) fun x hx => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mass_nonneg_on_tail hx)]
  exact mul_le_mul_of_nonneg_left ((GaussianSideIntegral.abs_sinc_le_one _).trans
    (tail_exp_ge_one hx)) (mass_nonneg_on_tail hx)

/-- Exact remaining obligations for the rectangle certificate. The compact
integral estimates and the identification of the continued function are
explicit premises. The code checks the infinite tails. -/
theorem assemble_from_core (Λ : ℂ → ℂ)
    (representation : ∀ a t : ℝ, |a| ≤ 1/20 → |t| ≤ 27/100 →
      Λ (GaussianSideSign.point a t) = SuperZeta.PinchRadius.halfMellin kernel ⟨a,t⟩)
    (positive_core : ∀ x ∈ Icc (0 : ℝ) 13, 0 ≤ kernel x)
    (line_core : ∀ t : ℝ, |t| ≤ 27/100 →
      519994 + (1 : ℝ)/10^10 < ∫ x in Icc (0 : ℝ) 18,
        mass x * GaussianSideIntegral.sinc (t*x))
    (curvature_core : (∫ x in Icc (0 : ℝ) 18, mass x) ≤ 3565602 - (1 : ℝ)/10^10) :
    GaussianSideSign.Certificate Λ kernel := by
  refine {
    representation := representation
    kernel_nonneg := ?_
    mass_integrable := mass_integrable
    theta_tail := fun x hx => kernel_upper_on_tail (mem_Ioi.mp hx).le
    base_integrable := fun t _ => sinc_mass_integrable t
    slope_integrable := fun _ t ha _ => sinhc_sinc_mass_integrable ha t
    complex_integrable := fun _ t ha _ => complex_integrable ha t
    line_floor := ?_
    curvature := ?_ }
  · intro x hx
    by_cases h : x ≤ 13
    · exact positive_core x ⟨hx,h⟩
    · exact (kernel_pos_after_13 (le_of_not_ge h)).le
  · intro t ht
    change (519994 : ℝ) < ∫ x in Ici (0 : ℝ), mass x * GaussianSideIntegral.sinc (t*x)
    rw [split_integral (sinc_mass_integrable t)]
    have hh := (abs_lt.mp (line_tail_lt t)).1
    linarith [line_core t ht]
  · change (∫ x in Ici (0 : ℝ), mass x) ≤ 3565602
    rw [split_integral mass_integrable]
    have hh := (abs_lt.mp mass_tail_lt).2
    linarith

#check @assemble_from_core
#print axioms mass_tail_lt
#print axioms line_tail_lt
#print axioms assemble_from_core

end QuarticKernel
