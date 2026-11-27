import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv

namespace FieldTarget

open Complex Set

private theorem affineProjection_hasDerivAt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c v : ℂ) (P : ℂ →L[ℝ] ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ P (f ((s : ℂ) * v + c)))
      (P (deriv f ((t : ℂ) * v + c) * v)) t := by
  let g (z : ℂ) := z * v + c
  have hg : HasDerivAt g v (t : ℂ) := by
    simpa only [id, one_mul] using
      (((hasDerivAt_id (t : ℂ)).mul_const v).add_const c)
  have h := ((hf (g (t : ℂ))).hasDerivAt.comp (t : ℂ) hg).comp_ofReal
  exact P.hasFDerivAt.comp_hasDerivAt t h

private theorem horizontalIm_hasDerivAt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (x y : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (f ⟨s, y⟩).im) (deriv f ⟨x, y⟩).im x := by
  have hPoint (s : ℝ) : (s : ℂ) + (y : ℂ) * I = ⟨s, y⟩ := by
    apply Complex.ext <;> simp
  simpa only [hPoint, Complex.imCLM_apply, mul_one] using
    affineProjection_hasDerivAt hf ((y : ℂ) * I) 1 Complex.imCLM x

private theorem verticalRe_hasDerivAt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (f ⟨x, t⟩).re) (-(deriv f ⟨x, y⟩).im) y := by
  have hPoint (t : ℝ) : (t : ℂ) * I + (x : ℂ) = ⟨x, t⟩ := by
    apply Complex.ext <;> simp
  simpa only [hPoint, Complex.reCLM_apply, Complex.mul_I_re] using
    affineProjection_hasDerivAt hf (x : ℂ) I Complex.reCLM y

/-- A positive imaginary derivative in the middle of the band makes the
horizontal imaginary reading strictly increasing and the vertical real
reading strictly decreasing. The two real signs at the ends then give one
simple zero on the line. -/
theorem strip_zero_unique_of_signed_bands {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {start a b finish : ℝ} (hstart : start ≤ a) (hab : a < b) (hfinish : b ≤ finish)
    (hBelow : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc start a → 0 < (f w).re)
    (hAbove : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc b finish → (f w).re < 0)
    (hSlope : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc a b → 0 < (deriv f w).im)
    (hReal : ∀ t ∈ Icc a b, (f ⟨1 / 2, t⟩).im = 0) :
    ∃ t ∈ Ioo a b, analyticOrderNatAt f ⟨1 / 2, t⟩ = 1 ∧
      ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc start finish →
        (f w = 0 ↔ w = ⟨1 / 2, t⟩) := by
  let onLine (t : ℝ) := (f ⟨1 / 2, t⟩).re
  have hHalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hCont : Continuous onLine := continuous_iff_continuousAt.mpr fun t ↦
    (verticalRe_hasDerivAt hf (1 / 2) t).continuousAt
  have hAnti : StrictAntiOn onLine (Icc a b) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a b) hCont.continuousOn (fun u hu ↦ ?_)
    change deriv (fun t : ℝ ↦ (f ⟨1 / 2, t⟩).re) u < 0
    rw [(verticalRe_hasDerivAt hf (1 / 2) u).deriv]
    exact neg_lt_zero.mpr (hSlope ⟨1 / 2, u⟩ hHalf (interior_subset hu))
  have hA : 0 < onLine a := hBelow ⟨1 / 2, a⟩ hHalf ⟨hstart, le_rfl⟩
  have hB : onLine b < 0 := hAbove ⟨1 / 2, b⟩ hHalf ⟨le_rfl, hfinish⟩
  obtain ⟨t, ht, htRe⟩ := intermediate_value_Ioo' hab.le hCont.continuousOn
    (show (0 : ℝ) ∈ Ioo (onLine b) (onLine a) from ⟨hB, hA⟩)
  have htc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have htZero : f ⟨1 / 2, t⟩ = 0 := Complex.ext htRe (hReal t htc)
  have htDeriv : deriv f ⟨1 / 2, t⟩ ≠ 0 := by
    intro h
    have ha := hSlope ⟨1 / 2, t⟩ hHalf htc
    rwa [h, Complex.zero_im, lt_self_iff_false] at ha
  refine ⟨t, ht, ?_, fun w hw htBand ↦ ?_⟩
  · rw [analyticOrderNatAt,
      (hf.analyticAt _).analyticOrderAt_eq_one_of_zero_deriv_ne_zero htZero htDeriv]
    rfl
  constructor
  · intro hwZero
    have htm : w.im ∈ Icc a b := by
      constructor
      · by_contra! hh
        have h := hBelow w hw ⟨htBand.1, hh.le⟩
        rwa [hwZero, Complex.zero_re, lt_self_iff_false] at h
      · by_contra! hh
        have h := hAbove w hw ⟨hh.le, htBand.2⟩
        rwa [hwZero, Complex.zero_re, lt_self_iff_false] at h
    let row (x : ℝ) := (f ⟨x, w.im⟩).im
    have hRow : StrictMonoOn row (Icc (0 : ℝ) 1) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
        (fun x _ ↦ (horizontalIm_hasDerivAt hf x w.im).continuousAt.continuousWithinAt)
        (fun x hx ↦ ?_)
      change 0 < deriv (fun s : ℝ ↦ (f ⟨s, w.im⟩).im) x
      rw [(horizontalIm_hasDerivAt hf x w.im).deriv]
      exact hSlope ⟨x, w.im⟩ (interior_subset hx) htm
    have hPoint : (⟨w.re, w.im⟩ : ℂ) = w := Complex.ext rfl rfl
    have hR : row w.re = 0 := by
      change (f ⟨w.re, w.im⟩).im = 0
      rw [hPoint, hwZero, Complex.zero_im]
    have hσ : w.re = 1 / 2 := hRow.injOn hw hHalf (hR.trans (hReal w.im htm).symm)
    have htEq : w.im = t := hAnti.injOn htm htc (by
      change (f ⟨1 / 2, w.im⟩).re = (f ⟨1 / 2, t⟩).re
      calc
        _ = (f ⟨w.re, w.im⟩).re := by rw [hσ]
        _ = 0 := by rw [hPoint, hwZero, Complex.zero_re]
        _ = _ := htRe.symm)
    exact Complex.ext hσ htEq
  · rintro rfl
    exact htZero

#check @strip_zero_unique_of_signed_bands
#print axioms strip_zero_unique_of_signed_bands

end FieldTarget
