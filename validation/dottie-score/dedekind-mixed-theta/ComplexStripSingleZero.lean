import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv

namespace FieldTarget

open Complex Set

private theorem affineProjection_hasDerivAt {f : ℂ → ℂ}
    (c v : ℂ) (P : ℂ →L[ℝ] ℝ) (t : ℝ) (hf : DifferentiableAt ℂ f ((t : ℂ) * v + c)) :
    HasDerivAt (fun s : ℝ ↦ P (f ((s : ℂ) * v + c)))
      (P (deriv f ((t : ℂ) * v + c) * v)) t := by
  let g (z : ℂ) := z * v + c
  have hg : HasDerivAt g v (t : ℂ) := by
    simpa only [id, one_mul] using
      (((hasDerivAt_id (t : ℂ)).mul_const v).add_const c)
  have h := (hf.hasDerivAt.comp (t : ℂ) hg).comp_ofReal
  exact P.hasFDerivAt.comp_hasDerivAt t h

private theorem horizontalIm_hasDerivAt {f : ℂ → ℂ} {x y : ℝ}
    (hf : DifferentiableAt ℂ f ⟨x, y⟩) :
    HasDerivAt (fun s : ℝ ↦ (f ⟨s, y⟩).im) (deriv f ⟨x, y⟩).im x := by
  have hPoint (s : ℝ) : (s : ℂ) + (y : ℂ) * I = ⟨s, y⟩ := by
    apply Complex.ext <;> simp
  simpa only [hPoint, Complex.imCLM_apply, mul_one] using
    affineProjection_hasDerivAt ((y : ℂ) * I) 1 Complex.imCLM x
      (by simpa only [mul_one, hPoint] using hf)

private theorem verticalRe_hasDerivAt {f : ℂ → ℂ} {x y : ℝ}
    (hf : DifferentiableAt ℂ f ⟨x, y⟩) :
    HasDerivAt (fun t : ℝ ↦ (f ⟨x, t⟩).re) (-(deriv f ⟨x, y⟩).im) y := by
  have hPoint (t : ℝ) : (t : ℂ) * I + (x : ℂ) = ⟨x, t⟩ := by
    apply Complex.ext <;> simp
  simpa only [hPoint, Complex.reCLM_apply, Complex.mul_I_re] using
    affineProjection_hasDerivAt (x : ℂ) I Complex.reCLM y
      (by simpa only [hPoint] using hf)

/-- Opposite real endpoint signs and one signed imaginary derivative give
exactly one simple zero in a rectangle, on the line where the reading is real. -/
theorem unique_simple_zero_of_signed_crossing {f : ℂ → ℂ} {l σ r a b direction : ℝ}
    (hf : ∀ w : ℂ, w.re ∈ Icc l r → w.im ∈ Icc a b → AnalyticAt ℂ f w)
    (hσ : σ ∈ Icc l r) (hab : a < b)
    (hA : 0 < direction * (f ⟨σ, a⟩).re)
    (hB : direction * (f ⟨σ, b⟩).re < 0)
    (hSlope : ∀ w : ℂ, w.re ∈ Icc l r → w.im ∈ Icc a b →
      0 < direction * (deriv f w).im)
    (hReal : ∀ t ∈ Icc a b, (f ⟨σ, t⟩).im = 0) :
    ∃ t ∈ Ioo a b, analyticOrderNatAt f ⟨σ, t⟩ = 1 ∧
      ∀ w : ℂ, w.re ∈ Icc l r → w.im ∈ Icc a b → (f w = 0 ↔ w = ⟨σ, t⟩) := by
  have hDir : direction ≠ 0 := by
    rintro rfl
    simp at hA
  let onLine (t : ℝ) := direction * (f ⟨σ, t⟩).re
  have hV (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivAt onLine (direction * -(deriv f ⟨σ, u⟩).im) u :=
    (verticalRe_hasDerivAt (hf ⟨σ, u⟩ hσ hu).differentiableAt).const_mul direction
  have hCont : ContinuousOn onLine (Icc a b) :=
    fun u hu ↦ (hV u hu).continuousAt.continuousWithinAt
  have hAnti : StrictAntiOn onLine (Icc a b) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a b) hCont (fun u hu ↦ ?_)
    rw [(hV u (interior_subset hu)).deriv, mul_neg]
    exact neg_lt_zero.mpr (hSlope ⟨σ, u⟩ hσ (interior_subset hu))
  obtain ⟨t, ht, htRe⟩ := intermediate_value_Ioo' hab.le hCont
    (show (0 : ℝ) ∈ Ioo (onLine b) (onLine a) from ⟨hB, hA⟩)
  have htc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have htZero : f ⟨σ, t⟩ = 0 :=
    Complex.ext ((mul_eq_zero.mp htRe).resolve_left hDir) (hReal t htc)
  have htDeriv : deriv f ⟨σ, t⟩ ≠ 0 := by
    intro h
    have ha := hSlope ⟨σ, t⟩ hσ htc
    simp only [h, Complex.zero_im, mul_zero, lt_self_iff_false] at ha
  refine ⟨t, ht, ?_, fun w hw htm ↦ ?_⟩
  · rw [analyticOrderNatAt,
      (hf ⟨σ, t⟩ hσ htc).analyticOrderAt_eq_one_of_zero_deriv_ne_zero htZero htDeriv]
    rfl
  constructor
  · intro hwZero
    let row (x : ℝ) := direction * (f ⟨x, w.im⟩).im
    have hH (x : ℝ) (hx : x ∈ Icc l r) :
        HasDerivAt row (direction * (deriv f ⟨x, w.im⟩).im) x :=
      (horizontalIm_hasDerivAt (hf ⟨x, w.im⟩ hx htm).differentiableAt).const_mul direction
    have hRow : StrictMonoOn row (Icc l r) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc l r)
        (fun x hx ↦ (hH x hx).continuousAt.continuousWithinAt)
        (fun x hx ↦ ?_)
      rw [(hH x (interior_subset hx)).deriv]
      exact hSlope ⟨x, w.im⟩ (interior_subset hx) htm
    have hPoint : (⟨w.re, w.im⟩ : ℂ) = w := Complex.ext rfl rfl
    have hR : row w.re = row σ := by
      simp only [row, hPoint, hwZero, Complex.zero_im, hReal w.im htm, mul_zero]
    have hLine : w.re = σ := hRow.injOn hw hσ hR
    have htEq : w.im = t := hAnti.injOn htm htc (by
      rw [htRe]
      dsimp only [onLine]
      rw [← hLine, hPoint, hwZero, Complex.zero_re, mul_zero])
    exact Complex.ext hLine htEq
  · rintro rfl
    exact htZero

/-- The full-strip sign test uses the local crossing and excludes the two
bands on either side by their real signs. -/
theorem strip_zero_unique_of_signed_bands {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {start a b finish : ℝ} (hstart : start ≤ a) (hab : a < b) (hfinish : b ≤ finish)
    (hBelow : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc start a → 0 < (f w).re)
    (hAbove : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc b finish → (f w).re < 0)
    (hSlope : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc a b → 0 < (deriv f w).im)
    (hReal : ∀ t ∈ Icc a b, (f ⟨1 / 2, t⟩).im = 0) :
    ∃ t ∈ Ioo a b, analyticOrderNatAt f ⟨1 / 2, t⟩ = 1 ∧
      ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc start finish →
        (f w = 0 ↔ w = ⟨1 / 2, t⟩) := by
  have hHalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  obtain ⟨t, ht, hOrder, hUnique⟩ :=
    unique_simple_zero_of_signed_crossing (direction := 1) (fun w _ _ ↦ hf.analyticAt w) hHalf hab
      (by simpa only [one_mul] using hBelow ⟨1 / 2, a⟩ hHalf ⟨hstart, le_rfl⟩)
      (by simpa only [one_mul] using hAbove ⟨1 / 2, b⟩ hHalf ⟨le_rfl, hfinish⟩)
      (fun w hw ht ↦ by simpa only [one_mul] using hSlope w hw ht) hReal
  refine ⟨t, ht, hOrder, fun w hw htBand ↦ ⟨?_, ?_⟩⟩
  · intro hwZero
    have htm : w.im ∈ Icc a b := by
      constructor
      · by_contra! hh
        have h := hBelow w hw ⟨htBand.1, hh.le⟩
        rwa [hwZero, Complex.zero_re, lt_self_iff_false] at h
      · by_contra! hh
        have h := hAbove w hw ⟨hh.le, htBand.2⟩
        rwa [hwZero, Complex.zero_re, lt_self_iff_false] at h
    exact (hUnique w hw htm).mp hwZero
  · rintro rfl
    exact (hUnique ⟨1 / 2, t⟩ hHalf (Ioo_subset_Icc_self ht)).mpr rfl

#check @unique_simple_zero_of_signed_crossing
#check @strip_zero_unique_of_signed_bands
#print axioms unique_simple_zero_of_signed_crossing
#print axioms strip_zero_unique_of_signed_bands

end FieldTarget
