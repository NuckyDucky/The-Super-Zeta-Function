import DedekindCofinalSignedRings
import DedekindMixedTheta
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The actual pole-cleared mixed-theta reading, at the same input as the
Dedekind continuation, supplies the analytic inputs of the finite-ring test. -/

namespace FieldTarget

open Complex Set ArtinPrimitiveRootsConjecture
open DedekindZetaZeroFree.AbelianQuotient
open scoped ComplexConjugate

/-- The ideal-counting continuation supplied by the mixed-theta construction. -/
noncomputable def mixedThetaContinuation (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  Classical.choose (exists_dedekind_continuation_with_reflection K)

theorem mixedThetaContinuation_isDedekind (K : Type*) [Field K] [NumberField K] :
    IsDedekindZeta K (mixedThetaContinuation K) :=
  (Classical.choose_spec (exists_dedekind_continuation_with_reflection K)).1

theorem mixedThetaContinuation_reflects (K : Type*) [Field K] [NumberField K]
    (w : ℂ) (hlo : 0 < w.re) (hhi : w.re < 1) (hz : mixedThetaContinuation K w = 0) :
    mixedThetaContinuation K (1-conj w) = 0 :=
  (Classical.choose_spec (exists_dedekind_continuation_with_reflection K)).2 w hlo hhi hz

/-- The pole-cleared reading written intrinsically using the field's infinite
places and discriminant. -/
noncomputable def mixedThetaSignedReading (K : Type*) [Field K] [NumberField K] (w : ℂ) : ℂ :=
  w * (1-w) * (dedekindGammaFactor K w * mixedThetaContinuation K w)

theorem mixedThetaSignedReading_eq_mellin_sub (K : Type) [Field K] [NumberField K] (w : ℂ)
    (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaSignedReading K w =
      w * (1-w) * (Theta.mixedThetaPair K).Λ₀ w - (Theta.mixedThetaPair K).f₀ :=
  mixedTheta_completion_eq_sub K (mixedThetaContinuation_isDedekind K) w hlo hhi

theorem mixedThetaSignedReading_zero_iff (K : Type*) [Field K] [NumberField K] (w : ℂ)
    (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaSignedReading K w = 0 ↔ mixedThetaContinuation K w = 0 := by
  have h0 : w ≠ 0 := by rintro rfl; norm_num at hlo
  have h1 : 1-w ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro h
    subst w
    norm_num at hhi
  simp [mixedThetaSignedReading, h0, h1, dedekindGammaFactor_ne_zero K hlo]

private theorem gamma_factor_differentiableAt (K : Type*) [Field K] [NumberField K]
    {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ (dedekindGammaFactor K) w := by
  let d : ℂ := ((|NumberField.discr K| : ℤ) : ℂ)
  have hd0 : d ≠ 0 := by simp [d, NumberField.discr_ne_zero K]
  have hd : DifferentiableAt ℂ (fun z : ℂ => d ^ (z / 2)) w :=
    (differentiableAt_id.div_const (2:ℂ)).const_cpow (Or.inl hd0)
  have hR0 := Complex.Gammaℝ_ne_zero_of_re_pos hw
  have hC0 : Complex.Gammaℂ w ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl
        (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))))
      (Complex.Gamma_ne_zero_of_re_pos hw)
  have hR : DifferentiableAt ℂ Complex.Gammaℝ w := by
    have h := (Complex.differentiable_Gammaℝ_inv w).inv (inv_ne_zero hR0)
    change DifferentiableAt ℂ (fun s => ((Complex.Gammaℝ s)⁻¹)⁻¹) w at h
    simpa only [inv_inv] using h
  have hC : DifferentiableAt ℂ Complex.Gammaℂ w := by
    have h := (Complex.differentiable_Gammaℂ_inv w).inv (inv_ne_zero hC0)
    change DifferentiableAt ℂ (fun s => ((Complex.Gammaℂ s)⁻¹)⁻¹) w at h
    simpa only [inv_inv] using h
  exact (hd.mul (hR.pow _)).mul (hC.pow _)

theorem mixedThetaSignedReading_differentiableOn (K : Type*) [Field K] [NumberField K] :
    DifferentiableOn ℂ (mixedThetaSignedReading K) (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
  let S := Complex.re ⁻¹' Ioo (0 : ℝ) 1
  have hgamma : DifferentiableOn ℂ (dedekindGammaFactor K) S :=
    fun _ hw => (gamma_factor_differentiableAt K hw.1).differentiableWithinAt
  have hsub : S ⊆ ({1}ᶜ : Set ℂ) := by
    intro w hw
    simp only [mem_compl_iff, mem_singleton_iff]
    intro h
    subst w
    have hlt := hw.2
    norm_num at hlt
  have hZ := (mixedThetaContinuation_isDedekind K).1.mono hsub
  have hp : Differentiable ℂ (fun z : ℂ => z*(1-z)) :=
    differentiable_id.mul ((differentiable_const (1:ℂ)).sub differentiable_id)
  exact hp.differentiableOn.mul (hgamma.mul hZ)

/-- In the open critical strip, the pole polynomial and the gamma factor
are analytic and nonzero. They preserve the order of a Dedekind zero. -/
theorem mixedThetaSignedReading_order_eq_continuation (K : Type*) [Field K] [NumberField K]
    {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1) :
    analyticOrderAt (mixedThetaSignedReading K) w = analyticOrderAt (mixedThetaContinuation K) w := by
  let S : Set ℂ := Complex.re ⁻¹' Ioi (0 : ℝ)
  let m : ℂ → ℂ := fun z ↦ z * (1 - z) * dedekindGammaFactor K z
  have hS : IsOpen S := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hp : Differentiable ℂ (fun z : ℂ ↦ z * (1 - z)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have hgamma : DifferentiableOn ℂ (dedekindGammaFactor K) S :=
    fun _ hz ↦ (gamma_factor_differentiableAt K hz).differentiableWithinAt
  have hm : AnalyticAt ℂ m w := (hp.differentiableOn.mul hgamma).analyticOnNhd hS w hlo
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hlo
  have hw1 : w ≠ 1 := by rintro rfl; norm_num at hhi
  have hm0 : m w ≠ 0 := mul_ne_zero (mul_ne_zero hw0 (sub_ne_zero.mpr hw1.symm))
    (dedekindGammaFactor_ne_zero K hlo)
  have hZ : AnalyticAt ℂ (mixedThetaContinuation K) w :=
    (mixedThetaContinuation_isDedekind K).1.analyticOnNhd isOpen_compl_singleton w (by simpa using hw1)
  have heq : mixedThetaSignedReading K = m * mixedThetaContinuation K := by
    funext z
    simp [mixedThetaSignedReading, m, mul_assoc]
  rw [heq, analyticOrderAt_mul hm hZ, hm.analyticOrderAt_eq_zero.mpr hm0, zero_add]

/-- The remaining inputs are the outer zero-free part of the strip and the
finite signed certificates for the actual mixed-theta readings. -/
theorem dedekindZetaRH_of_mixedTheta_signed_rings (K : Type*) [Field K] [NumberField K]
    (h31 : ∀ w : ℂ, 31/32 < w.re → w.re < 1 → mixedThetaContinuation K w ≠ 0)
    (hbands : ∀ N : ℕ, HasFiniteDottieBoundaryCertificate
      (mixedThetaContinuation K) (mixedThetaSignedReading K) (-(N:ℝ)) (N:ℝ)) :
    DedekindZetaRH K :=
  dedekindZetaRH_of_finite_signed_dottie_boundaries
    (mixedThetaContinuation_isDedekind K) (mixedThetaSignedReading_differentiableOn K)
    (fun w hlo hhi => (mixedThetaSignedReading_zero_iff K w hlo hhi).mpr)
    (mixedThetaContinuation_reflects K) h31 hbands

#check @dedekindZetaRH_of_mixedTheta_signed_rings
#print axioms mixedThetaContinuation_isDedekind
#print axioms mixedThetaContinuation_reflects
#print axioms mixedThetaSignedReading_eq_mellin_sub
#print axioms mixedThetaSignedReading_zero_iff
#print axioms mixedThetaSignedReading_differentiableOn
#print axioms mixedThetaSignedReading_order_eq_continuation
#print axioms dedekindZetaRH_of_mixedTheta_signed_rings

end FieldTarget
