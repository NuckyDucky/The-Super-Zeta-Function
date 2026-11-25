import EtaCenterBasisSound
import EtaEulerColumns

/-! The fixed-point calculation discharges both finite eta premises. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.MellinFixed

open EtaMellin

private def weight (j : ℕ) : ℝ := (-1:ℝ)^j * columnWeight 128 j

private def valueColumn (j : ℕ) : ℂ := (weight j:ℂ) * exponentialTerm j firstCenter

private def slopeColumn (j : ℕ) : ℂ :=
  (weight j:ℂ) * (exponentScale j * exponentialTerm j firstCenter)

private theorem signedWeight_contains (j : ℕ) :
    Contains (signedWeight128 j (binomialPrefix 128 j)) (weight j) := by
  have h := ratio_contains ((-1:Int)^j*((2:Int)^128-(binomialPrefix 128 j:Int)))
    (d := (2:Int)^128) (by decide +kernel)
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_ofNat,
    Int.cast_sub, Int.cast_natCast] at h
  change Contains (signedWeight128 j (binomialPrefix 128 j)) (weight j)
  unfold weight
  rw [columnWeight_eq]
  convert h using 1
  ring

private theorem sum_from_succ (f : ℕ → ℂ) (j count : ℕ) :
    (∑ k ∈ Finset.range (count+1), f (j+k)) =
      f j + ∑ k ∈ Finset.range count, f (j+1+k) := by
  rw [Finset.sum_range_succ', Nat.add_zero,
    add_comm (∑ k ∈ Finset.range count, f (j+(k+1))) (f j)]
  refine congrArg (fun z : ℂ => f j+z) (Finset.sum_congr rfl fun k _ => ?_)
  congr 1
  omega

private theorem etaColumns_contains (j tally count : ℕ) {b : EtaBounds}
    (htally : tally = ∑ k ∈ Finset.range j, (128:ℕ).choose k)
    (hj : j+count ≤ 128) (h : etaColumns j tally count = some b) :
    EtaContains b
      (∑ k ∈ Finset.range count, valueColumn (j+k))
      (∑ k ∈ Finset.range count, slopeColumn (j+k)) := by
  induction count generalizing j tally b with
  | zero =>
    have hb : zeroEta = b := Option.some.inj h
    simpa only [← hb, Finset.range_zero, Finset.sum_empty] using eta_zero_contains
  | succ count ih =>
    let total := tally+binomial128 j
    have hTotal : total = binomialPrefix 128 j := by
      unfold total binomial128 binomialPrefix
      rw [← Nat.choose_eq_descFactorial_div_factorial, htally, Finset.sum_range_succ]
    cases hBasis : etaBasis j with
    | none =>
      simp only [etaColumns, hBasis] at h
      cases h
    | some a =>
      cases hRest : etaColumns (j+1) total count with
      | none =>
        have hEq := hRest
        change etaColumns (j+1) (tally+binomial128 j) count = none at hEq
        simp only [etaColumns, hBasis, hEq] at h
        cases h
      | some rest =>
        have hEq := hRest
        change etaColumns (j+1) (tally+binomial128 j) count = some rest at hEq
        have hb : addEta (scaleEta (signedWeight128 j total) a) rest = b := by
          simpa only [etaColumns, hBasis, hEq, Option.some.injEq] using h
        have hScalar : Contains (signedWeight128 j total) (weight j) := by
          rw [hTotal]
          exact signedWeight_contains j
        have hF := eta_scale_contains hScalar (etaBasis_contains (by omega) hBasis)
        have hBack := ih (j+1) total hTotal (by omega) hRest
        rw [← hb, sum_from_succ, sum_from_succ, valueColumn, slopeColumn]
        exact eta_add_contains hF hBack

private theorem inside_correct {b : Box} {x : ℝ} {lo hi : ℤ}
    (hb : Contains b x) (h : inside b lo hi = true) :
    (lo:ℝ)/(scale:ℝ) ≤ x ∧ x ≤ (hi:ℝ)/(scale:ℝ) := by
  have hh : lo ≤ b.lo ∧ b.hi ≤ hi := of_decide_eq_true h
  have hlo : (lo:ℝ) ≤ (b.lo:ℝ) := by exact_mod_cast hh.1
  have hhi : (b.hi:ℝ) ≤ (hi:ℝ) := by exact_mod_cast hh.2
  exact ⟨(div_le_iff₀ scale_pos).mpr (by simpa only [mul_comm x] using hlo.trans hb.1),
    (le_div_iff₀ scale_pos).mpr (by simpa only [mul_comm x] using hb.2.trans hhi)⟩

private theorem checked_eta_reading {r : Option EtaBounds}
    (h : etaReadingCheck r = true) :
    ∃ a, r = some a ∧
      inside a.valueRe (-10^18) (10^18) = true ∧
      inside a.valueIm (-2*10^18) (2*10^18) = true ∧
      inside a.slopeRe (149*(scale/40)) (151*(scale/40)) = true ∧
      inside a.slopeIm (-11*(scale/40)) (-9*(scale/40)) = true := by
  cases r with
  | none => cases h
  | some a =>
    simp only [etaReadingCheck, Bool.and_eq_true_iff] at h
    exact ⟨a,rfl,by tauto⟩

theorem eta_center_bounds :
    ‖etaDiskApprox firstCenter‖ ≤ 3/10^6 ∧
      ‖deriv etaDiskApprox firstCenter - etaDiskDirection‖ ≤ 1/20 := by
  obtain ⟨b,hb,hR,hI,hDR,hDI⟩ :=
    checked_eta_reading (r := etaColumns 0 0 128) etaCenterCheck_passes
  have hC := etaColumns_contains 0 0 128 (by simp) (by decide) hb
  have hV : etaDiskApprox firstCenter = ∑ j ∈ Finset.range 128, valueColumn j := by
    simp only [etaDiskApprox, etaEulerSum, power_as_exp]
    simpa only [valueColumn, weight, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_neg, Complex.ofReal_one] using
      euler_sum_by_columns 128 (fun j => exponentialTerm j firstCenter)
  have hD : deriv etaDiskApprox firstCenter = ∑ j ∈ Finset.range 128, slopeColumn j := by
    rw [deriv_etaDiskApprox, etaDiskDerivative]
    simpa only [slopeColumn, weight, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_neg, Complex.ofReal_one] using
      euler_sum_by_columns 128 (fun j => exponentScale j * exponentialTerm j firstCenter)
  have hc : EtaContains b (etaDiskApprox firstCenter) (deriv etaDiskApprox firstCenter) := by
    simpa only [Nat.zero_add, ← hV, ← hD] using hC
  have hr := inside_correct hc.1 hR
  have hi := inside_correct hc.2.1 hI
  have hdr := inside_correct hc.2.2.1 hDR
  have hdi := inside_correct hc.2.2.2 hDI
  norm_num [scale] at hr hi hdr hdi
  constructor
  · have hAbsR : |(etaDiskApprox firstCenter).re| ≤ 1/1000000 := abs_le.mpr hr
    have hAbsI : |(etaDiskApprox firstCenter).im| ≤ 1/500000 := abs_le.mpr hi
    linarith only [Complex.norm_le_abs_re_add_abs_im (etaDiskApprox firstCenter), hAbsR,hAbsI]
  · have hAbsR : |(deriv etaDiskApprox firstCenter - etaDiskDirection).re| ≤ 1/40 := by
      simp only [Complex.sub_re, etaDiskDirection]
      exact abs_le.mpr ⟨by linarith only [hdr.1], by linarith only [hdr.2]⟩
    have hAbsI : |(deriv etaDiskApprox firstCenter - etaDiskDirection).im| ≤ 1/40 := by
      simp only [Complex.sub_im, etaDiskDirection]
      exact abs_le.mpr ⟨by linarith only [hdi.1], by linarith only [hdi.2]⟩
    linarith only [Complex.norm_le_abs_re_add_abs_im
      (deriv etaDiskApprox firstCenter - etaDiskDirection), hAbsR,hAbsI]

theorem firstContour_read_of_kernel_eta
    (hsamples : checkTableRange 576 1728 = true) :
    ∃ ρ ∈ Metric.ball firstCenter firstRadius,
      nativeCross ρ = 0 ∧ deriv nativeCross ρ ≠ 0 ∧ riemannZeta (2*ρ) = 0 ∧
      (∀ s ∈ Metric.closedBall firstCenter firstRadius, nativeCross s = 0 ↔ s = ρ) ∧
      (∀ p : ℂ → ℂ, Differentiable ℂ p →
        weightedCircle firstCenter firstRadius nativeCross p = p ρ) :=
  firstContour_read_of_finite_center hsamples eta_center_bounds.1 eta_center_bounds.2

#print axioms eta_center_bounds
#print axioms firstContour_read_of_kernel_eta

end DottieOriented.NativeSpectrum.MellinFixed
end
