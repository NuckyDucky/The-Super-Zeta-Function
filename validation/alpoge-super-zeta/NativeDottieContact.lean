import NativeDottieMellin

/-! The common arithmetic germ and the two native corrections at exactly
the same spectral input. The determinant coordinate does not move when
the orientation label is exchanged. -/
noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex Filter Set SuperZeta
open scoped Topology

def sharedReference (s : ℂ) : ℂ :=
  LiuConnection.reference (1/3 : ℝ) (2*s)

def spectralReading (positiveAngle : Bool) (s : ℂ) : ℂ :=
  sharedReference s + correction positiveAngle s

def thirdFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^(-(2*s))*((3 : ℂ)^(2*s)-1)

theorem sharedReference_eq {s : ℂ} (hp : 2*s ≠ 1) :
    sharedReference s = thirdFactor s * riemannZeta (2*s) := by
  simpa only [sharedReference, thirdFactor, mul_assoc] using
    LiuConnection.reference_at_thirds (Or.inl rfl) hp

theorem arithmetic_hurwitz_shifts {s : ℂ} (hp : 2*s ≠ 1) :
    LiuConnection.reference (2/3 : ℝ) (2*s) = sharedReference s := by
  rw [LiuConnection.reference_at_thirds (Or.inr rfl) hp, sharedReference_eq hp, thirdFactor, mul_assoc]

theorem thirdFactor_ne_zero {s : ℂ} (h₀ : 0 < s.re) : thirdFactor s ≠ 0 := by
  have hw : 0 < (2*s).re := by simp [two_mul]; linarith
  refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl ?_))
    (LiuConnection.three_factor_ne_zero hw)
  exact_mod_cast Real.pi_ne_zero

private theorem analytic_thirdFactor (s : ℂ) : AnalyticAt ℂ thirdFactor s := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold thirdFactor
  simp only [Complex.cpow_def_of_ne_zero hπ, Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ) ≠ 0)]
  fun_prop

theorem reference_zero_iff {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1/2) :
    sharedReference s = 0 ↔ riemannZeta (2*s) = 0 := by
  rw [sharedReference_eq (Multiplicity.doubled_ne_pole h₁)]
  exact mul_eq_zero_iff_left (thirdFactor_ne_zero h₀)

theorem corrected_reading_eq (b : Bool) (s : ℂ) :
    spectralReading b s - correction b s = sharedReference s := by
  simp [spectralReading]

/-- Compare the two readings against their own native corrections. -/
def nativeCross (s : ℂ) : ℂ :=
  correction false s * spectralReading true s - correction true s * spectralReading false s

theorem native_cross_eq (s : ℂ) : nativeCross s =
    (correction false s - correction true s) * sharedReference s := by
  unfold nativeCross spectralReading
  ring

theorem native_cross_zero_iff {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1/2)
    (hsep : correction false s ≠ correction true s) :
    nativeCross s = 0 ↔ riemannZeta (2*s) = 0 := by
  rw [native_cross_eq, mul_eq_zero_iff_left (sub_ne_zero.mpr hsep), reference_zero_iff h₀ h₁]

theorem native_ratio_difference {s : ℂ} (h : spectralReading false s ≠ 0)
    (hJ : correction false s ≠ 0) :
    spectralReading true s / spectralReading false s - correction true s / correction false s =
      nativeCross s / (spectralReading false s * correction false s) := by
  unfold nativeCross
  field_simp [h, hJ]
  ring

/-- Exchanging the orientation leaves the entire shared arithmetic
contribution out of the difference, at every spectral input. -/
theorem contrast_eq (s : ℂ) :
    spectralReading true s - spectralReading false s = correction true s - correction false s := by
  unfold spectralReading
  ring

theorem contrast_entire :
    Differentiable ℂ (fun s => spectralReading true s - spectralReading false s) := by
  rw [funext contrast_eq]
  exact (correction_entire true).sub (correction_entire false)

theorem corrected_slopes_equal :
    (fun s => deriv (fun z => spectralReading true z - correction true z) s /
        (spectralReading true s - correction true s)) =
    (fun s => deriv (fun z => spectralReading false z - correction false z) s /
        (spectralReading false s - correction false s)) := by
  rw [funext (corrected_reading_eq true), funext (corrected_reading_eq false)]
  simp only [corrected_reading_eq]

theorem values_at_reference_zero {s : ℂ} (h₁ : s.re < 1/2)
    (hzero : riemannZeta (2*s) = 0) (b : Bool) : spectralReading b s = correction b s := by
  rw [spectralReading, sharedReference_eq (Multiplicity.doubled_ne_pole h₁), hzero, mul_zero, zero_add]

/-- Both original readings have the same order-bearing term, including
the same analytic unit. The integral corrections remain separate. -/
theorem same_input_expansion {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1/2) {m : ℕ}
    (hm : (Multiplicity.analytic_zeta (Multiplicity.doubled_ne_pole h₁)).order = (m : ENat)) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U s ∧ U s ≠ 0 ∧
      ∀ᶠ z in 𝓝 s, ∀ b : Bool,
        spectralReading b z = correction b z + (z - s)^m * U z := by
  let F : ℂ → ℂ := fun z => thirdFactor z * riemannZeta (2*z)
  have hA := analytic_thirdFactor s
  have hZ := Multiplicity.analytic_zeta (Multiplicity.doubled_ne_pole h₁)
  have hZm := hZ.comp (Multiplicity.scale_analytic 2 s)
  have hF : AnalyticAt ℂ F s := hA.mul hZm
  have hFo : hF.order = (m : ENat) := by
    change (hA.mul hZm).order = _
    rw [AnalyticAt.order_mul, hA.order_eq_zero_iff.mpr (thirdFactor_ne_zero h₀), zero_add]
    exact (Multiplicity.scale_order (by norm_num) hZ).trans hm
  obtain ⟨U, hU, hne, hEq⟩ := hF.order_eq_nat_iff.mp hFo
  refine ⟨U,hU,hne,?_⟩
  have hs : ∀ᶠ z : ℂ in 𝓝 s, z.re < 1/2 :=
    (isOpen_lt continuous_re continuous_const).mem_nhds h₁
  filter_upwards [hEq, hs] with z hz hzu
  intro b
  rw [spectralReading, sharedReference_eq (Multiplicity.doubled_ne_pole hzu)]
  change F z + correction b z = _
  rw [hz, smul_eq_mul, add_comm]

/-- The native cross-product keeps the shared finite zero order wherever the
two native corrections have different values. No denominator is needed. -/
theorem native_cross_expansion {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1/2) {m : ℕ}
    (hm : (Multiplicity.analytic_zeta (Multiplicity.doubled_ne_pole h₁)).order = (m : ENat))
    (hsep : correction false s ≠ correction true s) :
    ∃ W : ℂ → ℂ, AnalyticAt ℂ W s ∧ W s ≠ 0 ∧
      ∀ᶠ z in 𝓝 s, nativeCross z = (z - s)^m * W z := by
  obtain ⟨U, hU, hU₀, hnear⟩ := same_input_expansion h₀ h₁ hm
  refine ⟨fun z => (correction false z - correction true z) * U z, ?_,
    mul_ne_zero (sub_ne_zero.mpr hsep) hU₀, ?_⟩
  · exact (((correction_entire false).analyticAt s).sub
      ((correction_entire true).analyticAt s)).mul hU
  filter_upwards [hnear] with z hz
  rw [nativeCross, hz true, hz false]
  ring

/-- If the raw values at a shared zero are individually nonzero, the raw
logarithmic slopes are themselves regular at that input. -/
theorem raw_signed_slope_regular {s : ℂ} (h₁ : s.re < 1/2)
    (hzero : riemannZeta (2*s) = 0) (h₀ : correction false s ≠ 0) (hp : correction true s ≠ 0) :
    AnalyticAt ℂ (fun z => deriv (spectralReading true) z / spectralReading true z -
      deriv (spectralReading false) z / spectralReading false z) s := by
  have hRef := (analytic_thirdFactor s).mul
    ((Multiplicity.analytic_zeta (Multiplicity.doubled_ne_pole h₁)).comp
      (Multiplicity.scale_analytic 2 s))
  have he : (fun z => thirdFactor z * riemannZeta (2*z)) =ᶠ[𝓝 s] sharedReference := by
    have hset : ∀ᶠ z : ℂ in 𝓝 s, z.re < 1/2 :=
      (isOpen_lt continuous_re continuous_const).mem_nhds h₁
    filter_upwards [hset] with z hz
    exact (sharedReference_eq (Multiplicity.doubled_ne_pole hz)).symm
  have hA (b : Bool) : AnalyticAt ℂ (spectralReading b) s :=
    (hRef.congr he).add ((correction_entire b).analyticAt s)
  have hne (b : Bool) : spectralReading b s ≠ 0 := by
    rw [values_at_reference_zero h₁ hzero b]
    cases b
    · exact h₀
    · exact hp
  exact ((hA true).deriv.div (hA true) (hne true)).sub
    ((hA false).deriv.div (hA false) (hne false))

#print axioms arithmetic_hurwitz_shifts
#print axioms reference_zero_iff
#print axioms corrected_slopes_equal
#print axioms contrast_entire
#print axioms values_at_reference_zero
#print axioms same_input_expansion
#print axioms native_cross_eq
#print axioms native_cross_zero_iff
#print axioms native_ratio_difference
#print axioms native_cross_expansion
#print axioms raw_signed_slope_regular

end DottieOriented.NativeSpectrum
end
