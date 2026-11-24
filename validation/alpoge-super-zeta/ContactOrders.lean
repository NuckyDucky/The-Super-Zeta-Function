import OrdinaryInteractions
import SuperZeta.QuarterLine.QuarterEuler

namespace AlpogeSuperZeta

open Complex SuperZeta

noncomputable section

/-- Along the nonpositive integers the two ingredients vanish separately,
so the original continued root sum vanishes there too. -/
theorem all_readings_zero_at_neg_nat (n : ℕ) :
    Reference.entireCorrection 1 (-(n : ℂ)) = 0 ∧
    corrected (-(n : ℂ)) = 0 ∧ UnitSpectrum.continuation (-(n : ℂ)) = 0 := by
  have hJ := Reference.entireCorrection_neg_nat (q := 1) (by norm_num) n
  have hD : corrected (-(n : ℂ)) = 0 := by
    cases n with
    | zero => simp [corrected_eq, Spectrum.riemannFactor]
    | succ k =>
      rw [corrected_eq, show (2 : ℂ) * -((k.succ : ℕ) : ℂ) = -2 * ((k : ℂ) + 1)
        by push_cast; ring, riemannZeta_neg_two_mul_nat_add_one, mul_zero]
  exact ⟨hJ, hD, (sub_eq_zero.mp hD).trans hJ⟩

/-- A boundary coincidence is an order-one vanishing of the corrected
difference. Its first derivative is an explicit nonzero multiple of zeta. -/
theorem boundary_contact_slope {s : ℂ} (hs : s.re = 0)
    (hF : Spectrum.riemannFactor s = 0) :
    deriv corrected s =
      4 * Complex.log 2 * (Real.pi : ℂ) ^ (-(2 * s)) * riemannZeta (2 * s) ∧
    analyticOrderAt corrected s = 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπp : (Real.pi : ℂ) ^ (-(2 * s)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  have hc : (2 : ℂ) ^ (2 * s) - 1 = 0 :=
    (mul_eq_zero.mp hF).resolve_left (mul_ne_zero two_ne_zero hπp)
  have he : Complex.exp (Complex.log 2 * (2 * s)) = 1 := by
    rw [← Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    exact sub_eq_zero.mp hc
  have hl : HasDerivAt (fun z : ℂ => Complex.log 2 * (2 * z)) (Complex.log 2 * 2) s := by
    simpa using ((hasDerivAt_id s).const_mul 2).const_mul (Complex.log 2)
  have hk : HasDerivAt (fun z : ℂ => (2 : ℂ) ^ (2 * z) - 1) (Complex.log 2 * 2) s := by
    have h := (hl.cexp.sub_const 1)
    simpa only [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
      he, one_mul] using h
  let A : ℂ → ℂ := fun z => 2 * (Real.pi : ℂ) ^ (-(2 * z)) * riemannZeta (2 * z)
  have hZ := (Multiplicity.analytic_zeta (Multiplicity.doubled_ne_pole
    (by rw [hs]; norm_num))).comp (Multiplicity.scale_analytic 2 s)
  have hA : DifferentiableAt ℂ A s := by
    have hP : DifferentiableAt ℂ (fun z : ℂ => 2 * (Real.pi : ℂ) ^ (-(2 * z))) s := by
      simp only [Complex.cpow_def_of_ne_zero hπ]
      fun_prop
    exact hP.mul hZ.differentiableAt
  have hE : corrected = fun z => A z * ((2 : ℂ) ^ (2 * z) - 1) := by
    funext z
    rw [corrected_eq, Spectrum.riemannFactor]
    dsimp [A]
    ring
  have hd : deriv corrected s =
      4 * Complex.log 2 * (Real.pi : ℂ) ^ (-(2 * s)) * riemannZeta (2 * s) := by
    have h := hA.hasDerivAt.mul hk
    change HasDerivAt (fun z => A z * ((2 : ℂ) ^ (2 * z) - 1))
      (deriv A s * ((2 : ℂ) ^ (2 * s) - 1) + A s * (Complex.log 2 * 2)) s at h
    rw [hE, h.deriv, hc, mul_zero, zero_add]
    dsimp [A]
    ring
  have hl0 : Complex.log 2 ≠ 0 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have ha := (Multiplicity.analytic_factor s).mul hZ
  change AnalyticAt ℂ (fun z : ℂ => Spectrum.riemannFactor z * riemannZeta (2 * z)) s at ha
  rw [← funext corrected_eq] at ha
  refine ⟨hd, ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_⟩
  · rw [corrected_eq, hF, zero_mul]
  · rw [hd]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hl0) hπp)
      (zeta_at_imaginary_address_ne_zero hs)

theorem normalized_floor_mellin {s : ℂ} (hs : 0 < s.re) (hi : s.im ≠ 0) :
    normalized s =
      (2 * s) / (2 * s - 1) - (2 * s) *
        mellin QuarterEuler.floorKernel (-(2 * s)) := by
  rw [normalized_eq hs]
  apply QuarterEuler.zeta_integral
  · simp [two_mul]; linarith
  · simpa [Complex.mul_im] using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hi

#print axioms all_readings_zero_at_neg_nat
#print axioms boundary_contact_slope
#print axioms normalized_floor_mellin

end
end AlpogeSuperZeta
