import SignedContact
import SuperZeta.Reciprocal

namespace AlpogeSuperZeta

open Complex SuperZeta Filter
open scoped Topology

noncomputable section

def ordinarySlope (s : ℂ) : ℂ :=
  (logDeriv corrected s - logDeriv Spectrum.riemannFactor s) / 2

def weightedSlope {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a b : ℂ) (s : ℂ) : ℂ :=
  b * signedSlope χ s + (a - b) * ordinarySlope s

theorem weightedSlope_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a b s : ℂ) :
    weightedSlope χ a b s = a * ordinarySlope s -
      b * (logDeriv (fun z : ℂ => χ.LFunction (2 * z)) s / 2) := by
  unfold weightedSlope ordinarySlope signedSlope
  ring

/-- Weight the two logarithmic derivatives before taking their difference.
The residue records the weighted difference of the original orders. -/
theorem weighted_slope_residue {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2)
    (hζ : analyticOrderAt riemannZeta (2 * s) ≠ ⊤)
    (hχ : analyticOrderAt χ.LFunction (2 * s) ≠ ⊤) :
    ∃ m n : ℕ, (m : ℕ∞) = analyticOrderAt riemannZeta (2 * s) ∧
      (n : ℕ∞) = analyticOrderAt χ.LFunction (2 * s) ∧
      ∀ a b : ℂ, Tendsto (fun z => (z - s) * weightedSlope χ a b z)
        (𝓝[≠] s) (𝓝 ((a * (m : ℂ) - b * (n : ℂ)) / 2)) := by
  obtain ⟨m, n, hm, hn, A, hA, heA⟩ := signed_slope_local χ h₀ h₁ hζ hχ
  have hJ := (Reference.entireCorrection_differentiable (q := 1) (by norm_num)).analyticAt s
  have hD : AnalyticAt ℂ corrected s :=
    (UnitSpectrum.continuation_analytic (Multiplicity.doubled_ne_pole h₁)).sub hJ
  have hDo : analyticOrderAt corrected s = analyticOrderAt riemannZeta (2 * s) :=
    UnitSpectrum.difference_order h₀ h₁
  obtain ⟨k, _, hk, B, hB, heB⟩ := Deduction.logDeriv_local hD
    (fun h => hζ (hDo.symm.trans (analyticOrderAt_eq_top.mpr h)))
  have hkm : k = m := by exact_mod_cast hk.trans (hDo.trans hm.symm)
  subst k
  have hF := Multiplicity.analytic_factor s
  have hL : AnalyticAt ℂ (logDeriv Spectrum.riemannFactor) s :=
    hF.deriv.div hF (Spectrum.riemannFactor_ne_zero h₀)
  refine ⟨m, n, hm, hn, ?_⟩
  intro a b
  let H : ℂ → ℂ := fun z =>
    b * A z + (a - b) * ((B z - logDeriv Spectrum.riemannFactor z) / 2)
  have hH : AnalyticAt ℂ H s :=
    (analyticAt_const.mul hA).add (analyticAt_const.mul
      ((hB.sub hL).div analyticAt_const (by norm_num)))
  have ht : Tendsto (fun z : ℂ => (a * (m : ℂ) - b * (n : ℂ)) / 2 + (z - s) * H z)
      (𝓝[≠] s) (𝓝 ((a * (m : ℂ) - b * (n : ℂ)) / 2)) := by
    have hc : ContinuousAt (fun z : ℂ => z - s) s := by fun_prop
    have hd : ContinuousAt (fun z : ℂ =>
        (a * (m : ℂ) - b * (n : ℂ)) / 2 + (z - s) * H z) s :=
      continuousAt_const.add (hc.mul hH.continuousAt)
    simpa only [sub_self, zero_mul, add_zero] using hd.tendsto.mono_left
      (nhdsWithin_le_nhds (s := ({s}ᶜ : Set ℂ)))
  apply ht.congr'
  filter_upwards [heA, heB, self_mem_nhdsWithin] with z hz hBz hzs
  have hne : z - s ≠ 0 := sub_ne_zero.mpr (show z ≠ s from hzs)
  rw [weightedSlope, hz, ordinarySlope, logDeriv_apply corrected, hBz]
  dsimp [H]
  field_simp [hne]
  ring

/-- The two rooted alternating words at the same cap, with minus-first
in the first slot. Both evaluations come from the actual reciprocal step. -/
def capReadings (L : ℂ) : ℂ × ℂ :=
  Reciprocal.step L (Reciprocal.step L (1, 1))

theorem cap_readings_eq (L : ℂ) :
    capReadings L = (exp (L * exp (-L)), exp (-L * exp L)) := by
  simp [capReadings, Reciprocal.step]

theorem positive_cap_readings_ne {L : ℝ} (hL : 0 < L) :
    (capReadings (L : ℂ)).1 ≠ (capReadings (L : ℂ)).2 := by
  rw [cap_readings_eq]
  have h₁ : 1 < Real.exp (L * Real.exp (-L)) := by
    rw [Real.one_lt_exp_iff]
    exact mul_pos hL (Real.exp_pos _)
  have h₂ : Real.exp (-L * Real.exp L) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hL) (Real.exp_pos _)
  have hne : Real.exp (L * Real.exp (-L)) ≠ Real.exp (-L * Real.exp L) :=
    ne_of_gt (h₂.trans h₁)
  intro h
  apply hne
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg] using h

theorem imaginary_cap_readings_ne {y : ℝ} (hy : 0 < y) (hyπ : y < Real.pi / 2) :
    (capReadings (I * (y : ℂ))).1 ≠ (capReadings (I * (y : ℂ))).2 := by
  let L := I * (y : ℂ)
  have ha : (L * exp (-L)).im = y * Real.cos y := by
    simp [L, Complex.mul_im, Complex.mul_re, Complex.exp_re]
  have hb : (-L * exp L).im = -(y * Real.cos y) := by
    simp [L, Complex.mul_im, Complex.mul_re, Complex.exp_re]
  have hcos : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hyπ⟩
  have hangle : y * Real.cos y < Real.pi :=
    (mul_le_of_le_one_right hy.le (Real.cos_le_one y)).trans_lt
      (hyπ.trans (half_lt_self Real.pi_pos))
  have hsin := Real.sin_pos_of_pos_of_lt_pi (mul_pos hy hcos) hangle
  have hp : 0 < (capReadings L).1.im := by
    rw [cap_readings_eq, Complex.exp_im, ha]
    exact mul_pos (Real.exp_pos _) hsin
  have hn : (capReadings L).2.im < 0 := by
    rw [cap_readings_eq, Complex.exp_im, hb, Real.sin_neg]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (neg_lt_zero.mpr hsin)
  intro h
  exact (ne_of_gt (hn.trans hp)) (congrArg Complex.im h)

theorem swapped_weights_read_total (a b : ℂ) (m n : ℕ) :
    (a * (m : ℂ) - b * (n : ℂ)) / 2 -
      (b * (m : ℂ) - a * (n : ℂ)) / 2 = (a - b) * ((m : ℂ) + (n : ℂ)) / 2 := by
  ring

theorem cap_recovers_order {L : ℂ} (hL : (capReadings L).1 ≠ (capReadings L).2) (m : ℕ) :
    2 * (((capReadings L).1 * (m : ℂ) - (capReadings L).2 * (m : ℂ)) / 2) /
      ((capReadings L).1 - (capReadings L).2) = (m : ℂ) := by
  have hn := sub_ne_zero.mpr hL
  field_simp [hn]

/-- When the ordinary signed residue cancels, the two actual cap readings
give a nonzero conversion factor back to the common order. -/
theorem ordered_cap_recovers_canceled_order {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2)
    (hf : analyticOrderAt riemannZeta (2 * s) ≠ ⊤)
    (he : analyticOrderAt riemannZeta (2 * s) = analyticOrderAt χ.LFunction (2 * s))
    {L : ℂ} (hL : (capReadings L).1 ≠ (capReadings L).2) :
    let a := (capReadings L).1
    let b := (capReadings L).2
    ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt riemannZeta (2 * s) ∧
      Tendsto (fun z => (z - s) * signedSlope χ z) (𝓝[≠] s) (𝓝 0) ∧
      Tendsto (fun z => 2 * ((z - s) * weightedSlope χ a b z) / (a - b))
        (𝓝[≠] s) (𝓝 (m : ℂ)) := by
  dsimp only
  obtain ⟨m, n, hm, hn, h⟩ := weighted_slope_residue χ h₀ h₁ hf (he ▸ hf)
  have hmn : m = n := by exact_mod_cast hm.trans (he.trans hn.symm)
  subst n
  refine ⟨m, hm, ?_, ?_⟩
  · simpa [weightedSlope] using h 1 1
  · simpa only [cap_recovers_order hL m] using
      ((h (capReadings L).1 (capReadings L).2).const_mul (2 : ℂ)).div_const
        ((capReadings L).1 - (capReadings L).2)

/-- The principal character mod two is an exact equal-order control
everywhere in the strip, because removing the prime 2 retains these orders. -/
theorem mod_two_orders_match {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2) :
    analyticOrderAt riemannZeta (2 * s) =
      analyticOrderAt (DirichletCharacter.LFunctionTrivChar 2) (2 * s) := by
  let B : ℂ → ℂ := fun z =>
    2 * (Real.pi : ℂ) ^ (-(2 * z)) * (2 : ℂ) ^ (2 * z)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hb : AnalyticAt ℂ B s := by
    dsimp [B]
    simp only [Complex.cpow_def_of_ne_zero hπ, Complex.cpow_def_of_ne_zero h2]
    fun_prop
  have hb0 : B s ≠ 0 := mul_ne_zero
    (mul_ne_zero h2 (Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl h2))
  have hp := Multiplicity.doubled_ne_pole h₁
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunctionTrivChar 2) ({1}ᶜ : Set ℂ) :=
    fun z hz => (DirichletCharacter.differentiableAt_LFunction
      (1 : DirichletCharacter ℂ 2) z (Or.inl hz)).differentiableWithinAt
  have ha := hd.analyticAt (isOpen_compl_singleton.mem_nhds hp)
  have he : corrected =ᶠ[𝓝 s] B * (DirichletCharacter.LFunctionTrivChar 2 ∘ (fun z : ℂ => 2*z)) := by
    have hn : ∀ᶠ z : ℂ in 𝓝 s, z.re < 1 / 2 :=
      (isOpen_lt continuous_re continuous_const).mem_nhds h₁
    filter_upwards [hn] with z hz
    exact corrected_eq_triv_char_two (Multiplicity.doubled_ne_pole hz)
  have hc := UnitSpectrum.difference_order h₀ h₁
  change analyticOrderAt corrected s = analyticOrderAt riemannZeta (2 * s) at hc
  have hprod := analyticOrderAt_mul hb (ha.comp (Multiplicity.scale_analytic 2 s))
  rw [hb.analyticOrderAt_eq_zero.mpr hb0, zero_add] at hprod
  exact hc.symm.trans ((analyticOrderAt_congr he).trans
    (hprod.trans (Multiplicity.scale_order h2 ha)))

theorem ordinary_order_finite {w : ℂ} (hp : w ≠ 1) :
    analyticOrderAt riemannZeta w ≠ ⊤ := by
  intro h
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    fun _ hz => Multiplicity.analytic_zeta hz
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hz := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc
    (show w ∈ ({1}ᶜ : Set ℂ) from hp) (analyticOrderAt_eq_top.mp h)
  exact (riemannZeta_ne_zero_of_one_le_re (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re))
    (hz (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num))

/-- A control with exact cancellation, using the principal character
modulo two and the actual ordered cap on the imaginary-lift section. -/
theorem mod_two_cancellation_read_at_imaginary_lift {s : ℂ}
    (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2)
    {y : ℝ} (hy : 0 < y) (hyπ : y < Real.pi / 2) :
    let χ : DirichletCharacter ℂ 2 := 1
    let L : ℂ := I * (y : ℂ)
    let a := (capReadings L).1
    let b := (capReadings L).2
    ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt riemannZeta (2 * s) ∧
      Tendsto (fun z => (z - s) * signedSlope χ z) (𝓝[≠] s) (𝓝 0) ∧
      Tendsto (fun z => 2 * ((z - s) * weightedSlope χ a b z) / (a - b))
        (𝓝[≠] s) (𝓝 (m : ℂ)) :=
  ordered_cap_recovers_canceled_order (1 : DirichletCharacter ℂ 2) h₀ h₁
    (ordinary_order_finite (Multiplicity.doubled_ne_pole h₁))
    (mod_two_orders_match h₀ h₁) (imaginary_cap_readings_ne hy hyπ)

#print axioms weightedSlope_eq
#print axioms weighted_slope_residue
#print axioms cap_readings_eq
#print axioms positive_cap_readings_ne
#print axioms imaginary_cap_readings_ne
#print axioms swapped_weights_read_total
#print axioms cap_recovers_order
#print axioms ordered_cap_recovers_canceled_order
#print axioms mod_two_orders_match
#print axioms ordinary_order_finite
#print axioms mod_two_cancellation_read_at_imaginary_lift

end
end AlpogeSuperZeta
