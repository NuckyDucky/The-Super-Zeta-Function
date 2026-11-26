import GaussianVaughanLogWindow
import GaussianRawWindowCriterion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Read the logarithmic derivative at the Gaussian zeros and transport the
one-sided bound on the complementary prime sum to the archived quartic. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory Set QuarticModel FieldTarget ArtinPrimitiveRootsConjecture
open scoped Topology

noncomputable section

/-- The negative logarithmic derivative at a zero of order n. The formula is
on a punctured neighborhood, so it describes the pole independently of the
value assigned by totalized division at the center. -/
theorem gaussianNegLogDeriv_local {f : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f ρ) (hn : analyticOrderAt f ρ = n) :
    ∃ b : ℂ → ℂ, AnalyticAt ℂ b ρ ∧
      ∀ᶠ z in 𝓝[≠] ρ, -logDeriv f z = -(n : ℂ) / (z - ρ) + b z := by
  obtain ⟨U, hU, hUn, hFactor⟩ := hf.analyticOrderAt_eq_natCast.mp hn
  have hEq : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ n * U z := by
    filter_upwards [hFactor] with z hz using by simpa only [smul_eq_mul] using hz
  refine ⟨fun z => -logDeriv U z, (hU.deriv.div hU hUn).neg, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (logDeriv_congr_nhds hEq),
    nhdsWithin_le_nhds hU.eventually_analyticAt,
    nhdsWithin_le_nhds (hU.continuousAt.eventually_ne hUn), self_mem_nhdsWithin]
    with z hz hUa hUne hne
  change z ≠ ρ at hne
  have hlin : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  change -logDeriv f z = -(n : ℂ) / (z - ρ) + -logDeriv U z
  rw [hz, logDeriv_mul (f := fun w : ℂ => (w - ρ) ^ n) (g := U) z
    (pow_ne_zero _ (sub_ne_zero.mpr hne)) hUne
    (hlin.differentiableAt.pow n) hUa.differentiableAt, logDeriv_fun_pow hlin.differentiableAt,
    show logDeriv (fun w : ℂ => w - ρ) z = 1 / (z - ρ) by
      rw [logDeriv_apply, hlin.deriv]]
  ring

/-- The fixed two-scale weight in the actual Gaussian Mellin variable. -/
def archivedGaussianVaughanMultiplier (z : ℂ) : ℂ :=
  gaussianScaleDifference (1 / 2) z * (archivedMellin (z / 7) / 7)

theorem archivedGaussianVaughanMultiplier_entire :
    Differentiable ℂ archivedGaussianVaughanMultiplier := by
  have hD : Differentiable ℂ (gaussianScaleDifference (1 / 2)) := by
    unfold gaussianScaleDifference
    fun_prop
  exact hD.mul
    (((archivedMellin_differentiable archivedTheta_reflection).comp
      (differentiable_id.div_const (7 : ℂ))).div_const 7)

theorem archivedGaussianVaughanMultiplier_ne_zero
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hz : archivedGaussianFactor ρ = 0) :
    archivedGaussianVaughanMultiplier ρ ≠ 0 := by
  have hr : 0 < ρ.re := by linarith
  have hs : 0 < (ρ / 7).re := by rw [div_ofNat_re]; positivity
  have hbelow := archivedGaussian_seventhFree_numerator_ne_zero hFree hr hz
  exact mul_ne_zero (gaussianHalfScale_zero_ne_zero hρ).2
    (div_ne_zero (fun h => hbelow ((archivedGaussianFactor_zero_iff_mellin hs).mpr h))
      (by norm_num))

def archivedGaussianVaughanMellin (z : ℂ) : ℂ :=
  archivedGaussianVaughanMultiplier z * (-logDeriv archivedGaussianFactor z)

theorem archivedGaussianVaughanMellin_eq_series {z : ℂ} (hz : 1 < z.re) :
    archivedGaussianVaughanMellin z =
      archivedGaussianVaughanMultiplier z * LSeries archivedGaussianMangoldt z := by
  rw [archivedGaussianVaughanMellin, archivedGaussianMangoldt_eq_neg_logDeriv hz]

theorem archivedGaussianVaughanMellin_analytic {z : ℂ}
    (hz : archivedGaussianFactor z ≠ 0) : AnalyticAt ℂ archivedGaussianVaughanMellin z := by
  have hG := archivedGaussianFactor_entire.analyticAt z
  exact (archivedGaussianVaughanMultiplier_entire.analyticAt z).mul
    (hG.deriv.div hG hz).neg

/-- The residue is exactly minus the multiplicity times the multiplier at
the same Gaussian zero. The multiplier is nonzero under the boundary input. -/
theorem archivedGaussianVaughanMellin_pole
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hz : archivedGaussianFactor ρ = 0) :
    ∃ n : ℕ, 0 < n ∧ analyticOrderAt archivedGaussianFactor ρ = n ∧
      (-(n : ℂ) * archivedGaussianVaughanMultiplier ρ) ≠ 0 ∧
      ∃ b : ℂ → ℂ, AnalyticAt ℂ b ρ ∧
        ∀ᶠ z in 𝓝[≠] ρ, archivedGaussianVaughanMellin z =
          (-(n : ℂ) * archivedGaussianVaughanMultiplier ρ) / (z - ρ) + b z := by
  have hG := archivedGaussianFactor_entire.analyticAt ρ
  have hfinite : analyticOrderAt archivedGaussianFactor ρ ≠ ⊤ := by
    intro htop
    have hzero : archivedGaussianFactor =ᶠ[𝓝 ρ] fun _ => 0 :=
      analyticOrderAt_eq_top.mp htop
    have hall := AnalyticOnNhd.eq_of_eventuallyEq
      (fun z _ => archivedGaussianFactor_entire.analyticAt z) analyticOnNhd_const hzero
    exact quartic_gaussian_one_ne_zero (congrFun hall 1)
  let n := analyticOrderNatAt archivedGaussianFactor ρ
  have hn : analyticOrderAt archivedGaussianFactor ρ = n :=
    (Nat.cast_analyticOrderNatAt hfinite).symm
  have hn₀ : n ≠ 0 := by
    intro h
    exact (hG.analyticOrderAt_ne_zero.mpr hz) (by simpa [h] using hn)
  obtain ⟨b, hb, hnear⟩ := gaussianNegLogDeriv_local hG hn
  let M := archivedGaussianVaughanMultiplier
  have hM : AnalyticAt ℂ M ρ := archivedGaussianVaughanMultiplier_entire.analyticAt ρ
  refine ⟨n, Nat.pos_of_ne_zero hn₀, hn, mul_ne_zero
    (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hn₀))
    (archivedGaussianVaughanMultiplier_ne_zero hFree hρ hz),
    fun z => dslope M ρ z * (-(n : ℂ)) + M z * b z,
    ((Deduction.poleData_dslope hM).mul analyticAt_const).add (hM.mul hb), ?_⟩
  filter_upwards [hnear, self_mem_nhdsWithin] with z hzEq hne
  change z ≠ ρ at hne
  rw [archivedGaussianVaughanMellin, hzEq, dslope_of_ne _ hne, slope_def_field]
  change M z * (-(n : ℂ) / (z - ρ) + b z) =
    (-(n : ℂ) * M ρ) / (z - ρ) + ((M z - M ρ) / (z - ρ) * -(n : ℂ) + M z * b z)
  ring

def archivedGaussianVaughanKernel (v : ℝ) : ℝ :=
  archivedGaussianSeventhFreeKernel v -
    Real.exp (1 / 2 * Real.log 2) * archivedGaussianSeventhFreeKernel (2 * v)

def archivedGaussianVaughanSum (x : ℝ) : ℝ :=
  if 0 < x then ∑' n : ℕ, (archivedGaussianMangoldt n).re *
    archivedGaussianVaughanKernel (n / x) else 0

def archivedGaussianVaughanConvolvedKernel (v : ℝ) : ℝ :=
  ∑' n : ℕ, (signedIdealCoefficients n).re * archivedGaussianVaughanKernel (n * v)

/-- The actual complementary prime window, including the minus sign. -/
def archivedGaussianVaughanLowerSum (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  let ℓ := Real.log x
  let V := x / ℓ ^ (5 / 2 : ℝ)
  let primes := (Finset.range (Nat.floor (2 * V) + 1)).filter
    (fun p : ℕ => p.Prime ∧ x / ℓ ^ (5 : ℕ) < (p : ℝ))
  let term (m : ℕ) :=
    (archivedGaussianMoebiusCoefficients m).re *
      ∑ p ∈ primes, (archivedGaussianMangoldt p).re * W (p / V) *
        archivedGaussianVaughanConvolvedKernel (m * p / x)
  if 1 < x then -(∑ m ∈ Finset.Icc 1 (Nat.floor (ℓ ^ (8 / 3 : ℝ))), term m) else 0

theorem archivedGaussianVaughanSum_measurable : Measurable archivedGaussianVaughanSum := by
  have ht : Measurable archivedTheta := by
    unfold archivedTheta
    exact Measurable.tsum fun n =>
      (continuous_const.mul ((Real.continuous_exp.comp continuous_neg).pow n)).measurable
  have hH : Measurable archivedGaussianSeventhFreeKernel :=
    ht.comp ((continuous_pow 7).div_const archivedThetaScale).measurable
  have hD : Measurable archivedGaussianVaughanKernel :=
    hH.sub (measurable_const.mul (hH.comp (continuous_const.mul continuous_id).measurable))
  unfold archivedGaussianVaughanSum
  exact Measurable.ite measurableSet_Ioi
    (Measurable.tsum fun _ => measurable_const.mul
      (hD.comp (measurable_const.div measurable_id))) measurable_const

/-- An error of the size from the contour shift can be absorbed by one
constant on the same arbitrarily late windows. -/
theorem gaussianLogWindow_error_transfer {F T : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ᶠ x in atTop, |F x - T x| ≤ C * (x ^ (3 / 8 : ℝ) *
      (Real.log x) ^ (8 / 3 : ℝ))) (hT : GaussianCutoffWindowBound T) :
    GaussianCutoffWindowBound F := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (8 / 3 : ℝ)
    (show (0 : ℝ) < 1 / 8 by norm_num)).def (show (0 : ℝ) < 1 by norm_num)
  have hl : ∀ᶠ x : ℝ in atTop, F x ≤ T x + C * x ^ (1 / 2 : ℝ) := by
    filter_upwards [hE, hlog, eventually_ge_atTop (1 : ℝ)] with x hx hg hx₁
    have hx₀ : 0 < x := zero_lt_one.trans_le hx₁
    have hg' : (Real.log x) ^ (8 / 3 : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
      simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx₁) _),
        Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _), one_mul] using hg
    have hpow : x ^ (3 / 8 : ℝ) * x ^ (1 / 8 : ℝ) = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hx₀]
      norm_num
    have hh := (le_abs_self (F x - T x)).trans hx
    exact (sub_le_iff_le_add.mp hh).trans (by
      rw [add_comm (T x), ← hpow]
      exact add_le_add_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hg' (Real.rpow_nonneg hx₀.le _)) hC) _)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hl
  intro θ hθ hθ₁
  obtain ⟨δ, hδ, D, hD, hLate⟩ := hT θ hθ hθ₁
  refine ⟨δ, hδ, D + C, add_nonneg hD hC, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hW⟩ := hLate (max Y₀ (max x₀ 1))
  refine ⟨Y, (le_max_left _ _).trans hY, fun x hx => ?_⟩
  have hx₁ : 1 ≤ x := (le_max_right x₀ 1).trans ((le_max_right Y₀ _).trans (hY.trans hx.1))
  have hx₀' : x₀ ≤ x := (le_max_left x₀ 1).trans ((le_max_right Y₀ _).trans (hY.trans hx.1))
  calc
    F x ≤ T x + C * x ^ (1 / 2 : ℝ) := hx₀ x hx₀'
    _ ≤ D * x ^ θ + C * x ^ θ := add_le_add (hW x hx)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx₁ hθ.le) hC)
    _ = (D + C) * x ^ θ := (add_mul _ _ _).symm

/-- Given the transform from one to infinity and the contour error, the
one-sided bound for the actual complementary reading suffices. No local
pole, regularity off the zeros, or real-residue assumption is needed. -/
theorem quartic_rh_of_archived_vaughan_lower_windows
    (hDir : DirichletLZerosOnLine)
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (W : ℝ → ℝ) (E : ℂ → ℂ) (hEntire : Differentiable ℂ E)
    (hGrowth : ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ),
      |archivedGaussianVaughanSum x| ≤ C * x ^ (2 : ℝ))
    (hTransform : ∀ z : ℂ, 2 < z.re →
      ∫ x in Ioi (1 : ℝ), (archivedGaussianVaughanSum x : ℂ) * (x : ℂ) ^ (-z - 1) =
        archivedGaussianVaughanMellin z - E z)
    {C : ℝ} (hC : 0 ≤ C)
    (hError : ∀ᶠ x in atTop,
      |archivedGaussianVaughanSum x - archivedGaussianVaughanLowerSum W x| ≤
        C * (x ^ (3 / 8 : ℝ) * (Real.log x) ^ (8 / 3 : ℝ)))
    (hcut : GaussianCutoffWindowBound (archivedGaussianVaughanLowerSum W)) :
    DedekindZetaRH QuarticModel.K := by
  have hReal := gaussian_poles_nonreal_of_mellin_pos (fun σ _ =>
    archivedMellin_eq_quartic_real_formula ▸ hpos σ)
  refine quartic_rh_of_gaussian_mellin_windows hDir archivedGaussianVaughanSum_measurable
    hGrowth (Φ := fun z => archivedGaussianVaughanMellin z - E z)
    (fun z _ hz => (archivedGaussianVaughanMellin_analytic hz).sub (hEntire.analyticAt z))
    ?_ hTransform (gaussianLogWindow_error_transfer hC hError hcut)
  intro ρ hρ hhalf
  obtain ⟨n, _, _, hc, b, hb, hnear⟩ := archivedGaussianVaughanMellin_pole hFree hhalf hρ.2
  refine ⟨_, hc, fun him => (hReal ρ hρ him).elim, fun z => b z - E z,
    hb.sub (hEntire.analyticAt ρ), ?_⟩
  filter_upwards [hnear] with z hz
  rw [hz]
  ring

#print axioms gaussianNegLogDeriv_local
#print axioms archivedGaussianVaughanMultiplier_entire
#print axioms archivedGaussianVaughanMultiplier_ne_zero
#print axioms archivedGaussianVaughanMellin_eq_series
#print axioms archivedGaussianVaughanMellin_analytic
#print axioms archivedGaussianVaughanMellin_pole
#print axioms archivedGaussianVaughanSum_measurable
#print axioms gaussianLogWindow_error_transfer
#check quartic_rh_of_archived_vaughan_lower_windows
#print axioms quartic_rh_of_archived_vaughan_lower_windows

end
end AlpogeSuperZeta
