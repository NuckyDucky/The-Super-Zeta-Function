import GaussianHigherPrimePowers

/-! Remove the compensated contribution of higher prime powers from the
one-sided norm-window hypothesis for the actual Gaussian factor. -/

namespace AlpogeSuperZeta

open ArithmeticFunction ArtinPrimitiveRootsConjecture Filter Set
open scoped Classical

noncomputable section

/-- The adjustment to the linear term after removing all higher prime powers. -/
def gaussianHigherPrimeLinearCoefficient : ℝ :=
  ∑' n : ℕ, gaussianHigherPrimeCoefficient n / n

/-- The archived ramp evaluated with just ordinary primes and the corrected linear term. -/
def archivedGaussianPrimeOnlyRamp (x : ℝ) : ℝ :=
  gaussianPrimeNormRamp (fun n => if n.Prime then archivedGaussianPrimeWeight n else 0) x +
    gaussianHigherPrimeLinearCoefficient * x

private theorem gaussianPrimeNormRamp_real (a : ℕ → ℝ) (x : ℝ) :
    gaussianPrimeNormRamp a x =
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1), vonMangoldt n * a n * max (x / n - 1) 0) +
        (logDeriv QuarticModel.archivedGaussianFactor 1).re * x := by
  simp only [gaussianPrimeNormRamp, Deduction.ramp, Complex.re_sum, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- Exact higher-power error after correcting the linear term. -/
theorem archivedGaussianPrimeOnlyRamp_sub {x : ℝ} (hx : 0 ≤ x) :
    gaussianPrimeNormRamp archivedGaussianPrimeWeight x - archivedGaussianPrimeOnlyRamp x =
      -(∑' n : ℕ, gaussianHigherPrimeCoefficient n * min 1 (x / n)) := by
  let b := gaussianHigherPrimeCoefficient
  let S := Finset.range (⌊x⌋₊ + 1)
  let f (n : ℕ) := b n * max (x / n - 1) 0
  let g (n : ℕ) := (b n / n) * x
  have hf0 (n : ℕ) (hn : n ∉ S) : f n = 0 := by
    have hx' : x < (n : ℝ) := Nat.lt_of_floor_lt (by
      simpa [S, Finset.mem_range, Nat.lt_succ_iff] using hn)
    have hnpos := hx.trans_lt hx'
    simp [f, max_eq_right (sub_nonpos.mpr ((div_le_one₀ hnpos).mpr hx'.le))]
  have hf : HasSum f (∑ n ∈ S, f n) := hasSum_sum_of_ne_finset_zero hf0
  have hg_base : Summable (fun n : ℕ => b n / n) := by
    apply Summable.of_abs
    have hcast (n : ℕ) : |(n : ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg n)
    change Summable (fun n : ℕ => |gaussianHigherPrimeCoefficient n / (n : ℝ)|)
    simp only [abs_div, hcast]
    simpa only [Real.rpow_one] using (gaussianHigherPrime_summable (θ := 1) (by norm_num))
  have hg : HasSum g (gaussianHigherPrimeLinearCoefficient * x) := hg_base.hasSum.mul_right x
  have hterms (n : ℕ) : f n - g n = -(b n * min 1 (x / n)) := by
    dsimp [f, g]
    rw [show b n / (n : ℝ) * x = b n * (x / n) by ring]
    by_cases h : x / (n : ℝ) ≤ 1
    · rw [max_eq_right (sub_nonpos.mpr h), min_eq_right h]
      ring
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h)), min_eq_left (le_of_not_ge h)]
      ring
  have hsum := hf.sub hg
  have heq : (fun n => f n - g n) = fun n => -(b n * min 1 (x / n)) := funext hterms
  rw [heq] at hsum
  rw [← tsum_neg, hsum.tsum_eq, archivedGaussianPrimeOnlyRamp, gaussianPrimeNormRamp_real,
    gaussianPrimeNormRamp_real]
  have hsplit :
      (∑ n ∈ S, vonMangoldt n * archivedGaussianPrimeWeight n * max (x / n - 1) 0) -
      (∑ n ∈ S, vonMangoldt n * (if n.Prime then archivedGaussianPrimeWeight n else 0) *
        max (x / n - 1) 0) = ∑ n ∈ S, f n := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : n.Prime <;> simp [f, b, gaussianHigherPrimeCoefficient, h]
  change _ = (∑ n ∈ S, f n) - _
  rw [← hsplit]
  ring

private theorem min_one_le_rpow {t θ : ℝ} (ht : 0 < t) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    min 1 t ≤ t ^ θ := by
  by_cases h : t ≤ 1
  · rw [min_eq_right h]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht h hθ₁
  · rw [min_eq_left (le_of_not_ge h), ← Real.one_rpow θ]
    exact Real.rpow_le_rpow zero_le_one (le_of_not_ge h) hθ₀

/-- A uniform bound for the actual higher-power error at every x ≥ 1. -/
theorem archivedGaussianPrimeOnlyRamp_error {θ : ℝ} (hθ₀ : 1 / 2 < θ) (hθ₁ : θ ≤ 1) :
    ∃ D ≥ 0, ∀ x ≥ (1 : ℝ),
      |gaussianPrimeNormRamp archivedGaussianPrimeWeight x - archivedGaussianPrimeOnlyRamp x| ≤
        D * x ^ θ := by
  let b := gaussianHigherPrimeCoefficient
  let a (n : ℕ) := |b n| / (n : ℝ) ^ θ
  have ha : Summable a := gaussianHigherPrime_summable hθ₀
  have ha₀ (n : ℕ) : 0 ≤ a n := by dsimp [a]; positivity
  refine ⟨∑' n : ℕ, a n, tsum_nonneg ha₀, fun x hx => ?_⟩
  have hxpos := zero_lt_one.trans_le hx
  rw [archivedGaussianPrimeOnlyRamp_sub hxpos.le, abs_neg, ← ha.tsum_mul_right]
  let f (n : ℕ) := b n * min 1 (x / n)
  have hterm (n : ℕ) : |f n| ≤ a n * x ^ θ := by
    by_cases hn : n = 0
    · subst n
      simp [f, a, b, gaussianHigherPrimeCoefficient]
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hd := div_pos hxpos hnpos
    have hmin := min_one_le_rpow hd (by linarith : 0 ≤ θ) hθ₁
    change |b n * min 1 (x / n)| ≤ a n * x ^ θ
    rw [abs_mul, abs_of_nonneg (le_min zero_le_one hd.le)]
    calc
      _ ≤ |b n| * (x / n) ^ θ := mul_le_mul_of_nonneg_left hmin (abs_nonneg _)
      _ = a n * x ^ θ := by
        simp only [Real.div_rpow hxpos.le hnpos.le, a]
        ring
  have habs : Summable (fun n => |f n|) :=
    (ha.mul_right _).of_nonneg_of_le (fun _ => abs_nonneg _) hterm
  calc
    |∑' n, f n| ≤ ∑' n, |f n| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := f) (by simpa only [Real.norm_eq_abs] using habs))
    _ ≤ ∑' n, a n * x ^ θ := habs.tsum_le_tsum hterm (ha.mul_right _)

/-- The same one-sided cutoff condition, using only primes and the adjusted linear term. -/
def ArchivedGaussianPrimeOnlyWindowBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C ≥ 0, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
      ∀ y ∈ Icc Y (Y ^ (1 + δ)), archivedGaussianPrimeOnlyRamp y ≤ C * y ^ θ

private theorem window_bound_of_le_add {f g : ℝ → ℝ} {θ δ C D : ℝ}
    (h : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)), g y ≤ C * y ^ θ)
    (herr : ∀ x ≥ (1 : ℝ), f x ≤ g x + D * x ^ θ) :
    ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)), f y ≤ (C + D) * y ^ θ := by
  intro Y₀
  obtain ⟨Y, hY, hg⟩ := h (max Y₀ 1)
  refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
  have h1 := (le_max_right Y₀ (1 : ℝ)).trans (hY.trans hy.1)
  rw [add_mul]
  exact (herr y h1).trans (add_le_add (hg y hy) le_rfl)

/-- Prime powers and primes give equivalent window conditions for the actual quartic. -/
theorem archivedGaussianPrimeWindowBound_iff_prime_only :
    ArchivedGaussianPrimeWindowBound ↔ ArchivedGaussianPrimeOnlyWindowBound := by
  constructor
  · intro h θ hθ₀ hθ₁
    obtain ⟨δ, hδ, C, hC, hW⟩ := h θ hθ₀ hθ₁
    obtain ⟨D, hD, herr⟩ := archivedGaussianPrimeOnlyRamp_error hθ₀ hθ₁.le
    refine ⟨δ, hδ, C + D, add_nonneg hC hD, window_bound_of_le_add hW ?_⟩
    intro x hx
    linarith [(abs_le.mp (herr x hx)).1]
  · intro h θ hθ₀ hθ₁
    obtain ⟨δ, hδ, C, hC, hW⟩ := h θ hθ₀ hθ₁
    obtain ⟨D, hD, herr⟩ := archivedGaussianPrimeOnlyRamp_error hθ₀ hθ₁.le
    refine ⟨δ, hδ, C + D, add_nonneg hC hD, window_bound_of_le_add hW ?_⟩
    intro x hx
    linarith [(abs_le.mp (herr x hx)).2]

theorem quartic_rh_of_archived_gaussian_prime_only_windows (hD : DirichletLZerosOnLine)
    (hcut : ArchivedGaussianPrimeOnlyWindowBound) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_window_bound hD
    (archivedGaussianPrimeWindowBound_iff_prime_only.mpr hcut)

/-- Divide the corrected Gaussian ramp by the cutoff to put the estimate
on the same scale as the normalized prime error in the Dirichlet proof. -/
def archivedGaussianPrimeError (x : ℝ) : ℝ :=
  archivedGaussianPrimeOnlyRamp x / x

theorem archivedGaussianPrimeError_le_iff {x θ C : ℝ} (hx : 0 < x) :
    archivedGaussianPrimeError x ≤ C * x ^ (θ - 1) ↔
      archivedGaussianPrimeOnlyRamp x ≤ C * x ^ θ := by
  rw [archivedGaussianPrimeError, div_le_iff₀ hx, mul_assoc, Real.rpow_sub hx,
    Real.rpow_one, div_mul_cancel₀ _ hx.ne']

/-- An eventual one-sided estimate on the normalized Gaussian prime error
would supply the cofinal windows used in the quartic deduction. -/
theorem quartic_rh_of_archived_gaussian_prime_error (hD : DirichletLZerosOnLine)
    (hcut : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ C ≥ 0, ∀ᶠ x in atTop, archivedGaussianPrimeError x ≤ C * x ^ (θ - 1)) :
    DedekindZetaRH QuarticModel.K := by
  apply quartic_rh_of_archived_gaussian_prime_only_windows hD
  intro θ hθ₀ hθ₁
  obtain ⟨C, hC, hE⟩ := hcut θ hθ₀ hθ₁
  obtain ⟨X, hX⟩ := eventually_atTop.mp hE
  refine ⟨1, zero_lt_one, C, hC, fun Y₀ => ?_⟩
  let Y := max (max X 1) Y₀
  refine ⟨Y, le_max_right _ _, fun y hy => ?_⟩
  have hXy : X ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy.1)
  have h1y : (1 : ℝ) ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy.1)
  exact (archivedGaussianPrimeError_le_iff (zero_lt_one.trans_le h1y)).mp (hX y hXy)

#print axioms archivedGaussianPrimeOnlyRamp_sub
#print axioms archivedGaussianPrimeOnlyRamp_error
#print axioms archivedGaussianPrimeWindowBound_iff_prime_only
#check quartic_rh_of_archived_gaussian_prime_only_windows
#print axioms quartic_rh_of_archived_gaussian_prime_only_windows
#print axioms archivedGaussianPrimeError_le_iff
#check quartic_rh_of_archived_gaussian_prime_error
#print axioms quartic_rh_of_archived_gaussian_prime_error

end
end AlpogeSuperZeta
