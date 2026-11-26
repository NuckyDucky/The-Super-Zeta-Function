import GaussianAveragedPrimeWindow

/-! The quartic criterion with signed prime prefixes on intervals of exponent \(3/2\). -/

namespace AlpogeSuperZeta

open ArtinPrimitiveRootsConjecture FieldTarget MeasureTheory Set

noncomputable section

private theorem cutoff_integrableOn_of_bound {A : ℝ → ℝ} (hm : Measurable A) {x C e : ℝ}
    (he : 0 ≤ e) (hC : 0 ≤ C) (hA : ∀ t ≥ (1 : ℝ), |A t| ≤ C * t ^ e) :
    IntegrableOn A (Ioc 1 x) := by
  have hconst : IntegrableOn (fun _ : ℝ => C * x ^ e) (Ioc 1 x) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  apply hconst.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact (hA t ht.1.le).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (zero_le_one.trans ht.1.le) ht.2 he) hC)

private theorem averagedSquaredWindow_prime_error {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) :
    ∃ E ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ),
      |averagedCutoff archivedGaussianSquaredWindow x -
        averagedCutoff archivedGaussianPrimeSquaredWindow x| ≤ E * x ^ θ := by
  let R := archivedGaussianSquaredWindow
  let P := archivedGaussianPrimeSquaredWindow
  obtain ⟨D, hD, hErr⟩ := archivedGaussianPrimeSquaredWindow_error hθ hθ₁
  obtain ⟨C, hC, hRaw⟩ := archivedGaussianSquaredWindow_growth
  have hRm : Measurable R := indexedSquaredRamp_measurable _ _
  have hPm : Measurable P := by
    unfold P archivedGaussianPrimeSquaredWindow
    apply (indexedSquaredRamp_measurable _ _).sub
    fun_prop
  have hPrime (x : ℝ) (hx : 1 ≤ x) : |P x| ≤ (C + D) * x ^ (2 : ℝ) := by
    have hDiff : |P x - R x| ≤ D * x ^ θ := by rw [abs_sub_comm]; exact hErr x hx
    calc
      _ = |P x - R x + R x| := by rw [sub_add_cancel]
      _ ≤ |P x - R x| + |R x| := abs_add_le _ _
      _ ≤ D * x ^ θ + C * x ^ (2 : ℝ) := add_le_add hDiff (hRaw x hx)
      _ ≤ D * x ^ (2 : ℝ) + C * x ^ (2 : ℝ) := add_le_add
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hD) le_rfl
      _ = _ := by ring
  refine ⟨3 * D, by positivity, fun x hx => ?_⟩
  have h₂ : 0 ≤ (2 : ℝ) := by norm_num
  have hRi := cutoff_integrableOn_of_bound (x := x) hRm h₂ hC hRaw
  have hPi := cutoff_integrableOn_of_bound (x := x) hPm h₂ (add_nonneg hC hD) hPrime
  have hEq : averagedCutoff R x - averagedCutoff P x = averagedCutoff (fun t => R t - P t) x := by
    unfold averagedCutoff
    rw [integral_sub hRi hPi]
    ring
  change |averagedCutoff R x - averagedCutoff P x| ≤ _
  rw [hEq]
  exact averagedCutoff_abs_le hx (by linarith : 0 ≤ θ) hD hErr

/-- Eventual windows on which the cumulative signed prime prefix has an upper bound. -/
def ArchivedGaussianThreeHalvesPrimeWindows (θ : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ n : ℕ,
    Y ≤ (n : ℝ) → (n : ℝ) ≤ Y ^ (3 / 2 : ℝ) →
      archivedGaussianSignedPrimePrefix n ≤ A * (n : ℝ) ^ θ

theorem averagedPrimeSquaredWindowBound_of_three_halves_prime_windows {B : ℝ}
    (hB : 0 ≤ B)
    (hglobal : ∀ n : ℕ, archivedGaussianSignedPrimePrefix n ≤ B * (n : ℝ) ^ (7 / 8 : ℝ))
    (hWindows : ∀ θ : ℝ, 1 / 2 < θ → θ ≤ 3 / 4 → ArchivedGaussianThreeHalvesPrimeWindows θ) :
    GaussianCutoffWindowBound (averagedCutoff archivedGaussianPrimeSquaredWindow) := by
  intro θ hθ _
  let t := min θ (3 / 4 : ℝ)
  have ht : 1 / 2 < t := lt_min hθ (by norm_num)
  have ht₀ : t ≤ 3 / 4 := min_le_right _ _
  have he : 0 < t - 1 / 2 := sub_pos.mpr ht
  obtain ⟨A, hA, hlocal⟩ := hWindows t ht ht₀
  let C := A / 2 + 2 * B * (1 + (2 / 3) / (t - 1 / 2)) + |archivedGaussianPrimeCenter| / 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨1 / 5, by norm_num, C, hC, fun y₀ => ?_⟩
  obtain ⟨Y, hY', hP⟩ := hlocal (max 1 y₀)
  have hY : 1 ≤ Y := (le_max_left 1 y₀).trans hY'
  let y := Y ^ (5 / 4 : ℝ)
  have hy : Y ≤ y := by
    nth_rw 1 [← Real.rpow_one Y]
    exact Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
  refine ⟨y, ((le_max_right 1 y₀).trans hY').trans hy, fun x hx => ?_⟩
  have hYpow : y ^ (1 + (1 / 5 : ℝ)) = Y ^ (3 / 2 : ℝ) := by
    dsimp [y]
    rw [← Real.rpow_mul (zero_le_one.trans hY)]
    norm_num
  have hh := averagedPrimeSquaredWindow_le_of_local_prefix hY hx.1 (hx.2.trans_eq hYpow) ht hA hB
    hglobal hP
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hY.trans (hy.trans hx.1)) (min_le_left _ _)) hC)

/-- On the actual quartic, the prefixes before each local window need only the
global one-sided estimate at exponent \(7/8\). -/
theorem quartic_rh_of_three_halves_prime_windows
    (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    {B : ℝ} (hB : 0 ≤ B)
    (hglobal : ∀ n : ℕ, archivedGaussianSignedPrimePrefix n ≤ B * (n : ℝ) ^ (7 / 8 : ℝ))
    (hWindows : ∀ θ : ℝ, 1 / 2 < θ → θ ≤ 3 / 4 → ArchivedGaussianThreeHalvesPrimeWindows θ) :
    DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_averaged_squared_windows hD hpos
    ((gaussianCutoffWindowBound_iff_of_error (X₀ := 1)
      (fun _ => averagedSquaredWindow_prime_error)).mpr
      (averagedPrimeSquaredWindowBound_of_three_halves_prime_windows hB hglobal hWindows))

#print axioms averagedSquaredWindow_prime_error
#print axioms averagedPrimeSquaredWindowBound_of_three_halves_prime_windows
#check quartic_rh_of_three_halves_prime_windows
#print axioms quartic_rh_of_three_halves_prime_windows

end

end AlpogeSuperZeta
