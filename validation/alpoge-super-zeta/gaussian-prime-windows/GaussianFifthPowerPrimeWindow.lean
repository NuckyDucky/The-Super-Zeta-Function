import GaussianLocalPrimeWindow

/-! A cofinal prime-prefix criterion for the archived quartic's norm windows. -/

namespace AlpogeSuperZeta

open ArtinPrimitiveRootsConjecture FieldTarget Set

noncomputable section

/-- A one-sided signed prefix estimate throughout arbitrarily late intervals \([Y,Y^5]\). -/
def ArchivedGaussianFifthPowerPrimeWindows (θ : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
    ∀ n : ℕ, Y ≤ (n : ℝ) → (n : ℝ) ≤ Y ^ (5 : ℝ) →
      archivedGaussianSignedPrimePrefix n ≤ A * (n : ℝ) ^ θ

/-- Within a fifth-power prime window, the two remote terms are absorbed on the interior
interval \([Y^{5/4}, Y^{5/(8(1-\theta))}]\). -/
theorem archivedGaussianPrimeSquaredWindow_le_in_fifth_power_window {x Y θ A B : ℝ}
    (hY : 1 ≤ Y) (hθ : 1 / 2 < θ) (hθ₁ : θ < 7 / 8) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hl : Y ^ (5 / 4 : ℝ) ≤ x) (hu : x ≤ Y ^ (5 / (8 * (1 - θ))))
    (hcenter : ArchivedGaussianPrimeCenterLimit)
    (hglobal : ∀ n : ℕ, |archivedGaussianSignedPrimePrefix n| ≤ B * (n : ℝ) ^ (7 / 8 : ℝ))
    (hlocal : ∀ n : ℕ, Y ≤ (n : ℝ) → (n : ℝ) ≤ Y ^ (5 : ℝ) →
      archivedGaussianSignedPrimePrefix n ≤ A * (n : ℝ) ^ θ) :
    archivedGaussianPrimeSquaredWindow x ≤
      (A * (1 / 2 + 1 / (3 * (1 - θ))) + 10 / 3 * B) * x ^ θ := by
  let η : ℝ := 7 / 8
  let Z := Y ^ (5 : ℝ)
  have hη₀ : 0 ≤ η := by norm_num [η]
  have hη₁ : η < 1 := by norm_num [η]
  have hθ₀ : 0 ≤ θ := by linarith
  have hθ' : θ < 1 := by linarith
  have hbar : 0 < 1 - θ := sub_pos.mpr hθ'
  have hY₀ : 0 < Y := one_pos.trans_le hY
  have hYx : Y ≤ x := by
    calc
      Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
      _ ≤ Y ^ (5 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
      _ ≤ x := hl
  have hx₀ := hY₀.trans_le hYx
  have hxZ : x ≤ Z := hu.trans (Real.rpow_le_rpow_of_exponent_le hY (by
    apply (div_le_iff₀ (show 0 < 8 * (1 - θ) by positivity)).mpr
    linarith))
  have hZ₀ : 0 < Z := Real.rpow_pos_of_pos hY₀ _
  have hlow : Y * Y ^ η ≤ x * x ^ θ := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hY₀.le _) hl (show 0 ≤ 1 + θ by linarith)
    rw [← Real.rpow_mul hY₀.le] at h
    calc
      Y * Y ^ η = Y ^ (1 + η) := by rw [Real.rpow_add hY₀, Real.rpow_one]
      _ ≤ Y ^ ((5 / 4) * (1 + θ)) := Real.rpow_le_rpow_of_exponent_le hY (by dsimp [η]; linarith)
      _ ≤ x ^ (1 + θ) := h
      _ = x * x ^ θ := by rw [Real.rpow_add hx₀, Real.rpow_one]
  have hhigh : x ^ (1 - θ) ≤ Z ^ (1 - η) := by
    have h := Real.rpow_le_rpow hx₀.le hu hbar.le
    rw [← Real.rpow_mul hY₀.le] at h
    rw [show 5 / (8 * (1 - θ)) * (1 - θ) = 5 * (1 - η) by
      dsimp [η]
      field_simp
      norm_num] at h
    rwa [Real.rpow_mul hY₀.le] at h
  have hL : B * (Y + 1) * Y ^ η / (3 * x) ≤ (2 / 3 * B) * x ^ θ := by
    have h := mul_le_mul_of_nonneg_right (show Y + 1 ≤ 2 * Y by linarith)
      (Real.rpow_nonneg hY₀.le η)
    have h' : (Y + 1) * Y ^ η ≤ 2 * (x * x ^ θ) := by
      calc
        _ ≤ (2 * Y) * Y ^ η := h
        _ = 2 * (Y * Y ^ η) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by norm_num)
    apply (div_le_iff₀ (show 0 < 3 * x by positivity)).mpr
    calc
      _ = B * ((Y + 1) * Y ^ η) := by ring
      _ ≤ B * (2 * (x * x ^ θ)) := mul_le_mul_of_nonneg_left h' hB
      _ = _ := by ring
  have hU : B * x / (3 * (1 - η)) * Z ^ (η - 1) ≤ (8 / 3 * B) * x ^ θ := by
    have hratio : x ^ (1 - θ) * Z ^ (η - 1) ≤ 1 := by
      rw [show η - 1 = -(1 - η) by ring, Real.rpow_neg hZ₀.le, ← div_eq_mul_inv]
      exact (div_le_one (Real.rpow_pos_of_pos hZ₀ _)).mpr hhigh
    have hfactor : x = x ^ θ * x ^ (1 - θ) := by
      rw [← Real.rpow_add hx₀, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
    calc
      _ = ((8 / 3 * B) * x ^ θ) * (x ^ (1 - θ) * Z ^ (η - 1)) := by
        conv_lhs => rw [hfactor]
        dsimp [η]
        ring
      _ ≤ ((8 / 3 * B) * x ^ θ) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := mul_one _
  have h := archivedGaussianPrimeSquaredWindow_le_of_local_prefix hY hYx hxZ
    hθ₀ hθ' hη₀ hη₁ hA hB hcenter hglobal hlocal
  calc
    _ ≤ A * (1 / 2 + 1 / (3 * (1 - θ))) * x ^ θ +
        B * (Y + 1) * Y ^ η / (3 * x) + B * x / (3 * (1 - η)) * Z ^ (η - 1) := h
    _ ≤ A * (1 / 2 + 1 / (3 * (1 - θ))) * x ^ θ +
        (2 / 3 * B) * x ^ θ + (8 / 3 * B) * x ^ θ :=
      add_le_add (add_le_add le_rfl hL) hU
    _ = _ := by ring

theorem archivedGaussianPrimeSquaredWindowBound_of_fifth_power_prime_windows {B : ℝ}
    (hB : 0 ≤ B) (hcenter : ArchivedGaussianPrimeCenterLimit)
    (hglobal : ∀ n : ℕ, |archivedGaussianSignedPrimePrefix n| ≤ B * (n : ℝ) ^ (7 / 8 : ℝ))
    (hwindows : ∀ θ : ℝ, 1 / 2 < θ → θ ≤ 3 / 4 → ArchivedGaussianFifthPowerPrimeWindows θ) :
    GaussianCutoffWindowBound archivedGaussianPrimeSquaredWindow := by
  intro θ hθ _
  let t := min θ (3 / 4 : ℝ)
  have ht : 1 / 2 < t := lt_min hθ (by norm_num)
  have ht₀ : t ≤ 3 / 4 := min_le_right _ _
  have ht₁ : t < 7 / 8 := ht₀.trans_lt (by norm_num)
  have hb : 0 < 1 - t := by linarith
  obtain ⟨A, hA, hlocal⟩ := hwindows t ht ht₀
  let δ := 1 / (2 * (1 - t)) - 1
  let C := A * (1 / 2 + 1 / (3 * (1 - t))) + 10 / 3 * B
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sub_pos.mpr ((lt_div_iff₀ (show 0 < 2 * (1 - t) by positivity)).mpr (by linarith))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨δ, hδ, C, hC, fun y₀ => ?_⟩
  obtain ⟨Y, hY', hP⟩ := hlocal (max 1 y₀)
  have hY : 1 ≤ Y := (le_max_left 1 y₀).trans hY'
  let y := Y ^ (5 / 4 : ℝ)
  have hy : Y ≤ y := by
    nth_rw 1 [← Real.rpow_one Y]
    exact Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
  refine ⟨y, ((le_max_right 1 y₀).trans hY').trans hy, fun x hx => ?_⟩
  have hYpower : y ^ (1 + δ) = Y ^ (5 / (8 * (1 - t))) := by
    dsimp [y]
    rw [← Real.rpow_mul (zero_le_one.trans hY)]
    congr 1
    dsimp [δ]
    field_simp
    ring
  have h := archivedGaussianPrimeSquaredWindow_le_in_fifth_power_window hY ht ht₁ hA hB
    hx.1 (hx.2.trans_eq hYpower) hcenter hglobal hP
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hY.trans (hy.trans hx.1)) (min_le_left _ _)) hC)

namespace GaussianQuarticClosure

theorem archivedGaussianActualNormBound_of_fifth_power_prime_windows {B : ℝ}
    (hB : 0 ≤ B) (hcenter : ArchivedGaussianPrimeCenterLimit)
    (hglobal : ∀ n : ℕ, |archivedGaussianSignedPrimePrefix n| ≤ B * (n : ℝ) ^ (7 / 8 : ℝ))
    (hwindows : ∀ θ : ℝ, 1 / 2 < θ → θ ≤ 3 / 4 → ArchivedGaussianFifthPowerPrimeWindows θ) :
    GaussianCutoffWindowBound archivedGaussianRetainedNormWindow :=
  archivedGaussianRetainedNormWindow_bound_iff_triangle.mpr
    (archivedGaussianSqrtTriangleWindowBound_iff.mpr
      (archivedGaussianPrimeSquaredWindowBound_of_fifth_power_prime_windows
        hB hcenter hglobal hwindows))

/-- The actual quartic consequence with only a signed cofinal prime-prefix estimate
at the lower exponents, the ordered center, and the global \(7/8\) envelope as arithmetic inputs. -/
theorem quartic_rh_of_fifth_power_prime_windows
    (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    {B : ℝ} (hB : 0 ≤ B) (hcenter : ArchivedGaussianPrimeCenterLimit)
    (hglobal : ∀ n : ℕ, |archivedGaussianSignedPrimePrefix n| ≤ B * (n : ℝ) ^ (7 / 8 : ℝ))
    (hwindows : ∀ θ : ℝ, 1 / 2 < θ → θ ≤ 3 / 4 → ArchivedGaussianFifthPowerPrimeWindows θ) :
    DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_actual_norm_windows hD hpos
    (archivedGaussianActualNormBound_of_fifth_power_prime_windows hB hcenter hglobal hwindows)

#check quartic_rh_of_fifth_power_prime_windows
#print axioms archivedGaussianPrimeSquaredWindow_le_in_fifth_power_window
#print axioms archivedGaussianActualNormBound_of_fifth_power_prime_windows
#print axioms quartic_rh_of_fifth_power_prime_windows

end GaussianQuarticClosure

end

end AlpogeSuperZeta
