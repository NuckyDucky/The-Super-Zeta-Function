import GaussianVaughanRationalSquares

/-! The fully split primes of the biquadratic base use the sum of the
four rational characters at the conductor level. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex DirichletCharacter QuarticModel
open scoped Classical

noncomputable section

private abbrev χ₀ : DirichletCharacter ℂ archivedGaussianRationalLevel := 1
private abbrev χ₁ := archivedGaussianRationalChi4
private abbrev χ₂ := archivedGaussianNormCharacter
private abbrev χ₃ := χ₁ * χ₂

private theorem char_ne_one_of_value_neg_one {χ : DirichletCharacter ℂ archivedGaussianRationalLevel}
    {n : ℕ} (hn : n.Coprime archivedGaussianRationalLevel)
    (h : χ (n : ZMod archivedGaussianRationalLevel) = -1) : χ ≠ 1 := by
  intro he
  rw [he, MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).2 hn)] at h
  norm_num at h

private theorem norm_sign_73 : rationalNormSign 73 = -1 := by
  let : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  have h := archivedGaussianPrimeWeight_sq (p := 73) (by decide) (by decide +kernel)
  rw [archivedGaussianPrimeWeights_at_73.1,
    ZMod.χ₄_nat_one_mod_four (by decide : (73 : ℕ) % 4 = 1)] at h
  norm_num at h
  exact_mod_cast (show (rationalNormSign 73 : ℝ) = -1 by linarith)

theorem archivedGaussianSplitCharacters_ne_one :
    χ₁ ≠ 1 ∧ χ₂ ≠ 1 ∧ χ₃ ≠ 1 := by
  have h3 : (3 : ℕ).Coprime archivedGaussianRationalLevel := by decide +kernel
  have h73 : (73 : ℕ).Coprime archivedGaussianRationalLevel := by decide +kernel
  have hχ₁ : χ₁ (73 : ZMod archivedGaussianRationalLevel) = 1 := by
    change χ₁ ((73 : ℕ) : ZMod archivedGaussianRationalLevel) = 1
    rw [archivedGaussianRationalChi4_apply_of_coprime h73,
      ZMod.χ₄_nat_one_mod_four (by decide : (73 : ℕ) % 4 = 1)]
    norm_num
  have hχ₂ : χ₂ (73 : ZMod archivedGaussianRationalLevel) = -1 := by
    change χ₂ ((73 : ℕ) : ZMod archivedGaussianRationalLevel) = -1
    rw [archivedGaussianNormCharacter_apply_of_coprime h73, norm_sign_73]
    norm_num
  refine ⟨char_ne_one_of_value_neg_one h3 ?_,
    char_ne_one_of_value_neg_one h73 (by exact hχ₂),
    char_ne_one_of_value_neg_one h73 (by simp [MulChar.mul_apply, hχ₁, hχ₂])⟩
  rw [archivedGaussianRationalChi4_apply_of_coprime h3,
    ZMod.χ₄_nat_three_mod_four (by decide : (3 : ℕ) % 4 = 3)]
  norm_num

def archivedGaussianSplitMangoldt : ArithmeticFunction ℂ :=
  ⟨fun n =>
    let u := (n : ZMod archivedGaussianRationalLevel)
    (χ₀ u + χ₁ u + χ₂ u + χ₃ u) * (vonMangoldt n : ℂ), by simp⟩

theorem archivedGaussianSplitMangoldt_at_prime {p : ℕ} (hp : p.Prime)
    (hp₂ : p ≠ 2) (hpD : p.Coprime 26509772707289)
    (hc : p.Coprime archivedGaussianRationalLevel) :
    archivedGaussianSplitMangoldt p =
      (if p % 4 = 1 ∧ rationalNormSign p = 1 then 4 else 0) *
        (Real.log (p : ℝ) : ℂ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : rationalNormSign p = 1 ∨ rationalNormSign p = -1 := by
    rw [← rationalNormSign_reciprocity p hp₂]
    exact legendreSym.eq_one_or_neg_one p (a := (26509772707289 : ℤ)) (by
      simpa only [Int.cast_ofNat] using norm_discriminant_ne_zero hpD)
  have ho := hp.mod_two_eq_one_iff_ne_two.mpr hp₂
  have he : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hunit := (ZMod.isUnit_iff_coprime p archivedGaussianRationalLevel).2 hc
  simp only [archivedGaussianSplitMangoldt, ArithmeticFunction.coe_mk, vonMangoldt_apply_prime hp,
    MulChar.one_apply hunit, MulChar.mul_apply, archivedGaussianRationalChi4_apply_of_coprime hc,
    archivedGaussianNormCharacter_apply_of_coprime hc]
  rcases he with he | he <;> rcases hd with hd | hd
  · norm_num [he, hd, ZMod.χ₄_nat_one_mod_four he]
  · norm_num [he, hd, ZMod.χ₄_nat_one_mod_four he]
  · norm_num [he, hd, ZMod.χ₄_nat_three_mod_four he]
  · norm_num [he, hd, ZMod.χ₄_nat_three_mod_four he]

theorem archivedGaussianSplitMangoldt_norm_le (n : ℕ) :
    ‖archivedGaussianSplitMangoldt n‖ ≤ 4 * vonMangoldt n := by
  let u : ZMod archivedGaussianRationalLevel := n
  have h : ‖χ₀ u + χ₁ u + χ₂ u + χ₃ u‖ ≤ (4 : ℝ) := by
    calc
      _ ≤ ‖χ₀ u + χ₁ u + χ₂ u‖ + ‖χ₃ u‖ := norm_add_le _ _
      _ ≤ ‖χ₀ u‖ + ‖χ₁ u‖ + ‖χ₂ u‖ + ‖χ₃ u‖ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ _ := by linarith [χ₀.norm_le_one u, χ₁.norm_le_one u, χ₂.norm_le_one u, χ₃.norm_le_one u]
  change ‖(χ₀ u + χ₁ u + χ₂ u + χ₃ u) * (vonMangoldt n : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  exact mul_le_mul_of_nonneg_right h vonMangoldt_nonneg

private def twist (χ : DirichletCharacter ℂ archivedGaussianRationalLevel) : ℕ → ℂ :=
  fun n => χ (n : ZMod archivedGaussianRationalLevel) * (vonMangoldt n : ℂ)

private theorem twist_summable (χ : DirichletCharacter ℂ archivedGaussianRationalLevel)
    {z : ℂ} (hz : 1 < z.re) : LSeriesSummable (twist χ) z :=
  LSeriesSummable_twist_vonMangoldt χ hz

private theorem twist_series (χ : DirichletCharacter ℂ archivedGaussianRationalLevel)
    {z : ℂ} (hz : 1 < z.re) : LSeries (twist χ) z = -logDeriv (LFunction χ) z := by
  rw [logDeriv_apply, ← neg_div, deriv_LFunction_eq_deriv_LSeries χ hz, LFunction_eq_LSeries χ hz]
  exact LSeries_twist_vonMangoldt_eq χ hz

private theorem splitMangoldt_eq :
    (archivedGaussianSplitMangoldt : ℕ → ℂ) = twist χ₀ + twist χ₁ + twist χ₂ + twist χ₃ := by
  funext n
  simp only [archivedGaussianSplitMangoldt, ArithmeticFunction.coe_mk, twist, Pi.add_apply]
  ring

theorem archivedGaussianSplitMangoldt_summable {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable archivedGaussianSplitMangoldt z := by
  rw [splitMangoldt_eq]
  exact (((twist_summable χ₀ hz).add (twist_summable χ₁ hz)).add
    (twist_summable χ₂ hz)).add (twist_summable χ₃ hz)

theorem archivedGaussianSplitMangoldt_LSeries {z : ℂ} (hz : 1 < z.re) :
    LSeries archivedGaussianSplitMangoldt z =
      -logDeriv (LFunction χ₀) z + -logDeriv (LFunction χ₁) z +
        -logDeriv (LFunction χ₂) z + -logDeriv (LFunction χ₃) z := by
  rw [splitMangoldt_eq,
    LSeries_add (((twist_summable χ₀ hz).add (twist_summable χ₁ hz)).add
      (twist_summable χ₂ hz)) (twist_summable χ₃ hz),
    LSeries_add ((twist_summable χ₀ hz).add (twist_summable χ₁ hz)) (twist_summable χ₂ hz),
    LSeries_add (twist_summable χ₀ hz) (twist_summable χ₁ hz)]
  simp only [twist_series _ hz]

#print axioms archivedGaussianSplitCharacters_ne_one
#print axioms archivedGaussianSplitMangoldt_at_prime
#print axioms archivedGaussianSplitMangoldt_norm_le
#print axioms archivedGaussianSplitMangoldt_summable
#print axioms archivedGaussianSplitMangoldt_LSeries

end
end AlpogeSuperZeta
