import GaussianVaughanPrimePowers
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-! Read the exact prime-square coefficients on the rational Dirichlet
side at doubled Mellin coordinate, keeping the conductor exceptions. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Set QuarticModel
open scoped Classical

noncomputable section

abbrev archivedGaussianRationalLevel : ℕ := 4 * 26509772707289

local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
set_option maxRecDepth 60000 in
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

private def liftedQuadraticCharacter (p : ℕ) [Fact p.Prime]
    (hp : p ∣ archivedGaussianRationalLevel) :
    DirichletCharacter ℂ archivedGaussianRationalLevel :=
  DirichletCharacter.changeLevel hp ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))

def archivedGaussianNormCharacter : DirichletCharacter ℂ archivedGaussianRationalLevel :=
  liftedQuadraticCharacter 41 (by decide +kernel) *
    liftedQuadraticCharacter 457 (by decide +kernel) *
    liftedQuadraticCharacter 1414835497 (by decide +kernel)

def archivedGaussianRationalChi4 : DirichletCharacter ℂ archivedGaussianRationalLevel :=
  DirichletCharacter.changeLevel (by decide +kernel : 4 ∣ archivedGaussianRationalLevel)
    (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))

private theorem changeLevel_apply_nat_of_coprime {M N n : ℕ}
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (hn : n.Coprime N) :
    DirichletCharacter.changeLevel hMN χ (n : ZMod N) = χ (n : ZMod M) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime n N).2 hn
  simpa only [hu, ZMod.cast_natCast hMN] using
    DirichletCharacter.changeLevel_eq_cast_of_dvd χ hMN u

private theorem liftedQuadraticCharacter_apply {p : ℕ} [Fact p.Prime]
    (hp : p ∣ archivedGaussianRationalLevel) {n : ℕ}
    (hn : n.Coprime archivedGaussianRationalLevel) :
    liftedQuadraticCharacter p hp (n : ZMod archivedGaussianRationalLevel) =
      (legendreSym p n : ℂ) := by
  rw [liftedQuadraticCharacter, changeLevel_apply_nat_of_coprime _ _ hn]
  simp [legendreSym, MulChar.ringHomComp_apply]

theorem archivedGaussianNormCharacter_apply_of_coprime {n : ℕ}
    (hn : n.Coprime archivedGaussianRationalLevel) :
    archivedGaussianNormCharacter (n : ZMod archivedGaussianRationalLevel) =
      (rationalNormSign n : ℂ) := by
  simp only [archivedGaussianNormCharacter, MulChar.mul_apply, liftedQuadraticCharacter_apply _ hn,
    rationalNormSign, Int.cast_mul]

theorem archivedGaussianRationalChi4_apply_of_coprime {n : ℕ}
    (hn : n.Coprime archivedGaussianRationalLevel) :
    archivedGaussianRationalChi4 (n : ZMod archivedGaussianRationalLevel) =
      (ZMod.χ₄ (n : ZMod 4) : ℂ) := by
  rw [archivedGaussianRationalChi4, changeLevel_apply_nat_of_coprime _ _ hn]
  rfl

private theorem prime_dvd_rationalLevel_iff {p : ℕ} (hp : p.Prime) :
    p ∣ archivedGaussianRationalLevel ↔ p ∣ 2 * 26509772707289 := by
  change p ∣ 4 * 26509772707289 ↔ p ∣ 2 * 26509772707289
  constructor
  · intro h
    rcases hp.dvd_mul.mp h with h4 | hD
    · have h2 := hp.dvd_of_dvd_pow (show p ∣ (2 : ℕ) ^ 2 from h4)
      exact h2.trans (dvd_mul_right _ _)
    · exact hD.trans (dvd_mul_left _ _)
  · intro h
    rcases hp.dvd_mul.mp h with h2 | hD
    · exact h2.trans ((by norm_num : (2 : ℕ) ∣ 4).trans (dvd_mul_right _ _))
    · exact hD.trans (dvd_mul_left _ _)

def archivedGaussianRationalSquareWeight (n : ℕ) : ℂ :=
  let u : ZMod archivedGaussianRationalLevel := n
  (1 : DirichletCharacter ℂ archivedGaussianRationalLevel) u +
    archivedGaussianRationalChi4 u + archivedGaussianNormCharacter u -
      (archivedGaussianRationalChi4 * archivedGaussianNormCharacter) u

/-- All four rational characters live at the same level. The exceptional
prime square contributes its original weight one when they all vanish. -/
theorem archivedGaussianVaughanSquareWeight_eq_rational {p : ℕ} (hp : p.Prime) :
    (archivedGaussianPrimeWeight (p ^ 2) : ℂ) =
      archivedGaussianRationalSquareWeight p + (if p ∣ archivedGaussianRationalLevel then 1 else 0) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have ha := archivedGaussianPrimeWeight_even_all (p := p) 1 (by decide)
  norm_num only [mul_one, pow_one] at ha
  rw [ha]
  by_cases h : p ∣ archivedGaussianRationalLevel
  · rw [if_pos h, if_pos ((prime_dvd_rationalLevel_iff hp).mp h)]
    have hn : ¬IsUnit (p : ZMod archivedGaussianRationalLevel) := by
      rw [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd]
      exact not_not.mpr h
    simp [archivedGaussianRationalSquareWeight, MulChar.map_nonunit _ hn]
  · rw [if_neg h, if_neg (fun hh => h ((prime_dvd_rationalLevel_iff hp).mpr hh))]
    have hc : p.Coprime archivedGaussianRationalLevel := hp.coprime_iff_not_dvd.mpr h
    have hu := (ZMod.isUnit_iff_coprime p archivedGaussianRationalLevel).2 hc
    simp only [archivedGaussianRationalSquareWeight, MulChar.one_apply hu,
      MulChar.mul_apply, archivedGaussianRationalChi4_apply_of_coprime hc,
      archivedGaussianNormCharacter_apply_of_coprime hc, ofReal_sub, ofReal_add, ofReal_mul,
      ofReal_one, ofReal_intCast, add_zero]

def archivedGaussianRationalMangoldt : ArithmeticFunction ℂ :=
  ⟨fun n => archivedGaussianRationalSquareWeight n * (vonMangoldt n : ℂ), by simp⟩

def archivedGaussianExceptionalMangoldt : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Prime ∧ n ∣ archivedGaussianRationalLevel then (vonMangoldt n : ℂ) else 0,
    by simp⟩

theorem archivedGaussianRationalMangoldt_norm_le (n : ℕ) :
    ‖archivedGaussianRationalMangoldt n‖ ≤ 4 * vonMangoldt n := by
  let u : ZMod archivedGaussianRationalLevel := n
  let χ₁ : DirichletCharacter ℂ archivedGaussianRationalLevel := 1
  let χ₂ := archivedGaussianRationalChi4
  let χ₃ := archivedGaussianNormCharacter
  let χ₄ := χ₂ * χ₃
  have h : ‖χ₁ u + χ₂ u + χ₃ u - χ₄ u‖ ≤ (4 : ℝ) := by
    calc
      _ ≤ ‖χ₁ u + χ₂ u + χ₃ u‖ + ‖χ₄ u‖ := norm_sub_le _ _
      _ ≤ ‖χ₁ u‖ + ‖χ₂ u‖ + ‖χ₃ u‖ + ‖χ₄ u‖ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ _ := by linarith [χ₁.norm_le_one u, χ₂.norm_le_one u, χ₃.norm_le_one u, χ₄.norm_le_one u]
  change ‖(χ₁ u + χ₂ u + χ₃ u - χ₄ u) * (vonMangoldt n : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  exact mul_le_mul_of_nonneg_right h vonMangoldt_nonneg

def squareDilation (a : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.sqrt ^ 2 = n then a n.sqrt else 0, by simp⟩

private theorem squareDilation_at_square (a : ArithmeticFunction ℂ) (n : ℕ) :
    squareDilation a (n ^ 2) = a n := by simp [squareDilation]

/-- Squaring all coefficient addresses doubles the L-series coordinate. -/
theorem squareDilation_LSeries (a : ArithmeticFunction ℂ) (z : ℂ) :
    LSeries (squareDilation a) z = LSeries a (2 * z) := by
  let sq (n : ℕ) := n ^ 2
  have hs : Function.Injective sq := fun _ _ h => by simpa [sq] using congrArg Nat.sqrt h
  let e := Equiv.ofInjective sq hs
  let f := LSeries.term (squareDilation a) z
  have hterm (n : ℕ) : f (sq n) = LSeries.term a (2 * z) n := by
    by_cases hn : n = 0
    · subst n
      simp [f, sq]
    change LSeries.term (squareDilation a) z (n ^ 2) = _
    rw [LSeries.term_of_ne_zero (pow_ne_zero _ hn), LSeries.term_of_ne_zero hn,
      squareDilation_at_square, Nat.cast_pow]
    have he : ((n : ℂ) ^ 2) ^ z = (n : ℂ) ^ ((2 : ℂ) * z) := by
      have h := Complex.cpow_mul_ofReal_nonneg (x := (n : ℝ)) (by positivity) ((2 : ℕ) : ℝ) z
      have h₂ : (((2 : ℕ) : ℝ) : ℂ) = (2 : ℂ) := by norm_num
      have hnPow : ((((n : ℝ) ^ ((2 : ℕ) : ℝ)) : ℝ) : ℂ) = (n : ℂ) ^ (2 : ℕ) := by
        rw [Real.rpow_natCast (n : ℝ) 2, Complex.ofReal_pow, Complex.ofReal_natCast]
      rw [h₂, hnPow, Complex.ofReal_natCast] at h
      exact h.symm
    rw [he]
  have hf : (range sq).indicator f = f := by
    funext n
    by_cases hn : n ∈ range sq
    · exact indicator_of_mem hn f
    have hN : ¬n.sqrt ^ 2 = n := fun h => hn ⟨n.sqrt, h⟩
    rw [indicator_of_notMem hn]
    change 0 = LSeries.term (squareDilation a) z n
    simp [LSeries.term, squareDilation, hN]
  calc
    _ = ∑' n : range sq, f n.val := by rw [tsum_subtype, hf]; rfl
    _ = ∑' n : ℕ, f (sq n) := (e.tsum_eq (fun n : range sq => f n.val)).symm
    _ = _ := by simp only [hterm, LSeries]

def primePart (a : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Prime then a n else 0, by simp⟩

theorem primePart_add_tail_two (a : ArithmeticFunction ℂ)
    (ha : ∀ n, ¬IsPrimePow n → a n = 0) :
    primePart a + primePowerTail 2 a = a := by
  ext n
  change (if n.Prime then a n else 0) +
    (if IsPrimePow n ∧ 2 ≤ n.factorization n.minFac then a n else 0) = a n
  by_cases h : IsPrimePow n
  · obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp h
    rw [hp.pow_minFac hj.ne', hp.factorization_pow, Finsupp.single_eq_same]
    by_cases hj₁ : j = 1
    · subst j
      simp [hp]
    · simp [Nat.Prime.not_prime_pow' (x := p) hj₁, h, show 2 ≤ j by omega]
  have hn : ¬n.Prime := fun hp => h hp.isPrimePow
  simp [hn, h, ha n h]

theorem archivedGaussianVaughanSquareCoefficients_eq_dilation :
    archivedGaussianVaughanSquareCoefficients =
      squareDilation (primePart archivedGaussianRationalMangoldt + archivedGaussianExceptionalMangoldt) := by
  ext n
  by_cases hn : IsPrimePow n ∧ n.factorization n.minFac = 2
  · obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hn.1
    have hj₂ : j = 2 := by
      have h := hn.2
      rwa [hp.pow_minFac hj.ne', hp.factorization_pow, Finsupp.single_eq_same] at h
    subst j
    rw [squareDilation_at_square, ArithmeticFunction.add_apply]
    simp only [archivedGaussianVaughanSquareCoefficients, ArithmeticFunction.coe_mk,
      if_pos hn, archivedGaussianMangoldt, primePart, if_pos hp,
      archivedGaussianRationalMangoldt, archivedGaussianExceptionalMangoldt,
      vonMangoldt_apply_pow (show (2 : ℕ) ≠ 0 by decide)]
    rw [archivedGaussianVaughanSquareWeight_eq_rational hp, add_mul]
    by_cases h : p ∣ archivedGaussianRationalLevel <;> simp [h, hp]
  have hL : archivedGaussianVaughanSquareCoefficients n = 0 := by
    simp [archivedGaussianVaughanSquareCoefficients, hn]
  rw [hL]
  by_cases hs : n.sqrt ^ 2 = n
  · have hnp : ¬n.sqrt.Prime := by
      intro hp
      apply hn
      rw [← hs]
      refine ⟨(isPrimePow_nat_iff _).mpr ⟨n.sqrt, 2, hp, by decide, rfl⟩, ?_⟩
      rw [hp.pow_minFac (by decide : (2 : ℕ) ≠ 0), hp.factorization_pow, Finsupp.single_eq_same]
    change 0 = if n.sqrt ^ 2 = n then
      (primePart archivedGaussianRationalMangoldt + archivedGaussianExceptionalMangoldt) n.sqrt else 0
    rw [if_pos hs, ArithmeticFunction.add_apply]
    simp [primePart, archivedGaussianExceptionalMangoldt, hnp]
  · simp [squareDilation, hs]

theorem archivedGaussianVaughanSquare_LSeries (z : ℂ) :
    LSeries archivedGaussianVaughanSquareCoefficients z =
      LSeries (primePart archivedGaussianRationalMangoldt + archivedGaussianExceptionalMangoldt) (2 * z) := by
  rw [archivedGaussianVaughanSquareCoefficients_eq_dilation, squareDilation_LSeries]
  congr 1

#print axioms archivedGaussianNormCharacter_apply_of_coprime
#print axioms archivedGaussianRationalChi4_apply_of_coprime
#print axioms archivedGaussianVaughanSquareWeight_eq_rational
#print axioms archivedGaussianRationalMangoldt_norm_le
#print axioms squareDilation_LSeries
#print axioms primePart_add_tail_two
#print axioms archivedGaussianVaughanSquareCoefficients_eq_dilation
#print axioms archivedGaussianVaughanSquare_LSeries

end
end AlpogeSuperZeta
