import GaussianPrimeOnlyWindow
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! Certify a whole interval of the archived signed prime ramp using two
samples and the negative slope jumps between them. -/

namespace AlpogeSuperZeta

open ArithmeticFunction ArtinPrimitiveRootsConjecture Finset Set
open scoped Classical

noncomputable section

/-- The line through the readings of f at the two endpoints. -/
def gaussianPrimeCellChord (f : ℝ → ℝ) (l r x : ℝ) : ℝ :=
  (r - x) / (r - l) * f l + (x - l) / (r - l) * f r

/-- The gap above one hinge between the two samples. -/
def gaussianPrimeCellTent (l r x p : ℝ) : ℝ :=
  if p ∈ Ioo l r then (min x p - l) * (r - max x p) / (r - l) else 0

theorem gaussianPrimeCellChord_hinge {l r x : ℝ} (hlr : l < r) (hx : x ∈ Icc l r)
    (p : ℝ) :
    gaussianPrimeCellChord (fun y => max (y - p) 0) l r x - max (x - p) 0 =
      gaussianPrimeCellTent l r x p := by
  dsimp only [gaussianPrimeCellChord, gaussianPrimeCellTent]
  have hden := sub_ne_zero.mpr hlr.ne'
  by_cases hpl : p ≤ l
  · rw [if_neg (fun hp => (mem_Ioo.mp hp).1.not_ge hpl)]
    rw [max_eq_left (sub_nonneg.mpr hpl),
      max_eq_left (sub_nonneg.mpr (hpl.trans hlr.le)),
      max_eq_left (sub_nonneg.mpr (hpl.trans hx.1))]
    field_simp [hden]
    ring
  by_cases hrp : r ≤ p
  · rw [if_neg (fun hp => (mem_Ioo.mp hp).2.not_ge hrp)]
    rw [max_eq_right (sub_nonpos.mpr (hlr.le.trans hrp)),
      max_eq_right (sub_nonpos.mpr hrp),
      max_eq_right (sub_nonpos.mpr (hx.2.trans hrp))]
    ring
  have hp : p ∈ Ioo l r := ⟨lt_of_not_ge hpl, lt_of_not_ge hrp⟩
  rw [if_pos hp, max_eq_right (sub_nonpos.mpr hp.1.le),
    max_eq_left (sub_nonneg.mpr hp.2.le)]
  by_cases hxp : x ≤ p
  · rw [max_eq_right (sub_nonpos.mpr hxp), min_eq_left hxp, max_eq_right hxp]
    field_simp [hden]
    ring
  · have hpx := (lt_of_not_ge hxp).le
    rw [max_eq_left (sub_nonneg.mpr hpx), min_eq_right hpx, max_eq_left hpx]
    field_simp [hden]
    ring

/-- The chord gap of any hinge is nonnegative and has a uniform height bound. -/
theorem gaussianPrimeCellTent_bounds {l r x : ℝ} (hlr : l < r) (hx : x ∈ Icc l r)
    (p : ℝ) :
    0 ≤ gaussianPrimeCellTent l r x p ∧
      gaussianPrimeCellTent l r x p ≤ (x - l) * (r - x) / (r - l) ∧
      (x - l) * (r - x) / (r - l) ≤ (r - l) / 4 := by
  have hden := sub_pos.mpr hlr
  have hxl := sub_nonneg.mpr hx.1
  have hrx := sub_nonneg.mpr hx.2
  have hmax : (x - l) * (r - x) / (r - l) ≤ (r - l) / 4 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg ((x - l) - (r - x))]
  refine ⟨?_, ?_, hmax⟩
  · unfold gaussianPrimeCellTent
    split_ifs with hp
    · exact div_nonneg (mul_nonneg (sub_nonneg.mpr (le_min hx.1 hp.1.le))
        (sub_nonneg.mpr (max_le hx.2 hp.2.le))) hden.le
    · exact le_rfl
  · unfold gaussianPrimeCellTent
    split_ifs with hp
    · apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul (sub_le_sub_right (min_le_left _ _) _)
        (sub_le_sub_left (le_max_left _ _) _)
        (sub_nonneg.mpr (max_le hx.2 hp.2.le)) hxl
    · positivity

/-- The slope jump of the archived prime-only ramp at a rational prime. -/
def archivedGaussianPrimeSlope (p : ℕ) : ℝ :=
  vonMangoldt p * (if p.Prime then archivedGaussianPrimeWeight p else 0) / p

theorem archivedGaussianPrimeSlope_at_prime {p : ℕ} (hp : p.Prime) :
    archivedGaussianPrimeSlope p = archivedGaussianPrimeWeight p * Real.log p / p := by
  rw [archivedGaussianPrimeSlope, if_pos hp, vonMangoldt_apply_prime hp, mul_comm]

private theorem archivedGaussianPrimeOnlyRamp_eq_hinges {r x : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ r) :
    archivedGaussianPrimeOnlyRamp x =
      (∑ p ∈ range (⌊r⌋₊ + 1), archivedGaussianPrimeSlope p * max (x - p) 0) +
        ((logDeriv QuarticModel.archivedGaussianFactor 1).re +
          gaussianHigherPrimeLinearCoefficient) * x := by
  simp only [archivedGaussianPrimeOnlyRamp, gaussianPrimeNormRamp, Deduction.ramp,
    Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  let a (p : ℕ) := vonMangoldt p * (if p.Prime then archivedGaussianPrimeWeight p else 0)
  change (∑ p ∈ range (⌊x⌋₊ + 1), a p * max (x / p - 1) 0) +
    (logDeriv QuarticModel.archivedGaussianFactor 1).re * x +
    gaussianHigherPrimeLinearCoefficient * x = _
  have hS : range (⌊x⌋₊ + 1) ⊆ range (⌊r⌋₊ + 1) :=
    range_subset_range.mpr (Nat.succ_le_succ (Nat.floor_mono hxr))
  have htail (p : ℕ) (_ : p ∈ range (⌊r⌋₊ + 1)) (hp : p ∉ range (⌊x⌋₊ + 1)) :
      a p * max (x / p - 1) 0 = 0 := by
    have hp' : x < (p : ℝ) := Nat.lt_of_floor_lt (by
      simpa only [Finset.mem_range, Nat.lt_succ_iff, not_le] using hp)
    have hpos := hx.trans_lt hp'
    rw [max_eq_right (sub_nonpos.mpr ((div_le_one₀ hpos).mpr hp'.le)), mul_zero]
  rw [sum_subset hS htail]
  have hterm (p : ℕ) : a p * max (x / p - 1) 0 =
      archivedGaussianPrimeSlope p * max (x - p) 0 := by
    by_cases hp : p = 0
    · simp [hp, a, archivedGaussianPrimeSlope]
    have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
    have heq : x / p - 1 = (x - p) * (p : ℝ)⁻¹ := by field_simp
    have hm := max_mul_of_nonneg (x - p) 0 (inv_nonneg.mpr hpos.le)
    rw [zero_mul] at hm
    rw [heq, ← hm]
    simp only [archivedGaussianPrimeSlope, a, div_eq_mul_inv]
    ring
  simp_rw [hterm]
  ring

/-- All affine terms cancel. Only primes strictly between the readings
contribute to the chord gap. -/
theorem archivedGaussianPrimeCellChord_gap {l r x : ℝ}
    (hl : 0 ≤ l) (hlr : l < r) (hx : x ∈ Icc l r) :
    gaussianPrimeCellChord archivedGaussianPrimeOnlyRamp l r x -
        archivedGaussianPrimeOnlyRamp x =
      ∑ p ∈ range (⌊r⌋₊ + 1),
        archivedGaussianPrimeSlope p * gaussianPrimeCellTent l r x p := by
  rw [← sum_congr rfl (fun p (_ : p ∈ range (⌊r⌋₊ + 1)) =>
    congrArg (fun y => archivedGaussianPrimeSlope p * y) (gaussianPrimeCellChord_hinge hlr hx p))]
  unfold gaussianPrimeCellChord
  rw [archivedGaussianPrimeOnlyRamp_eq_hinges hl hlr.le,
    archivedGaussianPrimeOnlyRamp_eq_hinges (hl.trans hlr.le) le_rfl,
    archivedGaussianPrimeOnlyRamp_eq_hinges (hl.trans hx.1) hx.2]
  let a := (r - x) / (r - l)
  let b := (x - l) / (r - l)
  let m := (logDeriv QuarticModel.archivedGaussianFactor 1).re +
    gaussianHigherPrimeLinearCoefficient
  have hlin : a * (m * l) + b * (m * r) = m * x := by
    dsimp [a, b]
    field_simp [(sub_pos.mpr hlr).ne']
    ring
  let H (p : ℕ) (t : ℝ) := archivedGaussianPrimeSlope p * max (t - p) 0
  let S := range (⌊r⌋₊ + 1)
  have hterms (p : ℕ) : archivedGaussianPrimeSlope p *
      (a * max (l - p) 0 + b * max (r - p) 0 - max (x - p) 0) =
      a * H p l + b * H p r - H p x := by dsimp [H]; ring
  change a * ((∑ p ∈ S, H p l) + m * l) +
      b * ((∑ p ∈ S, H p r) + m * r) - ((∑ p ∈ S, H p x) + m * x) =
    ∑ p ∈ S, archivedGaussianPrimeSlope p *
      (a * max (l - p) 0 + b * max (r - p) 0 - max (x - p) 0)
  simp_rw [hterms]
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
  linarith

/-- The total downward change in slope from primes strictly inside a cell. -/
def archivedGaussianPrimeCellNegativeMass (l r : ℝ) : ℝ :=
  ∑ p ∈ range (⌊r⌋₊ + 1),
    if (p : ℝ) ∈ Ioo l r then max (-archivedGaussianPrimeSlope p) 0 else 0

theorem archivedGaussianPrimeCellNegativeMass_nonneg (l r : ℝ) :
    0 ≤ archivedGaussianPrimeCellNegativeMass l r := by
  unfold archivedGaussianPrimeCellNegativeMass
  apply sum_nonneg
  intro p _
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

/-- The bound depends only on downward jumps and the interpolation weights. -/
theorem archivedGaussianPrimeCellChord_upper {l r x : ℝ}
    (hl : 0 ≤ l) (hlr : l < r) (hx : x ∈ Icc l r) :
    archivedGaussianPrimeOnlyRamp x ≤
      gaussianPrimeCellChord archivedGaussianPrimeOnlyRamp l r x +
        (x - l) * (r - x) / (r - l) * archivedGaussianPrimeCellNegativeMass l r := by
  rw [← sub_le_iff_le_add', ← neg_sub,
    archivedGaussianPrimeCellChord_gap hl hlr hx, ← sum_neg_distrib]
  unfold archivedGaussianPrimeCellNegativeMass
  rw [mul_sum]
  apply sum_le_sum
  intro p _
  by_cases hp : (p : ℝ) ∈ Ioo l r
  · rw [if_pos hp, ← neg_mul, mul_comm ((x - l) * (r - x) / (r - l))]
    obtain ⟨ht₀, ht₁, _⟩ := gaussianPrimeCellTent_bounds hlr hx p
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) ht₀).trans
      (mul_le_mul_of_nonneg_left ht₁ (le_max_right _ _))
  · simp [hp, gaussianPrimeCellTent]

/-- An elementary cell budget from just the endpoints. The number of
interior integer knots bounds the number of primes contributing. -/
theorem archivedGaussianPrimeIntegerCellMass_le {l r : ℕ} (hl : 1 ≤ l) (hlr : l < r) :
    archivedGaussianPrimeCellNegativeMass l r ≤
      ((r : ℝ) - l) * (2 * Real.log r / l) := by
  have hl₀ : (0 : ℝ) < l := Nat.cast_pos.mpr hl
  have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast hl.trans hlr.le
  have hlog₀ := Real.log_nonneg hr₁
  have hB₀ : 0 ≤ 2 * Real.log (r : ℝ) / (l : ℝ) := by positivity
  let S := Finset.Ioo l r
  have hS : S ⊆ range (⌊(r : ℝ)⌋₊ + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (by simpa using (Finset.mem_Ioo.mp hp).2.le)
  let a (p : ℕ) := if (p : ℝ) ∈ Set.Ioo (l : ℝ) (r : ℝ)
    then max (-archivedGaussianPrimeSlope p) 0 else 0
  have hzero (p : ℕ) (_ : p ∈ range (⌊(r : ℝ)⌋₊ + 1)) (hp : p ∉ S) :
      a p = 0 := by
    dsimp only [a]
    rw [if_neg]
    intro hp'
    exact hp (Finset.mem_Ioo.mpr ⟨by exact_mod_cast hp'.1, by exact_mod_cast hp'.2⟩)
  have hterm (p : ℕ) (hp : p ∈ S) : a p ≤ 2 * Real.log r / l := by
    have hpL : (l : ℝ) < p := by exact_mod_cast (Finset.mem_Ioo.mp hp).1
    have hpR : (p : ℝ) < r := by exact_mod_cast (Finset.mem_Ioo.mp hp).2
    have hp₀ := hl₀.trans hpL
    rw [show a p = max (-archivedGaussianPrimeSlope p) 0 from if_pos ⟨hpL, hpR⟩]
    apply max_le _ hB₀
    by_cases hprime : p.Prime
    · rw [archivedGaussianPrimeSlope_at_prime hprime]
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
        exact_mod_cast hprime.one_lt.le)
      have hlog := Real.strictMonoOn_log (show (p : ℝ) ∈ Set.Ioi (0 : ℝ) from hp₀)
        (show (r : ℝ) ∈ Set.Ioi (0 : ℝ) from hp₀.trans hpR) hpR
      have habs := (abs_le.mp (archivedGaussianPrimeWeight_abs_le_two p)).1
      rw [← neg_div, ← neg_mul]
      calc
        _ ≤ 2 * Real.log p / p :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hlogp) hp₀.le
        _ ≤ 2 * Real.log r / p :=
          div_le_div_of_nonneg_right (by linarith) hp₀.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hl₀ hpL.le
    · simpa only [archivedGaussianPrimeSlope, if_neg hprime, mul_zero, zero_div, neg_zero] using hB₀
  have hcard : (S.card : ℝ) ≤ (r : ℝ) - l := by
    rw [← Nat.cast_sub hlr.le]
    exact_mod_cast (show S.card ≤ r - l by simp [S])
  change (∑ p ∈ range (⌊(r : ℝ)⌋₊ + 1), a p) ≤ _
  rw [← sum_subset hS hzero]
  calc
    _ ≤ ∑ p ∈ S, 2 * Real.log r / l := sum_le_sum hterm
    _ = (S.card : ℝ) * (2 * Real.log r / l) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB₀

theorem archivedGaussianPrimeIntegerCellError {l r : ℕ} (hl : 1 ≤ l) (hlr : l < r) :
    ((r : ℝ) - l) / 4 * archivedGaussianPrimeCellNegativeMass l r ≤
      ((r : ℝ) - l) ^ 2 * Real.log r / (2 * l) := by
  have hgap : 0 ≤ (r : ℝ) - l := sub_nonneg.mpr (by exact_mod_cast hlr.le)
  calc
    _ ≤ ((r : ℝ) - l) / 4 * (((r : ℝ) - l) * (2 * Real.log r / l)) :=
      mul_le_mul_of_nonneg_left (archivedGaussianPrimeIntegerCellMass_le hl hlr)
        (div_nonneg hgap (by norm_num))
    _ = _ := by ring

/-- An exact error budget for the 100 cells from one to two million. -/
theorem archivedGaussianPrimeMillionCellBudget (j : ℕ) (hj : j < 100) :
    let l := 1000000 + 10000 * j
    let r := l + 10000
    ((r : ℝ) - l) / 4 * archivedGaussianPrimeCellNegativeMass l r ≤ 1050 := by
  dsimp only
  let l := 1000000 + 10000 * j
  let r := l + 10000
  change ((r : ℝ) - l) / 4 * archivedGaussianPrimeCellNegativeMass l r ≤ 1050
  have hl : 1 ≤ l := by dsimp [l]; omega
  have hlr : l < r := by dsimp [r]; omega
  have hr : (0 : ℝ) < r := Nat.cast_pos.mpr (zero_lt_one.trans (hl.trans_lt hlr))
  have hpow : (r : ℝ) ≤ (2 : ℝ) ^ 21 := by
    have h : r ≤ 2097152 := by dsimp [r, l]; omega
    norm_num
    exact_mod_cast h
  have hlog : Real.log (r : ℝ) ≤ 21 := calc
    _ ≤ Real.log ((2 : ℝ) ^ 21) := (Real.log_le_log_iff hr (by positivity)).2 hpow
    _ = 21 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hwidth : (r : ℝ) - l = 10000 := by simp [r, Nat.cast_add]
  have hL : (1000000 : ℝ) ≤ l := by
    exact_mod_cast (show 1000000 ≤ l by dsimp [l]; omega)
  refine (archivedGaussianPrimeIntegerCellError hl hlr).trans ?_
  rw [hwidth]
  apply (div_le_iff₀ (show (0 : ℝ) < 2 * l by linarith)).mpr
  nlinarith

/-- Two samples and a cell-specific error budget certify every point
between them, at the same exponent as the samples. -/
theorem archivedGaussianPrimeCellBound {l r θ C D : ℝ}
    (hl : 1 ≤ l) (hlr : l < r) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hC : 0 ≤ C)
    (hL : archivedGaussianPrimeOnlyRamp l ≤ C * l ^ θ)
    (hR : archivedGaussianPrimeOnlyRamp r ≤ C * r ^ θ)
    (hMass : (r - l) / 4 * archivedGaussianPrimeCellNegativeMass l r ≤ D * l ^ θ)
    (hD : 0 ≤ D) :
    ∀ x ∈ Icc l r, archivedGaussianPrimeOnlyRamp x ≤ (C + D) * x ^ θ := by
  intro x hx
  let a := (r - x) / (r - l)
  let b := (x - l) / (r - l)
  have hl₀ := zero_le_one.trans hl
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hlr.le)
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hlr.le)
  have hden := (sub_pos.mpr hlr).ne'
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [hden]
    ring
  have hx' : a * l + b * r = x := by
    dsimp [a, b]
    field_simp [hden]
    ring
  have hConc : a * l ^ θ + b * r ^ θ ≤ x ^ θ := by
    have h := (Real.concaveOn_rpow hθ₀ hθ₁).2
      (show l ∈ Ici (0 : ℝ) from hl₀) (show r ∈ Ici (0 : ℝ) from hl₀.trans hlr.le)
      ha hb hab
    simpa only [smul_eq_mul, hx'] using h
  have hchord : gaussianPrimeCellChord archivedGaussianPrimeOnlyRamp l r x ≤ C * x ^ θ := by
    change a * archivedGaussianPrimeOnlyRamp l + b * archivedGaussianPrimeOnlyRamp r ≤ _
    calc
      _ ≤ a * (C * l ^ θ) + b * (C * r ^ θ) :=
        add_le_add (mul_le_mul_of_nonneg_left hL ha) (mul_le_mul_of_nonneg_left hR hb)
      _ = C * (a * l ^ θ + b * r ^ θ) := by ring
      _ ≤ C * x ^ θ := mul_le_mul_of_nonneg_left hConc hC
  have htent := (gaussianPrimeCellTent_bounds hlr hx l).2.2
  rw [add_mul]
  exact (archivedGaussianPrimeCellChord_upper hl₀ hlr hx).trans (add_le_add hchord
    ((mul_le_mul_of_nonneg_right htent (archivedGaussianPrimeCellNegativeMass_nonneg l r)).trans
      (hMass.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hl₀ hx.1 hθ₀) hD))))

/-- Cofinal windows covered by certified cells. Individual cells may have
different lengths and different sets of prime jumps. -/
def ArchivedGaussianPrimeMeshBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C ≥ 0, ∃ D ≥ 0, ∀ Y₀ : ℝ,
      ∃ Y ≥ max Y₀ 1, ∃ S : Finset ℝ,
        (∀ y ∈ S, archivedGaussianPrimeOnlyRamp y ≤ C * y ^ θ) ∧
        ∀ x ∈ Icc Y (Y ^ (1 + δ)),
          ∃ l ∈ S, ∃ r ∈ S, Y ≤ l ∧ l < r ∧ x ∈ Icc l r ∧
            (r - l) / 4 * archivedGaussianPrimeCellNegativeMass l r ≤ D * l ^ θ

theorem archivedGaussianPrimeOnlyWindowBound_of_mesh (hmesh : ArchivedGaussianPrimeMeshBound) :
    ArchivedGaussianPrimeOnlyWindowBound := by
  intro θ hθ₀ hθ₁
  obtain ⟨δ, hδ, C, hC, D, hD, hW⟩ := hmesh θ hθ₀ hθ₁
  refine ⟨δ, hδ, C + D, add_nonneg hC hD, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, S, hsamples, hcover⟩ := hW Y₀
  refine ⟨Y, (le_max_left _ _).trans hY, fun x hx => ?_⟩
  obtain ⟨l, hl, r, hr, hYl, hlr, hcell, hMass⟩ := hcover x hx
  exact archivedGaussianPrimeCellBound ((le_max_right _ _).trans (hY.trans hYl)) hlr
    (by linarith) hθ₁.le hC (hsamples l hl) (hsamples r hr) hMass hD x hcell

theorem quartic_rh_of_archived_gaussian_prime_mesh (hD : DirichletLZerosOnLine)
    (hmesh : ArchivedGaussianPrimeMeshBound) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_prime_only_windows hD
    (archivedGaussianPrimeOnlyWindowBound_of_mesh hmesh)

#print axioms gaussianPrimeCellChord_hinge
#print axioms gaussianPrimeCellTent_bounds
#print axioms archivedGaussianPrimeSlope_at_prime
#print axioms archivedGaussianPrimeCellChord_gap
#print axioms archivedGaussianPrimeCellChord_upper
#print axioms archivedGaussianPrimeIntegerCellError
#print axioms archivedGaussianPrimeMillionCellBudget
#print axioms archivedGaussianPrimeCellBound
#check quartic_rh_of_archived_gaussian_prime_mesh
#print axioms quartic_rh_of_archived_gaussian_prime_mesh

end
end AlpogeSuperZeta
