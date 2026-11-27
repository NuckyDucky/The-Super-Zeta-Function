import DedekindDiscriminant23CharacterSparse
import FoldedExponentialTaylor
import NinePointGrid

/-! Reduce the discriminant-23 sign tests to real coefficient data and
finite complex polynomials. -/

namespace FieldTarget

open Set
open scoped BigOperators

noncomputable section

def discriminant23ReadingNode (j : ℕ) : ℝ :=
  3 * (j : ℝ) / 256

def discriminant23ReadingWeight (j : ℕ) : ℝ :=
  (3 / (32 * 28350) : ℝ) * (ninePointGridWeight 32 j : ℝ)

theorem discriminant23_readingNode_mem {j : ℕ} (hj : j ∈ Finset.range 257) :
    discriminant23ReadingNode j ∈ Icc (0 : ℝ) 3 := by
  have h : (j : ℝ) ≤ 256 := by
    exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  unfold discriminant23ReadingNode
  exact ⟨by positivity, by linarith only [h]⟩

private theorem weight_mass :
    ∑ j ∈ Finset.range 257, |discriminant23ReadingWeight j| ≤ 22 / 5 := by
  have h := congrArg (fun x : ℤ ↦ (x : ℝ)) ninePointGrid32_weight_abs_sum
  push_cast at h
  simp only [discriminant23ReadingWeight, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / (32 * 28350)), ← Finset.mul_sum]
  rw [h]
  norm_num

private theorem composite_eq_sum (f : ℝ → ℂ) :
    ninePointComposite f 0 (3 / 64) 32 =
      ∑ j ∈ Finset.range 257, (discriminant23ReadingWeight j : ℂ) * f (discriminant23ReadingNode j) := by
  rw [ninePointComposite_eq_grid, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show ninePointGridPoint 0 (3 / 64) j = discriminant23ReadingNode j by
    unfold ninePointGridPoint discriminant23ReadingNode
    ring]
  unfold discriminant23ReadingWeight
  push_cast
  ring

def discriminant23ReadingHeat (u : ℝ) : ℝ :=
  Real.exp (-discriminant23ThetaScale * Real.exp u)

private theorem heat_le {u : ℝ} (hu : 0 ≤ u) :
    discriminant23ReadingHeat u ≤ 3 / 11 := by
  have ha : 0 ≤ discriminant23ThetaScale := by linarith [discriminant23_thetaScale_interval.1]
  have he : 1 ≤ Real.exp u := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hu
  refine (Real.exp_le_exp.mpr ?_).trans discriminant23_thetaExp_interval.2
  nlinarith only [mul_le_mul_of_nonneg_left he ha]

private def phase (odd : Bool) (w : ℂ) (u : ℝ) : ℂ :=
  if odd then
    (u : ℂ) * (Complex.exp (w * (u : ℂ)) - Complex.exp ((1 - w) * (u : ℂ)))
  else Complex.exp (w * (u : ℂ)) + Complex.exp ((1 - w) * (u : ℂ))

private def reading (odd : Bool) (w : ℂ) : ℂ :=
  if odd then deriv discriminant23CharacterComplexModel w else discriminant23CharacterComplexModel w

private def denseSample (odd : Bool) (w : ℂ) (u : ℝ) : ℂ :=
  phase odd w u * (discriminant23CharacterPolynomial (discriminant23ReadingHeat u) : ℂ)

private def sparseSample (odd : Bool) (w : ℂ) (u : ℝ) : ℂ :=
  phase odd w u * (discriminant23SparsePolynomial (discriminant23ReadingHeat u) : ℂ)

private theorem panelDensity_ofReal (u : ℝ) :
    discriminant23PanelDensity u =
      (discriminant23CharacterPolynomial (discriminant23ReadingHeat u) : ℂ) := by
  have h := discriminant23_panelValue_eq_integrand 0 u
  have hWeight : Complex.exp (0 * (u : ℂ)) + Complex.exp ((1 - 0) * (u : ℂ)) ≠ 0 := by
    rw [zero_mul, Complex.exp_zero, sub_zero, one_mul, ← Complex.ofReal_exp, ← Complex.ofReal_one,
      ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  apply mul_left_cancel₀ hWeight
  exact h

private theorem reading_quad {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1)
    (ht : |w.im| ≤ 11 / 2) (odd : Bool) :
    ‖reading odd w - ninePointComposite (denseSample odd w) 0 (3 / 64) 32‖ ≤ 3 / 100000 := by
  have h := discriminant23_character_quadrature_bounds hlo hhi ht
  cases odd
  · have heq : denseSample false w = fun u : ℝ ↦ discriminant23PanelValue w u := by
      funext u
      simp [denseSample, phase, discriminant23PanelValue, panelDensity_ofReal]
    rw [heq]
    exact h.1
  · have heq : denseSample true w = fun u : ℝ ↦ discriminant23PanelSlope w u := by
      funext u
      simp [denseSample, phase, discriminant23PanelSlope, panelDensity_ofReal]
    rw [heq]
    exact h.2

private theorem phase_norm_le {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) (odd : Bool) : ‖phase odd w u‖ ≤ 2 * Real.exp (2 * u) := by
  have hE₁ : ‖Complex.exp (w * (u : ℂ))‖ ≤ Real.exp u := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr (by linarith only [mul_le_mul_of_nonneg_right hhi hu])
  have hE₂ : ‖Complex.exp ((1 - w) * (u : ℂ))‖ ≤ Real.exp u := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.sub_re, Complex.one_re]
    exact Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hlo hu])
  cases odd
  · change ‖Complex.exp (w * (u : ℂ)) + Complex.exp ((1 - w) * (u : ℂ))‖ ≤ _
    calc
      _ ≤ Real.exp u + Real.exp u := (norm_add_le _ _).trans (add_le_add hE₁ hE₂)
      _ ≤ _ := by linarith only [Real.exp_le_exp.mpr (show u ≤ 2 * u by linarith only [hu])]
  · change ‖(u : ℂ) * (Complex.exp (w * (u : ℂ)) - Complex.exp ((1 - w) * (u : ℂ)))‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
    have huExp : u ≤ Real.exp u := by linarith only [Real.add_one_le_exp u]
    calc
      _ ≤ Real.exp u * (Real.exp u + Real.exp u) :=
        mul_le_mul huExp ((norm_sub_le _ _).trans (add_le_add hE₁ hE₂)) (norm_nonneg _) (by positivity)
      _ = _ := by rw [two_mul u, Real.exp_add]; ring

private theorem scaled_heat_thirteen {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (2 * u) * discriminant23ReadingHeat u ^ 13 ≤ (3 / 11 : ℝ) ^ 13 * Real.exp (-(14 : ℝ) * u) := by
  let a := discriminant23ThetaScale
  have ha : 13 / 10 ≤ a := discriminant23_thetaScale_interval.1
  have han : 0 ≤ a := by linarith only [ha]
  have hG : 1 + u ≤ Real.exp u := by linarith only [Real.add_one_le_exp u]
  have hProd := mul_le_mul_of_nonneg_left hG han
  have hArg : 2 * u + (13 : ℕ) * (-a * Real.exp u) ≤ (13 : ℕ) * (-a) + -(14 : ℝ) * u := by
    push_cast
    nlinarith only [hProd, mul_nonneg (sub_nonneg.mpr ha) hu, hu]
  change Real.exp (2 * u) * Real.exp (-a * Real.exp u) ^ 13 ≤ _
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  calc
    _ ≤ Real.exp ((13 : ℕ) * (-a) + -(14 : ℝ) * u) := Real.exp_le_exp.mpr hArg
    _ = Real.exp (-a) ^ 13 * Real.exp (-(14 : ℝ) * u) := by rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) discriminant23_thetaExp_interval.2 13) (Real.exp_nonneg _)

private theorem sample_change {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) (odd : Bool) :
    ‖denseSample odd w u - sparseSample odd w u‖ ≤
      6 * ((3 / 11 : ℝ) ^ 13 * Real.exp (-(14 : ℝ) * u)) := by
  have hsmall := (heat_le hu).trans (by norm_num : (3 / 11 : ℝ) ≤ 1 / 3)
  have hpoly := discriminant23_characterPolynomial_sparse_error (Real.exp_nonneg _) hsmall
  unfold denseSample sparseSample
  rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (2 * Real.exp (2 * u)) * (3 * discriminant23ReadingHeat u ^ 13) :=
      mul_le_mul (phase_norm_le hlo hhi hu odd) hpoly (abs_nonneg _) (by positivity)
    _ = 6 * (Real.exp (2 * u) * discriminant23ReadingHeat u ^ 13) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (scaled_heat_thirteen hu) (by norm_num)


private theorem readingWeight_abs_le : ∀ j : Fin 257, |ninePointGridWeight 32 j| ≤ 10496 := by
  decide +kernel

private theorem quad_change_sharp {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (odd : Bool) :
    ‖ninePointComposite (denseSample odd w) 0 (3 / 64) 32 -
      ninePointComposite (sparseSample odd w) 0 (3 / 64) 32‖ ≤ 1 / 10 ^ 7 := by
  have hWeight (j : ℕ) (hj : j ∈ Finset.range 257) : |discriminant23ReadingWeight j| ≤ 1 / 28 := by
    have hx : |(ninePointGridWeight 32 j : ℝ)| ≤ 10496 := by
      exact_mod_cast readingWeight_abs_le ⟨j, Finset.mem_range.mp hj⟩
    rw [discriminant23ReadingWeight, abs_mul, abs_of_nonneg (by norm_num)]
    linarith only [hx]
  have hDecay (j : ℕ) :
      Real.exp (-(14 : ℝ) * discriminant23ReadingNode j) ≤ (128 / 149 : ℝ) ^ j := by
    rw [show -(14 : ℝ) * discriminant23ReadingNode j = (j : ℝ) * (-(21 / 128 : ℝ)) by
      unfold discriminant23ReadingNode; ring, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_nonneg _)
    rw [Real.exp_neg, ← one_div, show (128 / 149 : ℝ) = 1 / (149 / 128) by norm_num]
    exact one_div_le_one_div_of_le (by norm_num)
      (by linarith only [Real.add_one_le_exp (21 / 128 : ℝ)])
  have hRatio := hasSum_geometric_of_lt_one
    (by norm_num : 0 ≤ (128 / 149 : ℝ)) (by norm_num : (128 / 149 : ℝ) < 1)
  have hGeometric : ∑ j ∈ Finset.range 257, (128 / 149 : ℝ) ^ j ≤ 149 / 21 := by
    have h := hRatio.summable.sum_le_tsum (Finset.range 257) (fun j _ ↦ by positivity)
    rw [hRatio.tsum_eq] at h
    exact h.trans (by norm_num)
  simp_rw [composite_eq_sum]
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j ∈ Finset.range 257, (1 / 28 * (6 * (3 / 11) ^ 13) : ℝ) * (128 / 149) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h := sample_change hlo hhi (discriminant23_readingNode_mem hj).1 odd
      calc
        _ ≤ (1 / 28 : ℝ) * (6 * ((3 / 11) ^ 13 *
              Real.exp (-(14 : ℝ) * discriminant23ReadingNode j))) :=
          mul_le_mul (hWeight j hj) h (norm_nonneg _) (by norm_num)
        _ = (1 / 28 * (6 * (3 / 11) ^ 13) : ℝ) *
              Real.exp (-(14 : ℝ) * discriminant23ReadingNode j) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hDecay j) (by positivity)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left hGeometric (by positivity)).trans (by norm_num)

private theorem quad_change {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (odd : Bool) :
    ‖ninePointComposite (denseSample odd w) 0 (3 / 64) 32 -
      ninePointComposite (sparseSample odd w) 0 (3 / 64) 32‖ ≤ 11 / 5000000 :=
  (quad_change_sharp hlo hhi odd).trans (by norm_num)

def discriminant23ReadingArgument (w : ℂ) : ℂ :=
  (w - 1 / 2) / 6

def discriminant23ReadingRate (j : ℕ) : ℝ :=
  6 * discriminant23ReadingNode j

/-- The same weights give the slope after multiplication by the log-grid node. -/
def discriminant23ReadingAmplitude (odd : Bool) (j : ℕ) : ℝ :=
  let u := discriminant23ReadingNode j
  discriminant23ReadingWeight j * Real.exp (u / 2) *
    discriminant23SparsePolynomial (discriminant23ReadingHeat u) * (if odd then u else 1)

def discriminant23ReadingCoefficient (odd : Bool) (k : ℕ) : ℝ :=
  reflectedExpCoefficient (Finset.range 257) (discriminant23ReadingAmplitude odd)
    discriminant23ReadingRate odd k

/-- Seventy-two terms, including zero coefficients from parity. -/
def discriminant23ReadingTaylor (odd : Bool) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range 72, (discriminant23ReadingCoefficient odd k : ℂ) *
    discriminant23ReadingArgument w ^ k

private theorem sparse_quad_eq_exp_sum (odd : Bool) (w : ℂ) :
    ninePointComposite (sparseSample odd w) 0 (3 / 64) 32 =
      reflectedExpSum (Finset.range 257) (discriminant23ReadingAmplitude odd)
        discriminant23ReadingRate odd (discriminant23ReadingArgument w) := by
  rw [composite_eq_sum, reflectedExpSum]
  apply Finset.sum_congr rfl
  intro j _
  let u := discriminant23ReadingNode j
  let z := (discriminant23ReadingRate j : ℂ) * discriminant23ReadingArgument w
  have hz : z = (w - 1 / 2) * (u : ℂ) := by
    dsimp only [z, u, discriminant23ReadingRate, discriminant23ReadingArgument]
    push_cast
    ring
  have h₁ : Complex.exp (w * (u : ℂ)) = (Real.exp (u / 2) : ℂ) * Complex.exp z := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, hz]
    congr 1
    push_cast
    ring
  have h₂ : Complex.exp ((1 - w) * (u : ℂ)) = (Real.exp (u / 2) : ℂ) * Complex.exp (-z) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, hz]
    congr 1
    push_cast
    ring
  change (discriminant23ReadingWeight j : ℂ) * sparseSample odd w u =
    (discriminant23ReadingAmplitude odd j : ℂ) * reflectedExp odd z
  cases odd <;>
    simp [sparseSample, phase, h₁, h₂, discriminant23ReadingAmplitude, u, reflectedExp,
      reflectedExpSign, Complex.ofReal_mul] <;> ring

private theorem sparse_density_abs_le {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 3) :
    |discriminant23SparsePolynomial q| ≤ 2 := by
  have h₂ := pow_le_pow_left₀ hq₀ hq₁ 2
  have h₃ := pow_le_pow_left₀ hq₀ hq₁ 3
  have h₆ := pow_le_pow_left₀ hq₀ hq₁ 6
  have h₈ := pow_le_pow_left₀ hq₀ hq₁ 8
  unfold discriminant23SparsePolynomial
  apply abs_le.mpr
  constructor <;> linarith only [hq₀, hq₁, h₂, h₃, h₆, h₈, pow_nonneg hq₀ 2,
    pow_nonneg hq₀ 3, pow_nonneg hq₀ 6, pow_nonneg hq₀ 8]

private theorem exp_half_le_five {u : ℝ} (hu : u ≤ 3) : Real.exp (u / 2) ≤ 5 := by
  refine (Real.exp_le_exp.mpr (show u / 2 ≤ 3 / 2 by linarith only [hu])).trans ?_
  have hpair : Real.exp (3 / 2 : ℝ) ^ 2 = Real.exp 3 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hThree : Real.exp 3 ≤ (29 / 10 : ℝ) ^ 3 := by
    rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [Real.exp_one_lt_d9]) 3
  apply (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 5)).mp
  rw [hpair]
  exact hThree.trans (by norm_num)

private theorem amplitude_mass (odd : Bool) :
    ∑ j ∈ Finset.range 257, |discriminant23ReadingAmplitude odd j| ≤ (22 / 5 : ℝ) * 30 := by
  calc
    _ ≤ ∑ j ∈ Finset.range 257, |discriminant23ReadingWeight j| * (30 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      let u := discriminant23ReadingNode j
      have hu := discriminant23_readingNode_mem hj
      have hq := (heat_le hu.1).trans (by norm_num : (3 / 11 : ℝ) ≤ 1 / 3)
      have hD : |discriminant23SparsePolynomial (discriminant23ReadingHeat u)| ≤ 2 :=
        sparse_density_abs_le (Real.exp_nonneg _) hq
      have hF : |if odd then u else 1| ≤ 3 := by
        cases odd
        · norm_num
        · exact (abs_of_nonneg hu.1).trans_le hu.2
      dsimp only [discriminant23ReadingAmplitude]
      simp only [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc
        _ ≤ |discriminant23ReadingWeight j| * 5 * 2 * 3 := by
          gcongr
          exact exp_half_le_five hu.2
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right weight_mass (by norm_num)

private theorem argument_norm_le_one {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1)
    (ht : |w.im| ≤ 11 / 2) : ‖discriminant23ReadingArgument w‖ ≤ 1 := by
  have hr : |(w - 1 / 2).re| ≤ 1 / 2 := by
    have h : (w - 1 / 2).re = w.re - 1 / 2 := by norm_num [Complex.sub_re, Complex.div_re]
    rw [h]
    exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩
  have hi : |(w - 1 / 2).im| ≤ 11 / 2 := by
    simpa [Complex.sub_im, Complex.div_im] using ht
  have hn : ‖w - 1 / 2‖ ≤ 6 :=
    (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith only [hr, hi])
  have hSix : ‖(6 : ℂ)‖ = (6 : ℝ) := by
    rw [show (6 : ℂ) = ((6 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  rw [discriminant23ReadingArgument, norm_div, hSix]
  exact (div_le_one (by norm_num)).mpr hn

private theorem sparse_quad_taylor_error_of_radius {w : ℂ} {R : ℝ}
    (hR : R / 73 ≤ 1 / 2) (harg : ‖discriminant23ReadingArgument w‖ ≤ R / 18)
    (odd : Bool) :
    ‖ninePointComposite (sparseSample odd w) 0 (3 / 64) 32 - discriminant23ReadingTaylor odd w‖ ≤
      (22 / 5 * 30) * (4 * R ^ 72 / (Nat.factorial 72 : ℝ)) := by
  have hnode (j : ℕ) (hj : j ∈ Finset.range 257) :
      ‖(discriminant23ReadingRate j : ℂ) * discriminant23ReadingArgument w‖ ≤ R := by
    obtain ⟨hu, hu'⟩ := discriminant23_readingNode_mem hj
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ discriminant23ReadingRate j by unfold discriminant23ReadingRate; positivity)]
    have hRate : discriminant23ReadingRate j ≤ 18 := by
      unfold discriminant23ReadingRate
      linarith only [hu']
    calc
      _ ≤ 18 * (R / 18) := mul_le_mul hRate harg (norm_nonneg _) (by norm_num)
      _ = R := by ring
  rw [sparse_quad_eq_exp_sum]
  change ‖reflectedExpSum (Finset.range 257) (discriminant23ReadingAmplitude odd)
    discriminant23ReadingRate odd (discriminant23ReadingArgument w) -
      reflectedExpPolynomial (Finset.range 257) (discriminant23ReadingAmplitude odd)
        discriminant23ReadingRate odd 72 (discriminant23ReadingArgument w)‖ ≤ _
  have hR₀ : 0 ≤ R := by linarith only [harg, norm_nonneg (discriminant23ReadingArgument w)]
  refine (reflectedExpPolynomial_error_le _ _ _ odd 72 (by simpa using hR) hnode).trans ?_
  exact mul_le_mul_of_nonneg_right (amplitude_mass odd) (by positivity)

private theorem sparse_quad_taylor_error {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1)
    (ht : |w.im| ≤ 11 / 2) (odd : Bool) :
    ‖ninePointComposite (sparseSample odd w) 0 (3 / 64) 32 - discriminant23ReadingTaylor odd w‖ ≤
      1 / 10 ^ 10 := by
  refine (sparse_quad_taylor_error_of_radius (R := 18) (by norm_num)
    (by simpa using argument_norm_le_one hlo hhi ht) odd).trans ?_
  norm_num [Nat.factorial]

/-- The same stored coefficient row works at every input inside the supplied
Taylor radius once the quadrature error there has been bounded. -/
theorem discriminant23_value_taylor_error_of_quadrature {w : ℂ} {R E : ℝ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (hR : R / 73 ≤ 1 / 2)
    (harg : ‖discriminant23ReadingArgument w‖ ≤ R / 18)
    (hQuad : ‖discriminant23CharacterComplexModel w -
      ninePointComposite (fun u ↦ discriminant23PanelValue w u) 0 (3 / 64) 32‖ ≤ E) :
    ‖discriminant23CharacterComplexModel w - discriminant23ReadingTaylor false w‖ ≤
      E + (11 / 5000000 + (22 / 5 * 30) * (4 * R ^ 72 / (Nat.factorial 72 : ℝ))) := by
  have heq : denseSample false w = fun u : ℝ ↦ discriminant23PanelValue w u := by
    funext u
    simp [denseSample, phase, discriminant23PanelValue, panelDensity_ofReal]
  rw [← heq] at hQuad
  exact (norm_sub_le_norm_sub_add_norm_sub _ (ninePointComposite (denseSample false w) 0 (3 / 64) 32)
    _).trans (add_le_add hQuad ((norm_sub_le_norm_sub_add_norm_sub _
      (ninePointComposite (sparseSample false w) 0 (3 / 64) 32) _).trans
        (add_le_add (quad_change hlo hhi false) (sparse_quad_taylor_error_of_radius hR harg false))))

/-- The absolute 72nd moment of the quadrature weights at nodes rescaled to
the unit interval. In particular, small weights at the largest nodes stay small. -/
def discriminant23ReadingMomentMass (odd : Bool) : ℝ :=
  ∑ j ∈ Finset.range 257, |discriminant23ReadingAmplitude odd j| *
    (discriminant23ReadingNode j / 3) ^ 72

private theorem sparse_quad_taylor_error_of_moment {w : ℂ} {r : ℝ}
    (hcut : 18 * r / 73 ≤ 1 / 2) (hr : ‖discriminant23ReadingArgument w‖ ≤ r)
    (odd : Bool) :
    ‖ninePointComposite (sparseSample odd w) 0 (3 / 64) 32 - discriminant23ReadingTaylor odd w‖ ≤
      discriminant23ReadingMomentMass odd * (4 * (18 * r) ^ 72 / (Nat.factorial 72 : ℝ)) := by
  have hRate (j : ℕ) (hj : j ∈ Finset.range 257) :
      0 ≤ discriminant23ReadingRate j ∧ discriminant23ReadingRate j ≤ 18 := by
    obtain ⟨h₀, h₁⟩ := discriminant23_readingNode_mem hj
    unfold discriminant23ReadingRate
    exact ⟨by linarith only [h₀], by linarith only [h₁]⟩
  have hr₀ : 0 ≤ r := (norm_nonneg _).trans hr
  have hTerm (j : ℕ) (hj : j ∈ Finset.range 257) :
      (discriminant23ReadingRate j * r) / (Nat.succ 72 : ℝ) ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hRate j hj).2 hr₀)
      (by norm_num : (0 : ℝ) ≤ (Nat.succ 72 : ℝ))).trans hcut
  have hNode (j : ℕ) (hj : j ∈ Finset.range 257) :
      ‖(discriminant23ReadingRate j : ℂ) * discriminant23ReadingArgument w‖ ≤
        discriminant23ReadingRate j * r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hRate j hj).1]
    exact mul_le_mul_of_nonneg_left hr (hRate j hj).1
  rw [sparse_quad_eq_exp_sum]
  refine (reflectedExpPolynomial_error_le_of_radii (Finset.range 257)
    (discriminant23ReadingAmplitude odd) discriminant23ReadingRate
    (fun j ↦ discriminant23ReadingRate j * r) odd 72 hTerm hNode).trans ?_
  unfold discriminant23ReadingMomentMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  apply le_of_eq
  rw [show discriminant23ReadingRate j * r =
      (discriminant23ReadingNode j / 3) * (18 * r) by unfold discriminant23ReadingRate; ring,
    mul_pow]
  ring

/-- Supply quadrature checks for the same samples on a larger rectangle.
The exponential remainder is proportional to the actual weighted moment. -/
theorem discriminant23_character_taylor_bounds_of_quadrature_sharp {w : ℂ} {r EValue ESlope : ℝ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1)
    (hcut : 18 * r / 73 ≤ 1 / 2) (hr : ‖discriminant23ReadingArgument w‖ ≤ r)
    (hValue : ‖discriminant23CharacterComplexModel w -
      ninePointComposite (fun u ↦ discriminant23PanelValue w u) 0 (3 / 64) 32‖ ≤ EValue)
    (hSlope : ‖deriv discriminant23CharacterComplexModel w -
      ninePointComposite (fun u ↦ discriminant23PanelSlope w u) 0 (3 / 64) 32‖ ≤ ESlope) :
    ‖discriminant23CharacterComplexModel w - discriminant23ReadingTaylor false w‖ ≤
      EValue + (1 / 10 ^ 7 + discriminant23ReadingMomentMass false *
        (4 * (18 * r) ^ 72 / (Nat.factorial 72 : ℝ))) ∧
    ‖deriv discriminant23CharacterComplexModel w - discriminant23ReadingTaylor true w‖ ≤
      ESlope + (1 / 10 ^ 7 + discriminant23ReadingMomentMass true *
        (4 * (18 * r) ^ 72 / (Nat.factorial 72 : ℝ))) := by
  let E (odd : Bool) := if odd then ESlope else EValue
  have hQuad (odd : Bool) :
      ‖reading odd w - ninePointComposite (denseSample odd w) 0 (3 / 64) 32‖ ≤ E odd := by
    cases odd
    · have hEq : denseSample false w = fun u : ℝ ↦ discriminant23PanelValue w u := by
        funext u
        simp [denseSample, phase, discriminant23PanelValue, panelDensity_ofReal]
      rw [hEq]
      exact hValue
    · have hEq : denseSample true w = fun u : ℝ ↦ discriminant23PanelSlope w u := by
        funext u
        simp [denseSample, phase, discriminant23PanelSlope, panelDensity_ofReal]
      rw [hEq]
      exact hSlope
  have hBoth (odd : Bool) : ‖reading odd w - discriminant23ReadingTaylor odd w‖ ≤
      E odd + (1 / 10 ^ 7 + discriminant23ReadingMomentMass odd *
        (4 * (18 * r) ^ 72 / (Nat.factorial 72 : ℝ))) :=
    (norm_sub_le_norm_sub_add_norm_sub _ (ninePointComposite (denseSample odd w) 0 (3 / 64) 32)
      _).trans (add_le_add (hQuad odd) ((norm_sub_le_norm_sub_add_norm_sub _
        (ninePointComposite (sparseSample odd w) 0 (3 / 64) 32) _).trans
          (add_le_add (quad_change_sharp hlo hhi odd) (sparse_quad_taylor_error_of_moment hcut hr odd))))
  exact ⟨hBoth false, hBoth true⟩


/-- Supply a common quadrature allowance for both readings, as in the lower bands. -/
theorem discriminant23_character_taylor_bounds_of_quadrature_weighted {w : ℂ} {r E : ℝ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1)
    (hcut : 18 * r / 73 ≤ 1 / 2) (hr : ‖discriminant23ReadingArgument w‖ ≤ r)
    (hValue : ‖discriminant23CharacterComplexModel w -
      ninePointComposite (fun u ↦ discriminant23PanelValue w u) 0 (3 / 64) 32‖ ≤ E)
    (hSlope : ‖deriv discriminant23CharacterComplexModel w -
      ninePointComposite (fun u ↦ discriminant23PanelSlope w u) 0 (3 / 64) 32‖ ≤ E) :
    ‖discriminant23CharacterComplexModel w - discriminant23ReadingTaylor false w‖ ≤
      E + (11 / 5000000 + discriminant23ReadingMomentMass false *
        (4 * (18 * r) ^ 72 / (Nat.factorial 72 : ℝ))) ∧
    ‖deriv discriminant23CharacterComplexModel w - discriminant23ReadingTaylor true w‖ ≤
      E + (11 / 5000000 + discriminant23ReadingMomentMass true *
        (4 * (18 * r) ^ 72 / (Nat.factorial 72 : ℝ))) := by
  have h := discriminant23_character_taylor_bounds_of_quadrature_sharp hlo hhi hcut hr hValue hSlope
  exact ⟨h.1.trans (by linarith), h.2.trans (by linarith)⟩

#print axioms discriminant23_character_taylor_bounds_of_quadrature_sharp

/-- This single allowance includes grid integration, the five-term substitution,
and the shared exponential Taylor tail. -/
theorem discriminant23_character_taylor_bounds {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1)
    (ht : |w.im| ≤ 11 / 2) :
    ‖discriminant23CharacterComplexModel w - discriminant23ReadingTaylor false w‖ ≤ 33 / 1000000 ∧
    ‖deriv discriminant23CharacterComplexModel w - discriminant23ReadingTaylor true w‖ ≤ 33 / 1000000 := by
  have both (odd : Bool) : ‖reading odd w - discriminant23ReadingTaylor odd w‖ ≤ 33 / 1000000 := by
    calc
      _ ≤ ‖reading odd w - ninePointComposite (denseSample odd w) 0 (3 / 64) 32‖ +
          ‖ninePointComposite (denseSample odd w) 0 (3 / 64) 32 -
            discriminant23ReadingTaylor odd w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (3 / 100000 : ℝ) +
          (‖ninePointComposite (denseSample odd w) 0 (3 / 64) 32 -
              ninePointComposite (sparseSample odd w) 0 (3 / 64) 32‖ +
            ‖ninePointComposite (sparseSample odd w) 0 (3 / 64) 32 -
              discriminant23ReadingTaylor odd w‖) := by
        exact add_le_add (reading_quad hlo hhi ht odd) (norm_sub_le_norm_sub_add_norm_sub _ _ _)
      _ ≤ _ := by linarith only [quad_change hlo hhi odd, sparse_quad_taylor_error hlo hhi ht odd]
  exact ⟨both false, both true⟩

/-- After the analytic transfer, only signed inequalities on the two explicit
Taylor polynomials remain for the count. -/
theorem discriminant23_character_counts_of_taylor_signs
    (hBelow : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (7 / 6) (9 / 2) →
      43 / 1000000 < (discriminant23ReadingTaylor false w).re)
    (hAbove : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (83 / 16) (11 / 2) →
      (discriminant23ReadingTaylor false w).re < -(43 / 1000000))
    (hSlope : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (9 / 2) (83 / 16) →
      43 / 1000000 < (discriminant23ReadingTaylor true w).im) :
    discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) (fun _ ↦ True) = 2 ∧
      discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) (fun w ↦ w.re = 1 / 2) = 2 := by
  refine discriminant23_character_counts_at_eleven_halves_of_model_signs ?_ ?_ ?_
  · intro w hr ht
    have hT : |w.im| ≤ 11 / 2 := abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
    have h := (Complex.abs_re_le_norm _).trans (discriminant23_character_taylor_bounds hr.1 hr.2 hT).1
    rw [Complex.sub_re] at h
    linarith only [(abs_le.mp h).1, hBelow w hr ht]
  · intro w hr ht
    have hT : |w.im| ≤ 11 / 2 := abs_le.mpr ⟨by linarith only [ht.1], ht.2⟩
    have h := (Complex.abs_re_le_norm _).trans (discriminant23_character_taylor_bounds hr.1 hr.2 hT).1
    rw [Complex.sub_re] at h
    linarith only [(abs_le.mp h).2, hAbove w hr ht]
  · intro w hr ht
    have hT : |w.im| ≤ 11 / 2 := abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
    have h := (Complex.abs_im_le_norm _).trans (discriminant23_character_taylor_bounds hr.1 hr.2 hT).2
    rw [Complex.sub_im] at h
    linarith only [(abs_le.mp h).1, hSlope w hr ht]

#check @discriminant23_character_taylor_bounds
#check @discriminant23_character_counts_of_taylor_signs
#print axioms discriminant23_character_taylor_bounds
#print axioms discriminant23_character_taylor_bounds_of_quadrature_weighted
#print axioms discriminant23_character_counts_of_taylor_signs

end

end FieldTarget

