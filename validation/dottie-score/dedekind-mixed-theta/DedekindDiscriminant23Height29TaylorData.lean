import GaussianRationalPolynomial
import DedekindDiscriminant23Height29FactorEnclosures

namespace FieldTarget

open Complex
open scoped BigOperators

noncomputable section

set_option exponentiation.threshold 512

private theorem complex_coe_gaussian_natCast (n : ℕ) : ((n : GaussianInt) : ℂ) = (n : ℂ) :=
  map_natCast GaussianInt.toComplex n

def discriminant23Height29TaylorCenter : ℂ := (3 / 4 : ℂ) + 29 * I

private def height29TaylorData : Array (GaussianInt × GaussianInt) := #[
  (⟨606609028222025586005269692786029400, 10456445096033106908690983390564931⟩, ⟨10184513472771059832, -8291986062790293011⟩),
  (⟨-1081165623058354939680755189277092, 41813359040512400219856165923769811⟩, ⟨43179563080233718351, -36018331643035918244⟩),
  (⟨-2161261172386027088324597565336600, -74516999504801745179291140993955⟩, ⟨112840700778070530231, -14726992090176901725⟩),
  (⟨4279405640400587087403909693027, -99282259990996181138186965094635⟩, ⟨109455603812384716693, -3086455330160708792⟩),
  (⟨4274959907183217460064786608576, 221156776958192528277489795081⟩, ⟨126985962940352825200, 54698979839118357863⟩),
  (⟨-10665960974676345803732597454, 176680391259520519935462876250⟩, ⟨41383556441961337181, 64338822032064138898⟩),
  (⟨-7097981110668056074834943987, -489842556191688316972173125⟩, ⟨25056860775528791721, 42925910574717578960⟩),
  (⟨21690265529458766169030683, -279287183778397850120233649⟩, ⟨-5290742701216307254, 29586373561552543320⟩),
  (⟨10815638629635168709771895, 933663028275332510358161⟩, ⟨-5073726125492468984, 7616115673552249641⟩),
  (⟨-39295399770851554733132, 413607474358968388658307⟩, ⟨-3405472300155676917, 3436074755519954497⟩),
  (⟨-15657961690715081715064, -1623239307695417262050⟩, ⟨-1699822986287567711, 15974453044412183⟩),
  (⟨65596713056732163688, -587715312967757998574⟩, ⟨-374073567276278864, -78999593249408963⟩),
  (⟨21742582135046587102, 2544575943188012592⟩, ⟨-133918521010208182, -90177277801000298⟩),
  (⟨-112519666687261357, 769090397752637922⟩, ⟨-7751479425306937, -36096996211442407⟩),
  (⟨-30666225768859860, -12048263952019697⟩, ⟨-1080380620929113, -7337112171144340⟩),
  (⟨1263866797820160, -3438788486581948⟩, ⟨982677376785883, -2193727690563077⟩),
  (⟨414950160463827, -164110924683418⟩, ⟨341092119285886, -173108431628122⟩),
  (⟨72176683711065, -32003155668318⟩, ⟨69669552778329, -34790229655204⟩),
  (⟨18600100381659, 4947236540772⟩, ⟨18051186115480, 4488184548693⟩),
  (⟨1614510178021, 1620492440877⟩, ⟨1621533524243, 1510826228940⟩),
  (⟨318568000761, 362522787022⟩, ⟨321822708239, 354715751447⟩),
  (⟨-4468784844, 83566165740⟩, ⟨-3382243002, 82088654292⟩),
  (⟨-2669342586, 8034247086⟩, ⟨-2445063307, 8042923311⟩),
  (⟨-1024851580, 1496192578⟩, ⟨-1010885873, 1500758205⟩),
  (⟨-218086176, 45699979⟩, ⟨-215744216, 47273279⟩),
  (⟨-23313209, 4185785⟩, ⟨-23310450, 4473546⟩),
  (⟨-4061674, -1566053⟩, ⟨-4064467, -1549339⟩),
  (⟨-209053, -324809⟩, ⟨-210529, -322275⟩),
  (⟨-28222, -41330⟩, ⟨-28466, -41308⟩),
  (⟨841, -6781⟩, ⟨827, -6781⟩),
  (⟨222, -438⟩, ⟨220, -439⟩),
  (⟨45, -60⟩, ⟨45, -60⟩),
  (⟨7, -1⟩, ⟨7, -1⟩),
  (⟨1, 0⟩, ⟨1, 0⟩),
  (⟨0, 0⟩, ⟨0, 0⟩),
  (⟨0, 0⟩, ⟨0, 0⟩)
]

private def height29TaylorNumerator (total : Bool) (k : ℕ) : GaussianInt :=
  if total then height29TaylorData[k]!.1 else height29TaylorData[k]!.2

def height29SavedTaylorNumerator (total : Bool) (k : ℕ) : GaussianInt :=
  height29TaylorNumerator total k

def discriminant23Height29TaylorApprox (total : Bool) (k : ℕ) : ℂ :=
  gaussianScaled (height29TaylorNumerator total k) height29FactorDenominator

def discriminant23Height29TaylorPolynomial (total : Bool) (d : ℂ) : ℂ :=
  ∑ k ∈ Finset.range 36, discriminant23Height29TaylorApprox total k * d ^ k

private def height29TaylorNumerators (total : Bool) : List GaussianInt :=
  List.ofFn fun k : Fin 36 ↦ height29TaylorNumerator total k

def height29RoundedOffsetNumerator (j : ℕ) : GaussianInt :=
  star (contourRoot128PhaseNumerator j)

def height29RoundedOffsetDenominator : ℕ := 2 * contourRoot128Scale

def height29RoundedOffset (j : ℕ) : ℂ :=
  gaussianScaled (height29RoundedOffsetNumerator j) height29RoundedOffsetDenominator

def height29RoundedPoint (j : ℕ) : ℂ := discriminant23Height29TaylorCenter + height29RoundedOffset j

private def height29RoundedPointNumerator (j : ℕ) : GaussianInt :=
  ⟨3 * 2 ^ 95, 29 * 2 ^ 97⟩ + height29RoundedOffsetNumerator j

private def height29PoleDenominatorNumerator (j : ℕ) : GaussianInt :=
  height29RoundedPointNumerator j *
    ((height29RoundedOffsetDenominator : GaussianInt) - height29RoundedPointNumerator j)

private def height29TaylorValueDenominator : ℕ :=
  height29FactorDenominator * height29RoundedOffsetDenominator ^ 36

private def height29TaylorValueNumerator (total : Bool) (j : ℕ) : GaussianInt :=
  gaussianScaledHorner (height29RoundedOffsetNumerator j) height29RoundedOffsetDenominator
    (height29TaylorNumerators total)

def height29TaylorDifferenceNumerator (total : Bool) (j : ℕ) : GaussianInt :=
  height29TaylorValueNumerator total j - ((height29RoundedOffsetDenominator ^ 36 : ℕ) : GaussianInt) *
    (if total then height29BaseNumerator j else height29HeckeNumerator j)

def height29BaseResidualNumerator (j : ℕ) : GaussianInt :=
  2 * height29TaylorDifferenceNumerator true j * height29PoleDenominatorNumerator j -
    ((3 * height29TaylorValueDenominator * height29RoundedOffsetDenominator ^ 2 : ℕ) : GaussianInt)

def height29BaseResidualDenominator : ℕ :=
  2 * height29TaylorValueDenominator * height29RoundedOffsetDenominator ^ 2

private theorem height29TaylorValueNumerator_correct (total : Bool) (j : ℕ) :
    discriminant23Height29TaylorPolynomial total (height29RoundedOffset j) =
      gaussianScaled (height29TaylorValueNumerator total j) height29TaylorValueDenominator := by
  let a := height29TaylorNumerators total
  let z := height29RoundedOffset j
  have hPoly : discriminant23Height29TaylorPolynomial total z =
      gaussianPolynomialEval a z / (height29FactorDenominator : ℂ) := by
    simp only [a, height29TaylorNumerators, gaussianPolynomialEval_ofFn,
      discriminant23Height29TaylorPolynomial, discriminant23Height29TaylorApprox]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦
      (height29TaylorNumerator total k : ℂ) * z ^ k), Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ ↦ by unfold gaussianScaled; ring
  have ha : a.length = 36 := by simp [a, height29TaylorNumerators]
  have hd : height29RoundedOffsetDenominator ≠ 0 := by
    norm_num [height29RoundedOffsetDenominator, contourRoot128Scale]
  change discriminant23Height29TaylorPolynomial total z = _
  rw [hPoly]
  change gaussianPolynomialEval a
    (gaussianScaled (height29RoundedOffsetNumerator j) height29RoundedOffsetDenominator) / _ = _
  rw [gaussianPolynomialEval_eq_scaledHorner a _ hd, ha]
  simp only [gaussianScaled, height29TaylorValueNumerator, a, height29TaylorValueDenominator,
    Nat.cast_mul, Nat.cast_pow]
  rw [div_div, mul_comm]

private theorem height29RoundedPoint_eq_scaled (j : ℕ) :
    height29RoundedPoint j =
      gaussianScaled (height29RoundedPointNumerator j) height29RoundedOffsetDenominator := by
  unfold height29RoundedPoint
  simp only [discriminant23Height29TaylorCenter, height29RoundedPointNumerator, height29RoundedOffset,
    gaussianScaled, map_add]
  have h : ((⟨3 * 2 ^ 95, 29 * 2 ^ 97⟩ : GaussianInt) : ℂ) /
      (height29RoundedOffsetDenominator : ℂ) = (3 / 4 : ℂ) + 29 * I := by
    norm_num [GaussianInt.toComplex_def', height29RoundedOffsetDenominator, contourRoot128Scale]
    ring
  rw [add_div, h]

private theorem height29PoleDenominator_eq_scaled (j : ℕ) :
    height29RoundedPoint j * (1 - height29RoundedPoint j) =
      gaussianScaled (height29PoleDenominatorNumerator j) (height29RoundedOffsetDenominator ^ 2) := by
  have hd : (height29RoundedOffsetDenominator : ℂ) ≠ 0 := by
    norm_num [height29RoundedOffsetDenominator, contourRoot128Scale]
  rw [height29RoundedPoint_eq_scaled]
  simp only [gaussianScaled, height29PoleDenominatorNumerator, map_mul, map_sub, map_natCast, Nat.cast_pow]
  field_simp

private theorem height29TaylorDifference_eq_scaled (total : Bool) (j : ℕ) :
    discriminant23Height29TaylorPolynomial total (height29RoundedOffset j) -
      (if total then discriminant23Height29BaseApprox j else discriminant23Height29HeckeApprox j) =
      gaussianScaled (height29TaylorDifferenceNumerator total j) height29TaylorValueDenominator := by
  rw [height29TaylorValueNumerator_correct]
  have hd : (height29RoundedOffsetDenominator : ℂ) ≠ 0 := by
    norm_num [height29RoundedOffsetDenominator, contourRoot128Scale]
  have hb : (height29FactorDenominator : ℂ) ≠ 0 := by norm_num [height29FactorDenominator]
  cases total <;>
    simp only [Bool.false_eq_true, ↓reduceIte, discriminant23Height29BaseApprox,
      discriminant23Height29HeckeApprox, gaussianScaled, height29TaylorDifferenceNumerator,
      height29TaylorValueDenominator, map_sub, map_mul, complex_coe_gaussian_natCast] <;>
    push_cast <;> field_simp

private theorem height29BaseResidual_eq_scaled (j : ℕ) :
    (discriminant23Height29TaylorPolynomial true (height29RoundedOffset j) -
      discriminant23Height29BaseApprox j) *
      (height29RoundedPoint j * (1 - height29RoundedPoint j)) - (3 / 2 : ℂ) =
      gaussianScaled (height29BaseResidualNumerator j) height29BaseResidualDenominator := by
  have hDiff := height29TaylorDifference_eq_scaled true j
  simp only [↓reduceIte] at hDiff
  rw [hDiff, height29PoleDenominator_eq_scaled]
  simp only [height29BaseResidualNumerator, height29BaseResidualDenominator, gaussianScaled,
    map_sub, map_mul, map_ofNat, complex_coe_gaussian_natCast]
  push_cast
  have hd : (height29RoundedOffsetDenominator : ℂ) ≠ 0 := by
    norm_num [height29RoundedOffsetDenominator, contourRoot128Scale]
  have hb : (height29TaylorValueDenominator : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < height29TaylorValueDenominator by
      unfold height29TaylorValueDenominator height29FactorDenominator height29RoundedOffsetDenominator
        contourRoot128Scale
      positivity))
  field_simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem height29Taylor_derivative_budget_checked :
    ∀ total : Bool,
      (∑ k ∈ Finset.range 36, k * gaussianL1 (height29TaylorNumerator total k)) * 1000 ≤
        height29FactorDenominator := by
  decide +kernel

theorem height29Taylor_derivative_budget (total : Bool) :
    (∑ k ∈ Finset.range 36, (k : ℝ) * ‖discriminant23Height29TaylorApprox total k‖) ≤ 1 / 1000 := by
  have hd : (0 : ℝ) < height29FactorDenominator := by norm_num [height29FactorDenominator]
  have hCheck : (∑ k ∈ Finset.range 36, (k : ℝ) * (gaussianL1 (height29TaylorNumerator total k) : ℝ)) *
      1000 ≤ (height29FactorDenominator : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr (height29Taylor_derivative_budget_checked total)
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using h
  calc
    _ ≤ (∑ k ∈ Finset.range 36, (k : ℝ) * (gaussianL1 (height29TaylorNumerator total k) : ℝ)) /
        (height29FactorDenominator : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro k _
      rw [discriminant23Height29TaylorApprox, gaussianScaled, norm_div, Complex.norm_natCast,
        ← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_gaussianInt_le_l1 _) (Nat.cast_nonneg k)) hd.le
    _ ≤ _ := by
      rw [div_le_iff₀ hd]
      linarith only [hCheck]

/-- Exact rational checks imply the bound at the rounded base phase. -/
theorem height29_base_residual_le {j : ℕ}
    (hCheck : gaussianL1 (height29BaseResidualNumerator j) * 10 ^ 27 ≤
      height29BaseResidualDenominator * 784) :
    ‖(discriminant23Height29TaylorPolynomial true (height29RoundedOffset j) -
      discriminant23Height29BaseApprox j) *
      (height29RoundedPoint j * (1 - height29RoundedPoint j)) - (3 / 2 : ℂ)‖ ≤ 784 / 10 ^ 27 := by
  rw [height29BaseResidual_eq_scaled]
  have h := norm_gaussianScaled_le_of_l1
    (show 0 < height29BaseResidualDenominator by
      unfold height29BaseResidualDenominator height29TaylorValueDenominator height29FactorDenominator
        height29RoundedOffsetDenominator contourRoot128Scale
      positivity) (by norm_num) hCheck
  simpa only [Nat.cast_ofNat, Nat.cast_pow] using h

/-- Exact rational checks imply the bound at the rounded Hecke phase. -/
theorem height29_hecke_residual_le {j : ℕ}
    (hCheck : gaussianL1 (height29TaylorDifferenceNumerator false j) * 10 ^ 27 ≤
      height29TaylorValueDenominator * 1) :
    ‖discriminant23Height29TaylorPolynomial false (height29RoundedOffset j) -
      discriminant23Height29HeckeApprox j‖ ≤ 1 / 10 ^ 27 := by
  have hDiff := height29TaylorDifference_eq_scaled false j
  simp only [Bool.false_eq_true, ↓reduceIte] at hDiff
  rw [hDiff]
  have h := norm_gaussianScaled_le_of_l1
    (show 0 < height29TaylorValueDenominator by
      unfold height29TaylorValueDenominator height29FactorDenominator height29RoundedOffsetDenominator
        contourRoot128Scale
      positivity) (by norm_num) hCheck
  simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] using h

/-- The finite integer comparisons needed for one index. -/
def Height29TaylorComparison (j : ℕ) : Prop :=
  gaussianL1 (height29BaseResidualNumerator j) * 10 ^ 27 ≤ height29BaseResidualDenominator * 784 ∧
    gaussianL1 (height29TaylorDifferenceNumerator false j) * 10 ^ 27 ≤ height29TaylorValueDenominator * 1

instance (j : ℕ) : Decidable (Height29TaylorComparison j) := by
  unfold Height29TaylorComparison
  infer_instance

#print axioms height29Taylor_derivative_budget
#print axioms height29_base_residual_le
#print axioms height29_hecke_residual_le

end
end FieldTarget
