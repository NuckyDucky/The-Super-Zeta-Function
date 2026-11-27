import DedekindDiscriminant23CharacterSamples
import DedekindDiscriminant23CharacterMoments

/-! Directed real intervals for the five-term grid amplitudes and their Taylor
moments. The moment multiplier is one exact rational at each dyadic node. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed
open Set
open scoped BigOperators

noncomputable section

def discriminant23ReadingNodeBox (j : ℕ) : Box :=
  fromRatio (3 * (j : ℤ)) 256

private def halfNodeBox (j : ℕ) : Box :=
  fromRatio (3 * (j : ℤ)) 512

private def readingWeightBox (j : ℕ) : Box :=
  fromRatio (3 * ninePointGridWeight 32 j) (32 * 28350)

private def fiveTermHeatBox (q : Box) : Box :=
  let square := mul q q
  let cube := mul square q
  let sixth := mul cube cube
  mul (constant 2) (add (add (sub (sub q square) cube) sixth) (mul sixth square))

def discriminant23ReadingAmplitudeBox (odd : Bool) (j : ℕ) : Box :=
  let half := expFixed (halfNodeBox j)
  let q := expFixed (neg (mul discriminant23ThetaScaleBox (mul half half)))
  let amp := mul (mul (readingWeightBox j) half) (fiveTermHeatBox q)
  if odd then mul amp (discriminant23ReadingNodeBox j) else amp

private theorem nodeBox_contains (j : ℕ) :
    Contains (discriminant23ReadingNodeBox j) (discriminant23ReadingNode j) := by
  unfold discriminant23ReadingNodeBox discriminant23ReadingNode
  simpa using ratio_contains (3 * (j : ℤ)) (d := 256) (by norm_num)

private theorem halfNodeBox_contains (j : ℕ) :
    Contains (halfNodeBox j) (discriminant23ReadingNode j / 2) := by
  have h := ratio_contains (3 * (j : ℤ)) (d := 512) (by norm_num)
  change Contains (halfNodeBox j) _ at h
  convert h using 1
  unfold discriminant23ReadingNode
  push_cast
  ring

private theorem readingWeightBox_contains (j : ℕ) :
    Contains (readingWeightBox j) (discriminant23ReadingWeight j) := by
  have h := ratio_contains (3 * ninePointGridWeight 32 j) (d := 32 * 28350) (by norm_num)
  change Contains (readingWeightBox j) _ at h
  convert h using 1
  unfold discriminant23ReadingWeight
  push_cast
  ring

private theorem fiveTermHeatBox_contains {q : Box} {x : ℝ} (hx : Contains q x) :
    Contains (fiveTermHeatBox q) (discriminant23SparsePolynomial x) := by
  have h₂ := mul_contains hx hx
  have h₃ := mul_contains h₂ hx
  have h₆ := mul_contains h₃ h₃
  have h₈ := mul_contains h₆ h₂
  have h := mul_contains (constant_contains 2)
    (add_contains (add_contains (sub_contains (sub_contains hx h₂) h₃) h₆) h₈)
  change Contains (fiveTermHeatBox q) _ at h
  convert h using 1
  unfold discriminant23SparsePolynomial
  push_cast
  ring

/-- Every fixed-point amplitude encloses the exact five-term reading at its node. -/
theorem discriminant23_readingAmplitudeBox_contains (odd : Bool) {j : ℕ} (hj : j < 257) :
    Contains (discriminant23ReadingAmplitudeBox odd j) (discriminant23ReadingAmplitude odd j) := by
  let u := discriminant23ReadingNode j
  have hu : u ∈ Icc (0 : ℝ) 3 := discriminant23_readingNode_mem (Finset.mem_range.mpr hj)
  have hHalf : |u / 2| ≤ 128 := abs_le.mpr ⟨by linarith only [hu.1], by linarith only [hu.2]⟩
  have hh := expFixed_contains (halfNodeBox_contains j) hHalf
  have hI := mul_contains hh hh
  rw [← Real.exp_add, show u / 2 + u / 2 = u by ring] at hI
  have ha := discriminant23_thetaScale_interval
  have ha₀ : 0 ≤ discriminant23ThetaScale := by linarith only [ha.1]
  have he : Real.exp u ≤ 27 := by
    refine (Real.exp_le_exp.mpr hu.2).trans ?_
    rw [show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (by positivity) Real.exp_one_lt_three.le 3).trans (by norm_num)
  have hsize : |- (discriminant23ThetaScale * Real.exp u)| ≤ 128 := by
    rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ discriminant23ThetaScale * Real.exp u)]
    exact (mul_le_mul ha.2 he (Real.exp_nonneg _) (by norm_num)).trans (by norm_num)
  have hq := expFixed_contains (neg_contains (mul_contains discriminant23_thetaScaleBox_contains hI))
    (by simpa only [neg_mul] using hsize)
  have hA := mul_contains (mul_contains (readingWeightBox_contains j) hh) (fiveTermHeatBox_contains hq)
  cases odd
  · simpa [discriminant23ReadingAmplitudeBox, discriminant23ReadingAmplitude,
      discriminant23ReadingHeat] using hA
  · simpa [discriminant23ReadingAmplitudeBox, discriminant23ReadingAmplitude,
      discriminant23ReadingHeat] using mul_contains hA (nodeBox_contains j)

/-- Since the argument is normalized by six, the exponential rate is the
exact dyadic `9 * j / 128`. Put the factorial into the same denominator. -/
def discriminant23MomentMultiplierBox (j k : ℕ) : Box :=
  fromRatio ((9 * (j : ℤ)) ^ k) ((128 : ℤ) ^ k * k.factorial)

theorem discriminant23_momentMultiplierBox_contains (j k : ℕ) :
    Contains (discriminant23MomentMultiplierBox j k)
      (discriminant23ReadingRate j ^ k / (k.factorial : ℝ)) := by
  have hd : 0 < (128 : ℤ) ^ k * k.factorial := by positivity
  have h := ratio_contains ((9 * (j : ℤ)) ^ k) hd
  change Contains (discriminant23MomentMultiplierBox j k) _ at h
  convert h using 1
  push_cast
  rw [show discriminant23ReadingRate j = (9 * (j : ℝ) / 128) by
    unfold discriminant23ReadingRate discriminant23ReadingNode
    ring, div_pow, div_div]

private def sumBoxes (f : ℕ → Box) : ℕ → Box
  | 0 => constant 0
  | n + 1 => add (sumBoxes f n) (f n)

private theorem sumBoxes_contains (f : ℕ → Box) (x : ℕ → ℝ) {n : ℕ}
    (h : ∀ i < n, Contains (f i) (x i)) :
    Contains (sumBoxes f n) (∑ j ∈ Finset.range n, x j) := by
  induction n with
  | zero => simpa only [sumBoxes, Finset.range_zero, Finset.sum_empty, Int.cast_zero] using
      constant_contains 0
  | succ n ih =>
    rw [sumBoxes, Finset.sum_range_succ]
    exact add_contains (ih fun i hi ↦ h i (hi.trans n.lt_succ_self)) (h n n.lt_succ_self)

def discriminant23ReadingCoefficientBox (amplitudes : ℕ → Box) (odd : Bool) (k : ℕ) : Box :=
  if k % 2 = (if odd then 1 else 0) then
    sumBoxes (fun j ↦ mul (mul (amplitudes j) (constant 2))
      (discriminant23MomentMultiplierBox j k)) 257
  else constant 0

/-- The validated amplitude table can be shared by all coefficients. -/
theorem discriminant23_readingCoefficientBox_contains (amplitudes : ℕ → Box) (odd : Bool) (k : ℕ)
    (hAmp : ∀ j < 257, Contains (amplitudes j) (discriminant23ReadingAmplitude odd j)) :
    Contains (discriminant23ReadingCoefficientBox amplitudes odd k)
      (discriminant23ReadingCoefficient odd k) := by
  unfold discriminant23ReadingCoefficientBox discriminant23ReadingCoefficient reflectedExpCoefficient
  rw [reflectedExpParity_eq]
  by_cases h : k % 2 = (if odd then 1 else 0)
  · simp only [h, ite_true, Int.cast_ofNat]
    apply sumBoxes_contains
    intro j hj
    simpa only [Int.cast_ofNat, mul_div_assoc] using
      mul_contains (mul_contains (hAmp j hj) (constant_contains 2))
        (discriminant23_momentMultiplierBox_contains j k)
  · simpa [h] using constant_contains 0

#print axioms discriminant23_readingAmplitudeBox_contains
#print axioms discriminant23_momentMultiplierBox_contains
#print axioms discriminant23_readingCoefficientBox_contains

end

end FieldTarget

