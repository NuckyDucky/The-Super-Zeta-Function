import DedekindDiscriminant23CharacterIntegral
import MellinFixedElementary
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Directed fixed-point samples for the two discriminant-23 endpoint readings. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

def discriminant23EndpointNumerator (high : Bool) : ℤ := if high then 11 else 10

def discriminant23EndpointHeight (high : Bool) : ℝ :=
  (discriminant23EndpointNumerator high : ℝ) / 2

def discriminant23LogNode (i : Fin 1025) : ℝ := 3 * (i.val : ℝ) / 1024

private def alphaBox : Box := ⟨1310134702738000000000000, 1310134702739000000000000⟩

private theorem alphaBox_contains : Contains alphaBox discriminant23ThetaScale := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 23 by norm_num)
  have hnonneg := Real.sqrt_nonneg 23
  have hSlo : (4795831523312 / 10^12 : ℝ) ≤ Real.sqrt 23 := by nlinarith
  have hShi : Real.sqrt 23 ≤ (4795831523313 / 10^12 : ℝ) := by nlinarith
  have hSpos := Real.sqrt_pos.2 (show (0 : ℝ) < 23 by norm_num)
  have hlo : (1310134702738 / 10^12 : ℝ) ≤ discriminant23ThetaScale := by
    unfold discriminant23ThetaScale
    apply (le_div_iff₀ hSpos).2
    nlinarith only [hShi, Real.pi_gt_d20]
  have hhi : discriminant23ThetaScale ≤ (1310134702739 / 10^12 : ℝ) := by
    unfold discriminant23ThetaScale
    apply (div_le_iff₀ hSpos).2
    nlinarith only [hSlo, Real.pi_lt_d20]
  unfold Contains alphaBox scale
  constructor <;> norm_num <;> linarith

private def halfNodeBox (i : Fin 1025) : Box := fromRatio (3 * (i.val : ℤ)) 2048

private def phaseBox (high : Bool) (i : Fin 1025) : Box :=
  fromRatio (discriminant23EndpointNumerator high * 3 * (i.val : ℤ)) 2048

private def polynomialBox (q : Box) : Box :=
  horner q (coefficients (fun n ↦ constant (discriminant23CharacterCoefficient n)) 0 33)

/-- The two sample rows use the same log grid and the same fixed-point arithmetic. -/
def discriminant23CharacterSample (high : Bool) (i : Fin 1025) : Box :=
  let e := expFixed (halfNodeBox i)
  let q := expFixed (neg (mul alphaBox (mul e e)))
  mul (mul (mul (constant 2) e) (cosSinFixed (phaseBox high i)).1) (polynomialBox q)

private theorem node_range (i : Fin 1025) : 0 ≤ discriminant23LogNode i ∧
    discriminant23LogNode i ≤ 3 := by
  have hi : (i.val : ℝ) ≤ 1024 := by exact_mod_cast (Nat.lt_succ_iff.mp i.isLt)
  unfold discriminant23LogNode
  exact ⟨by positivity, by linarith⟩

private theorem exp_three_le_twenty_seven : Real.exp 3 ≤ 27 := by
  calc
    _ = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (3 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
    _ = _ := by norm_num

private theorem phases_fit : ∀ (high : Bool) (i : Fin 1025),
    inUnit (divInt (reducedPhase (phaseBox high i)) 4) = true := by
  decide +kernel

theorem discriminant23_characterSample_contains (high : Bool) (i : Fin 1025) :
    Contains (discriminant23CharacterSample high i)
      (discriminant23CharacterLogPolynomial (discriminant23EndpointHeight high)
        (discriminant23LogNode i)) := by
  let u := discriminant23LogNode i
  let t := discriminant23EndpointHeight high
  have hu : 0 ≤ u ∧ u ≤ 3 := node_range i
  have hhalf : Contains (halfNodeBox i) (u / 2) := by
    have h : Contains (halfNodeBox i) (3 * (i.val : ℝ) / 2048) := by
      simpa only [halfNodeBox, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using
        ratio_contains (3 * (i.val : ℤ)) (d := 2048) (by decide)
    rwa [show 3 * (i.val : ℝ) / 2048 = u / 2 by dsimp [u, discriminant23LogNode]; ring] at h
  have hε := expFixed_contains hhalf (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hex : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE := mul_contains hε hε
  rw [hex] at hE
  have hH := neg_contains (mul_contains alphaBox_contains hE)
  have hα := discriminant23_thetaScale_interval
  have hU : Real.exp u ≤ 27 := (Real.exp_le_exp.mpr hu.2).trans exp_three_le_twenty_seven
  have hA : |-(discriminant23ThetaScale * Real.exp u)| ≤ 128 := by
    rw [abs_neg, abs_of_nonneg (mul_nonneg (by linarith [hα.1]) (Real.exp_nonneg _))]
    have h := mul_le_mul hα.2 hU (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 4 / 3)
    linarith only [h]
  have hq := expFixed_contains hH hA
  have hp := horner_contains hq
    (fun n ↦ constant (discriminant23CharacterCoefficient n))
    (fun n ↦ (discriminant23CharacterCoefficient n : ℝ))
    (fun n ↦ constant_contains _) 0 33
  have hp' : Contains
      (polynomialBox (expFixed (neg (mul alphaBox (mul (expFixed (halfNodeBox i))
        (expFixed (halfNodeBox i)))))))
      (discriminant23CharacterPolynomial (Real.exp (-(discriminant23ThetaScale * Real.exp u)))) := by
    simpa only [polynomialBox, discriminant23CharacterPolynomial, Nat.zero_add] using hp
  have hphase : Contains (phaseBox high i) (t * u) := by
    have h : Contains (phaseBox high i)
        ((discriminant23EndpointNumerator high : ℝ) * 3 * (i.val : ℝ) / 2048) := by
      simpa only [phaseBox, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using
        ratio_contains (discriminant23EndpointNumerator high * 3 * (i.val : ℤ))
          (d := 2048) (by decide)
    rwa [show (discriminant23EndpointNumerator high : ℝ) * 3 * (i.val : ℝ) / 2048 = t * u by
      dsimp [t, u, discriminant23EndpointHeight, discriminant23LogNode]; ring] at h
  have hcos := (cosSinFixed_contains hphase (phases_fit high i)).1
  have h := mul_contains (mul_contains (mul_contains (constant_contains 2) hε) hcos) hp'
  change Contains (discriminant23CharacterSample high i)
    (2 * Real.exp (u / 2) * Real.cos (t * u) *
      discriminant23CharacterPolynomial (Real.exp (-discriminant23ThetaScale * Real.exp u)))
  simpa only [discriminant23CharacterSample, neg_mul, Int.cast_ofNat] using h

#check @discriminant23_characterSample_contains
#print axioms phases_fit
#print axioms discriminant23_characterSample_contains

end

end FieldTarget
