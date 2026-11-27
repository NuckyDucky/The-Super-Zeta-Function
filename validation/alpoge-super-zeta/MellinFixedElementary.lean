import MellinFixedFunctions
import MellinFixedIntervalSound
import Mathlib.Data.Real.Pi.Bounds

/-! Taylor bounds and range reduction for the fixed-point exponentials and trigonometric functions. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.MellinFixed

private def expCoefficient (k : Nat) : Box := fromRatio 1 (k.factorial:Int)
private def cosCoefficient (k : Nat) : Box := fromRatio ((-1:Int)^k) ((2*k).factorial:Int)
private def sinCoefficient (k : Nat) : Box := fromRatio ((-1:Int)^k) ((2*k+1).factorial:Int)

private theorem exp_table : expCoefficients = coefficients expCoefficient 0 26 := by decide +kernel
private theorem cos_table : cosCoefficients = coefficients cosCoefficient 0 13 := by decide +kernel
private theorem sin_table : sinCoefficients = coefficients sinCoefficient 0 13 := by decide +kernel

private theorem exp_coefficient_contains (k : Nat) :
    Contains (expCoefficient k) (1/(k.factorial:ℝ)) := by
  have hk : (0:Int) < (k.factorial:Int) := by exact_mod_cast Nat.factorial_pos k
  simpa only [expCoefficient, Int.cast_one, Int.cast_natCast] using ratio_contains 1 hk

private theorem cos_coefficient_contains (k : Nat) :
    Contains (cosCoefficient k) (((-1:ℝ)^k)/((2*k).factorial:ℝ)) := by
  have hk : (0:Int) < ((2*k).factorial:Int) := by exact_mod_cast Nat.factorial_pos (2*k)
  simpa only [cosCoefficient, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] using
    ratio_contains ((-1:Int)^k) hk

private theorem sin_coefficient_contains (k : Nat) :
    Contains (sinCoefficient k) (((-1:ℝ)^k)/((2*k+1).factorial:ℝ)) := by
  have hk : (0:Int) < ((2*k+1).factorial:Int) := by exact_mod_cast Nat.factorial_pos (2*k+1)
  simpa only [sinCoefficient, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] using
    ratio_contains ((-1:Int)^k) hk

private theorem tail26 {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r^26 * ((27:ℝ)/(Nat.factorial 26*26)) ≤ 1/(scale:ℝ) := by
  have hp : r^26 ≤ 1 := by simpa using pow_le_pow_left₀ hr hr1 26
  calc
    _ ≤ 1 * ((27:ℝ)/(Nat.factorial 26*26)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ _ := by norm_num [scale, Nat.factorial]

private theorem expSmall_contains {a : Box} {x : ℝ} (hx : Contains a x) (h1 : |x| ≤ 1) :
    Contains (expSmall a) (Real.exp x) := by
  have h := horner_contains hx expCoefficient (fun k => 1/(k.factorial:ℝ))
    exp_coefficient_contains 0 26
  rw [← exp_table] at h
  have e := (Real.exp_bound h1 (n := 26) (by decide)).trans (tail26 (abs_nonneg x) h1)
  have hsum : (∑ k ∈ Finset.range 26, (1/(k.factorial:ℝ))*x^k) =
      ∑ k ∈ Finset.range 26, x^k/(k.factorial:ℝ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [Nat.zero_add] at h
  rw [hsum] at h
  exact widen_contains h (units := 1) (by simpa only [Nat.cast_one] using e)

theorem expFixed_contains {a : Box} {x : ℝ} (hx : Contains a x) (h : |x| ≤ 128) :
    Contains (expFixed a) (Real.exp x) := by
  have h1 : |x/128| ≤ (1:ℝ) := by
    rw [abs_div, abs_of_pos (show (0:ℝ) < 128 by norm_num), div_le_one (by norm_num)]
    exact h
  have hb : Contains (divInt a 128) (x/128) := by
    simpa only [Int.cast_ofNat] using divInt_contains hx (d := 128) (by decide)
  have hs := squareSteps_contains (expSmall_contains hb h1) 7
  have he : (Real.exp (x/128))^(2^7 : Nat) = Real.exp x := by
    rw [show (2:Nat)^7 = 128 by decide, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rwa [he] at hs

private def cosPoly (n : Nat) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (((-1:ℝ)^k)/((2*k).factorial:ℝ))*(x*x)^k

private def sinPoly (n : Nat) (x : ℝ) : ℝ :=
  x*(∑ k ∈ Finset.range n, (((-1:ℝ)^k)/((2*k+1).factorial:ℝ))*(x*x)^k)

private theorem complex_two_terms (n : Nat) (x : ℝ) :
    (∑ k ∈ Finset.range (2*n), ((x:ℂ)*Complex.I)^k/(k.factorial:ℂ)) =
      (cosPoly n x:ℂ)+(sinPoly n x:ℂ)*Complex.I := by
  induction n with
  | zero => simp [cosPoly,sinPoly]
  | succ n ih =>
    have he : ((x:ℂ)*Complex.I)^(2*n) =
        (-1:ℂ)^n*((x:ℂ)*(x:ℂ))^n := by
      rw [pow_mul, mul_pow, Complex.I_sq, pow_two (x:ℂ), mul_pow, mul_comm]
    have ho : ((x:ℂ)*Complex.I)^(2*n+1) =
        (-1:ℂ)^n*((x:ℂ)*(x:ℂ))^n*(x:ℂ)*Complex.I := by
      rw [pow_succ, he]
      ring
    rw [show 2*(n+1) = (2*n+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, ih, he, ho]
    simp only [cosPoly, sinPoly, Finset.sum_range_succ _ n]
    push_cast
    ring

private theorem trigSmall_error {x : ℝ} (h : |x| ≤ 1) :
    |Real.cos x - cosPoly 13 x| ≤ 1/(scale:ℝ) ∧
      |Real.sin x - sinPoly 13 x| ≤ 1/(scale:ℝ) := by
  have hn : ‖(x:ℂ)*Complex.I‖ = |x| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have ht := Complex.exp_bound (x := (x:ℂ)*Complex.I) (n := 26) (by simpa only [hn] using h) (by decide)
  rw [hn, show (26:Nat) = 2*13 by decide, complex_two_terms] at ht
  have ht' := ht.trans (tail26 (abs_nonneg x) h)
  constructor
  · have hp := (Complex.abs_re_le_norm _).trans ht'
    simpa [Complex.exp_re, Complex.sub_re, Complex.mul_re, Complex.mul_im] using hp
  · have hp := (Complex.abs_im_le_norm _).trans ht'
    simpa [Complex.exp_im, Complex.sub_im, Complex.mul_re, Complex.mul_im] using hp

theorem unit_contains {a : Box} {x : ℝ} (h : Contains a x) (hb : inUnit a = true) : |x| ≤ 1 := by
  have hd : -scale ≤ a.lo ∧ a.hi ≤ scale := of_decide_eq_true hb
  have hlo : -((scale:ℝ)) ≤ (a.lo:ℝ) := by exact_mod_cast hd.1
  have hhi : (a.hi:ℝ) ≤ (scale:ℝ) := by exact_mod_cast hd.2
  apply abs_le.mpr
  exact ⟨le_of_mul_le_mul_left (by simpa only [mul_neg, mul_one] using hlo.trans h.1) scale_pos,
    le_of_mul_le_mul_left (by simpa only [mul_one] using h.2.trans hhi) scale_pos⟩

private theorem cosSinSmall_contains {a : Box} {x : ℝ} (hx : Contains a x) (h : |x| ≤ 1) :
    Contains (cosSinSmall a).1 (Real.cos x) ∧ Contains (cosSinSmall a).2 (Real.sin x) := by
  have hcos := horner_contains (mul_contains hx hx) cosCoefficient _ cos_coefficient_contains 0 13
  have hsin := horner_contains (mul_contains hx hx) sinCoefficient _ sin_coefficient_contains 0 13
  rw [← cos_table] at hcos
  rw [← sin_table] at hsin
  have hr := (trigSmall_error h).1
  have hi := (trigSmall_error h).2
  simp only [Nat.zero_add] at hcos hsin
  exact ⟨widen_contains hcos (units := 1) (by simpa only [cosPoly, Nat.cast_one] using hr),
    widen_contains (mul_contains hx hsin) (units := 1) (by simpa only [sinPoly, Nat.cast_one] using hi)⟩

private theorem doubledAngle_contains {p : Box × Box} {x : ℝ}
    (h : Contains p.1 (Real.cos x) ∧ Contains p.2 (Real.sin x)) :
    Contains (doubledAngle p).1 (Real.cos (2*x)) ∧ Contains (doubledAngle p).2 (Real.sin (2*x)) := by
  rcases p with ⟨c,s⟩
  constructor
  · rw [two_mul, Real.cos_add]
    exact sub_contains (mul_contains h.1 h.1) (mul_contains h.2 h.2)
  · rw [two_mul, Real.sin_add, show Real.sin x*Real.cos x+Real.cos x*Real.sin x =
      2*(Real.sin x*Real.cos x) by ring]
    simpa only [doubledAngle, Int.cast_ofNat] using
      mul_contains (constant_contains 2) (mul_contains h.2 h.1)

private theorem pi_contains : Contains piBox Real.pi := by
  have hl := Real.pi_gt_d20
  have hu := Real.pi_lt_d20
  constructor
  · norm_num [piBox,scale]
    linarith only [hl]
  · norm_num [piBox,scale]
    linarith only [hu]

theorem cosSinFixed_contains {a : Box} {x : ℝ} (hx : Contains a x)
    (h : inUnit (divInt (reducedPhase a) 4) = true) :
    Contains (cosSinFixed a).1 (Real.cos x) ∧ Contains (cosSinFixed a).2 (Real.sin x) := by
  let y := x-((phaseTurn a:Int):ℝ)*(2*Real.pi)
  have hy : Contains (reducedPhase a) y := by
    have hconst := constant_contains (2*phaseTurn a)
    have hz := sub_contains hx (mul_contains hconst pi_contains)
    simpa only [reducedPhase, y, Int.cast_mul, Int.cast_ofNat, mul_assoc, mul_comm (2:ℝ)] using hz
  have hs : Contains (divInt (reducedPhase a) 4) (y/4) := by
    simpa only [Int.cast_ofNat] using divInt_contains hy (d := 4) (by decide)
  have ht := doubledAngle_contains (doubledAngle_contains (cosSinSmall_contains hs (unit_contains hs h)))
  rw [show (2:ℝ)*(2*(y/4)) = y by ring] at ht
  simpa only [cosSinFixed, y, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi] using ht

#print axioms expFixed_contains
#print axioms cosSinFixed_contains

end DottieOriented.NativeSpectrum.MellinFixed
end
