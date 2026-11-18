import SuperZeta.Reciprocal
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! All derivative orders of the original reciprocal return and phase recovery
from the cubic and quartic coefficients of its normalized germ. -/
namespace SuperZeta.Touchard
open Complex Polynomial
noncomputable section

/-- Touchard polynomials in the recurrence convention of the coefficient-fields note. -/
def T : ℕ → ℂ[X]
  | 0 => 1
  | n+1 => X * (T n + (T n).derivative)

def inner (a b z : ℂ) := a * exp (b*z)
def tower (a b z : ℂ) := exp (inner a b z)

private theorem inner_d (a b z : ℂ) : HasDerivAt (inner a b) (b*inner a b z) z := by
  convert (((hasDerivAt_id z).const_mul b).cexp.const_mul a) using 1
  simp [inner]
  ring

private theorem tower_d (a b z : ℂ) : HasDerivAt (tower a b)
    ((tower a b z)*(b*inner a b z)) z := (inner_d a b z).cexp

private theorem step_d (n : ℕ) (a b c z : ℂ) :
    HasDerivAt (fun z => c * b^n * (T n).eval (inner a b z) * tower a b z)
      (c * b^(n+1) * (T (n+1)).eval (inner a b z) * tower a b z) z := by
  have h := ((((T n).hasDerivAt _).comp z (inner_d a b z)).const_mul (c*b^n)).mul
    (tower_d a b z)
  convert h using 1
  simp only [T, eval_mul, eval_X, eval_add, pow_succ, Function.comp_apply]
  ring

theorem tower_derivatives (n : ℕ) (a b z : ℂ) :
    iteratedDeriv n (tower a b) z = b^n * (T n).eval (inner a b z) * tower a b z := by
  induction n generalizing z with
  | zero => simp [T]
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    simpa using (step_d n a b 1 z).deriv

/-- Proposition 3.2 for the map of the original ordered fixed-pair equations. -/
theorem return_derivatives (n : ℕ) (L z : ℂ) :
    iteratedDeriv n (Reciprocal.scalarReturn L) z =
      (-L)^n * (T n).eval (L*exp (-L*z)) * Reciprocal.scalarReturn L z :=
  tower_derivatives n L (-L) z

private theorem affine_derivatives (n : ℕ) (a b c d z : ℂ) :
    iteratedDeriv (n+1) (fun z => c*tower a b z+d) z =
      c*b^(n+1)*(T (n+1)).eval (inner a b z)*tower a b z := by
  induction n generalizing z with
  | zero =>
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
    convert (((tower_d a b z).const_mul c).add_const d).deriv using 1
    simp [T]
    ring
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    exact (step_d (n+1) a b c z).deriv

/-- Equation (4.4) of the manuscript. Its parabolic chart is used at a≠0,−1. -/
def normal (a z : ℂ) := ((1+a)/(2*a)) * (exp (a*(exp (2*z/(1+a))-1))-1)

theorem normalized_derivatives (n : ℕ) (a : ℂ) (ha : a ≠ 0) (hp : 1+a ≠ 0) :
    iteratedDeriv (n+1) (normal a) 0 = 2^n * (T (n+1)).eval a / (a*(1+a)^n) := by
  have hf : normal a = fun z =>
      (((1+a)/(2*a))*exp (-a)) * tower a (2/(1+a)) z - ((1+a)/(2*a)) := by
    funext z
    simp only [normal, tower, inner]
    simp only [mul_sub, mul_one, exp_sub, exp_neg]
    rw [show 2*z/(1+a) = (2/(1+a))*z by ring]
    ring
  rw [hf]
  change iteratedDeriv (n+1) (fun z => _ * tower a (2/(1+a)) z + -_) 0 = _
  rw [affine_derivatives]
  simp only [tower, inner, mul_zero, Complex.exp_zero, mul_one, Complex.exp_neg, div_pow, pow_succ]
  field_simp [ha,hp,Complex.exp_ne_zero]
  ring

def cubic (a : ℂ) := 2*(a^2+3*a+1)/(3*(a+1)^2)
def quartic (a : ℂ) := (a^3+6*a^2+7*a+1)/(3*(a+1)^3)

theorem cubic_coefficient (a : ℂ) (ha : a ≠ 0) (hp : 1+a ≠ 0) :
    iteratedDeriv 3 (normal a) 0 / 6 = cubic a := by
  rw [normalized_derivatives 2 a ha hp]
  simp [T, Polynomial.derivative_mul, cubic]
  field_simp [ha,hp,show a+1≠0 by rwa [add_comm]]
  ring

theorem quartic_coefficient (a : ℂ) (ha : a ≠ 0) (hp : 1+a ≠ 0) :
    iteratedDeriv 4 (normal a) 0 / 24 = quartic a := by
  rw [normalized_derivatives 3 a ha hp]
  simp [T, Polynomial.derivative_mul, quartic]
  field_simp [ha,hp,show a+1≠0 by rwa [add_comm]]
  ring

def recoveryCoordinate (h₃ h₄ : ℂ) := (24*h₄-22+42*(1-h₃))/(6*(1-h₃)-2)

/-- The measurement denominator equals −4a/(1+a)², so every nonzero phase
in the normalized chart is recoverable, including the self-reciprocal a=1. -/
theorem recovery_denominator (a : ℂ) (hp : a+1 ≠ 0) :
    6*(1-cubic a)-2 = -4*a/(a+1)^2 := by
  unfold cubic
  field_simp [hp]
  ring

theorem recover_phase (a : ℂ) (ha : a ≠ 0) (hp : a+1 ≠ 0) :
    let w := recoveryCoordinate (cubic a) (quartic a)
    (1+w)/(1-w) = a := by
  have hw : recoveryCoordinate (cubic a) (quartic a) = (a-1)/(a+1) := by
    unfold recoveryCoordinate
    rw [recovery_denominator a hp]
    unfold cubic quartic
    field_simp [ha,hp]
    ring
  dsimp only
  rw [hw]
  have hd : 1-(a-1)/(a+1) = 2/(a+1) := by field_simp [hp]; ring
  rw [hd]
  field_simp [hp]

theorem singular_recovery_iff (a : ℂ) (hp : a+1 ≠ 0) :
    6*(1-cubic a)-2 = 0 ↔ a=0 := by
  rw [recovery_denominator a hp]
  simp [hp]

/-- The cubic forgets which reciprocal phase was chosen. -/
theorem cubic_reciprocal (a : ℂ) (ha : a ≠ 0) (hp : a+1 ≠ 0) :
    cubic a = cubic a⁻¹ := by
  have hn : a⁻¹+1 = (a+1)/a := by field_simp [ha]; ring
  unfold cubic
  rw [hn, div_pow]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow]
  field_simp [ha,hp]
  ring

/-- The quartic records the signed distinction between the two reciprocal phases. -/
theorem quartic_reciprocal (a : ℂ) (ha : a ≠ 0) (hp : a+1 ≠ 0) :
    quartic a-quartic a⁻¹ = a*(1-a)/(3*(a+1)^3) := by
  have hn : a⁻¹+1 = (a+1)/a := by field_simp [ha]; ring
  have h : quartic a⁻¹ = (1+6*a+7*a^2+a^3)/(3*(a+1)^3) := by
    unfold quartic
    rw [hn, div_pow]
    apply (div_eq_div_iff (mul_ne_zero (by norm_num) (div_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ ha)))
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hp))).2
    field_simp [ha]
    ring
  rw [h, quartic, ←sub_div]
  congr 1
  ring

/-- Equivalently Q(h₃,h₄)=Q(a): exactly the same complex subfields contain
the two measured coefficients as contain the phase. -/
theorem joint_coefficient_field (K : Subfield ℂ) (a : ℂ) (ha : a ≠ 0) (hp : a+1 ≠ 0) :
    a ∈ K ↔ cubic a ∈ K ∧ quartic a ∈ K := by
  have two : (2:ℂ) ∈ K := natCast_mem K 2
  have three : (3:ℂ) ∈ K := natCast_mem K 3
  have six : (6:ℂ) ∈ K := natCast_mem K 6
  have seven : (7:ℂ) ∈ K := natCast_mem K 7
  have h₁ := K.one_mem
  constructor
  · intro h
    unfold cubic quartic
    constructor <;> repeat first | assumption | apply K.div_mem | apply K.add_mem | apply K.mul_mem | apply K.pow_mem
  · rintro ⟨h₃,h₄⟩
    have hw : recoveryCoordinate (cubic a) (quartic a) ∈ K := by
      have h24 : (24:ℂ) ∈ K := natCast_mem K 24
      have h22 : (22:ℂ) ∈ K := natCast_mem K 22
      have h42 : (42:ℂ) ∈ K := natCast_mem K 42
      unfold recoveryCoordinate
      repeat first | assumption | apply K.div_mem | apply K.sub_mem | apply K.add_mem | apply K.mul_mem
    have h := K.div_mem (K.add_mem h₁ hw) (K.sub_mem h₁ hw)
    simpa only [recover_phase a ha hp] using h

end
end SuperZeta.Touchard
