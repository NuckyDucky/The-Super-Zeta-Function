import Mathlib.Data.Real.Pi.Wallis
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The balanced-sign normalization in the Barnes–Dottie product. -/
namespace SuperZeta.Barnes
open Filter Finset
open scoped Topology
noncomputable section

/-- Probability of observing exactly as many positive as negative signs in 2n trials. -/
def B (n : ℕ) : ℝ := n.centralBinom / 4^n

/-- The purely binomial component of the quartet normalization. -/
def D (n : ℕ) : ℝ := Real.pi * n * B n ^ 2

theorem B_succ (n : ℕ) : B (n+1) = B n * ((2*n+1)/(2*n+2)) := by
  have h : ((n:ℝ)+1) * ((n+1).centralBinom:ℝ) =
      2*(2*(n:ℝ)+1)*n.centralBinom := by exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold B
  rw [pow_succ]
  field_simp
  linear_combination (2*(4:ℝ)^n)*h

/-- The finite bridge between the balanced-sign count and the half-integer Gamma values. -/
theorem gamma_half_grid (n : ℕ) :
    Real.Gamma ((n:ℝ)+1/2) = Real.sqrt Real.pi * n.factorial * B n := by
  induction n with
  | zero => simpa [B] using Real.Gamma_one_half_eq
  | succ n ih =>
    rw [Nat.cast_succ, show (n:ℝ)+1+1/2 = ((n:ℝ)+1/2)+1 by ring,
      Real.Gamma_add_one (show (n:ℝ)+1/2 ≠ 0 by positivity), ih, B_succ, Nat.factorial_succ]
    push_cast
    field_simp [show 2*(n:ℝ)+2 ≠ 0 by positivity]
    ring

/-- Exact finite Barnes identity, cross-multiplied. Only the two sampled
Gamma recurrences for G are needed; its normalization is G(2)=1. -/
theorem finite_barnes_identity (G : ℝ → ℝ) (h2 : G 2 = 1)
    (step : ∀ x : ℝ, 0 < x → G (x+1) = Real.Gamma x * G x) (N : ℕ) :
    (∏ k ∈ range N, D (k+1)) * (G (3/2) * G ((N:ℝ)+2))^2 =
      (N.factorial:ℝ) * G ((N:ℝ)+3/2)^2 := by
  induction N with
  | zero => simp [h2]
  | succ n ih =>
    have a : G ((n:ℝ)+1+2) = (n+1).factorial * G ((n:ℝ)+2) := by
      rw [show (n:ℝ)+1+2 = ((n:ℝ)+2)+1 by ring, step _ (by positivity)]
      have g := Real.Gamma_nat_eq_factorial (n+1)
      rw [Nat.cast_succ, show (n:ℝ)+1+1=(n:ℝ)+2 by ring] at g
      rw [g]
    have b : G ((n:ℝ)+1+3/2) = (Real.sqrt Real.pi * (n+1).factorial * B (n+1)) *
        G ((n:ℝ)+3/2) := by
      rw [show (n:ℝ)+1+3/2 = ((n:ℝ)+3/2)+1 by ring, step _ (by positivity)]
      have g := gamma_half_grid (n+1)
      rw [Nat.cast_succ, show (n:ℝ)+1+1/2=(n:ℝ)+3/2 by ring] at g
      rw [g]
    simp only [prod_range_succ, Nat.cast_succ, a, b, mul_pow,
      Real.sq_sqrt Real.pi_pos.le]
    simp only [D, Nat.cast_succ] at ih ⊢
    rw [show ((n+1).factorial:ℝ) = ((n:ℝ)+1)*n.factorial by
      rw [Nat.factorial_succ]; push_cast; ring]
    linear_combination Real.pi * ((n:ℝ)+1)^3 * (n.factorial:ℝ)^2 * B (n+1)^2 * ih

/-- Exact separation of the finite radial and binomial products, for any radius sequence. -/
theorem quartet_product (R : ℕ → ℝ) (N : ℕ) :
    (∏ k ∈ range N, R (k+1)*B (k+1)^2/2) =
      (∏ k ∈ range N, R (k+1)/(2*Real.pi*((k:ℝ)+1))) *
      ∏ k ∈ range N, D (k+1) := by
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro k _
  simp only [D, Nat.cast_add, Nat.cast_one]
  field_simp [Real.pi_ne_zero, show (k:ℝ)+1 ≠ 0 by positivity]
  ring

/-- Equation (4) of the normalization manuscript in denominator-free form. -/
theorem quartet_barnes_product (R : ℕ → ℝ) (G : ℝ → ℝ) (h2 : G 2 = 1)
    (step : ∀ x : ℝ, 0 < x → G (x+1) = Real.Gamma x * G x) (N : ℕ) :
    (∏ k ∈ range N, R (k+1)*B (k+1)^2/2) * (G (3/2) * G ((N:ℝ)+2))^2 =
      (∏ k ∈ range N, R (k+1)/(2*Real.pi*((k:ℝ)+1))) *
      ((N.factorial:ℝ) * G ((N:ℝ)+3/2)^2) := by
  rw [quartet_product, mul_assoc, finite_barnes_identity G h2 step]

/-- At every positive level the relative increase is exactly 1/(4n(n+1)).
The cross-product also holds at zero. -/
theorem D_increment (n : ℕ) :
    4*(n:ℝ)*(n+1)*(D (n+1) - D n) = D n := by
  simp only [D, B_succ, Nat.cast_succ]
  field_simp [show 2*(n:ℝ)+2 ≠ 0 by positivity]
  ring

theorem wallis_balance (n : ℕ) :
    Real.Wallis.W n * ((2*(n:ℝ)+1) * B n ^ 2) = 1 := by
  induction n with
  | zero => norm_num [Real.Wallis.W, B, Nat.centralBinom_zero]
  | succ n ih =>
    rw [Real.Wallis.W_succ, B_succ]
    push_cast
    have a : 2*(n:ℝ)+1 ≠ 0 := by positivity
    have b : 2*(n:ℝ)+2 ≠ 0 := by positivity
    have c : 2*(n:ℝ)+3 ≠ 0 := by positivity
    field_simp [a,b,c]
    linear_combination (2*(n:ℝ)+1)*(2*(n:ℝ)+2)^2*(2*(n:ℝ)+3) * ih

private lemma moments_tendsto :
    Tendsto (fun n : ℕ => (2*(n:ℝ)+1)*B n^2) atTop (𝓝 (2/Real.pi)) := by
  have h (n : ℕ) : (2*(n:ℝ)+1)*B n^2 = 1/Real.Wallis.W n := by
    rw [eq_div_iff (Real.Wallis.W_pos n).ne', mul_comm, wallis_balance]
  simp_rw [h]
  convert tendsto_const_nhds.div Real.Wallis.tendsto_W_nhds_pi_div_two
    (show Real.pi/2 ≠ 0 by positivity) using 1
  ring

private lemma inv_tendsto : Tendsto (fun n : ℕ => 1/(2*(n:ℝ)+1)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop.const_mul_atTop
    (show (0:ℝ)<2 by norm_num)).atTop_add tendsto_const_nhds)

private lemma B_sq_tendsto : Tendsto (fun n => B n^2) atTop (𝓝 0) := by
  convert moments_tendsto.mul inv_tendsto using 1
  · funext n
    dsimp
    field_simp [show 2*(n:ℝ)+1≠0 by positivity]
  · ring

theorem D_tendsto : Tendsto D atTop (𝓝 1) := by
  convert (moments_tendsto.sub B_sq_tendsto).const_mul (Real.pi/2) using 1
  · funext n
    simp [D]
    ring
  · field_simp [Real.pi_ne_zero]

private def lower (n : ℕ) := D n + Real.pi*B n^2/4
private def upper (n : ℕ) := lower n + Real.pi*B n^2/(4*((n:ℝ)+1))

private lemma lower_strictMono : StrictMono lower := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h : lower (n+1)-lower n = Real.pi * B n^2 / (16*((n:ℝ)+1)^2) := by
    dsimp only [lower,D]
    rw [B_succ]
    push_cast
    field_simp [show (2*(n:ℝ)+2) ≠ 0 by positivity, show (n:ℝ)+1 ≠ 0 by positivity]
    ring
  have hb : 0 < B n := by
    unfold B
    have hc := Nat.centralBinom_pos n
    positivity
  exact sub_pos.mp (h.symm ▸ (by positivity))

private lemma upper_antitone : Antitone upper := by
  apply antitone_nat_of_succ_le
  intro n
  have h : upper n-upper (n+1) =
      Real.pi * B n^2 * (7*(n:ℝ)+5) / (16*((n:ℝ)+1)^2*((n:ℝ)+2)) := by
    dsimp only [upper,lower,D]
    rw [B_succ]
    push_cast
    have a : 2*(n:ℝ)+2 ≠ 0 := by positivity
    have b : (n:ℝ)+1 ≠ 0 := by positivity
    have c : (n:ℝ)+2 ≠ 0 := by positivity
    have d : (n:ℝ)+1+1 ≠ 0 := by positivity
    field_simp [a,b,c,d]
    ring
  exact sub_nonneg.mp (h.symm ▸ (by positivity))

private lemma lower_tendsto : Tendsto lower atTop (𝓝 1) := by
  convert D_tendsto.add ((B_sq_tendsto.const_mul Real.pi).div_const 4) using 1
  norm_num

private lemma upper_tendsto : Tendsto upper atTop (𝓝 1) := by
  have z := (B_sq_tendsto.const_mul Real.pi).div_atTop
    (((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1:ℝ)))).const_mul_atTop
      (show (0:ℝ)<4 by norm_num))
  convert lower_tendsto.add z using 1
  norm_num

/-- A uniform finite-level envelope for the quarter correction. -/
theorem quarter_bounds (n : ℕ) : D n / 4 ≤ n*(1-D n) ∧
    (n:ℝ)*(1-D n) ≤ D n / 4 + D n/(4*((n:ℝ)+1)) := by
  have h := mul_le_mul_of_nonneg_left (lower_strictMono.monotone.ge_of_tendsto lower_tendsto n)
    (show 0 ≤ (n:ℝ) by positivity)
  have k := mul_le_mul_of_nonneg_left (upper_antitone.le_of_tendsto upper_tendsto n)
    (show 0 ≤ (n:ℝ) by positivity)
  dsimp only [lower,upper,D] at h k ⊢
  constructor
  · linarith
  · convert (show (n:ℝ)*(1-Real.pi*n*B n^2) ≤
        n*(Real.pi*B n^2/4) + n*(Real.pi*B n^2/(4*((n:ℝ)+1))) by linarith) using 1
    ring

/-- The displacement on the reference grid of radii 2πn increases strictly. -/
theorem grid_displacement_strictMono : StrictMono (fun n : ℕ => (n:ℝ)*(1-D n)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h : lower n < 1 :=
    (lower_strictMono (Nat.lt_succ_self n)).trans_le
      (lower_strictMono.monotone.ge_of_tendsto lower_tendsto (n+1))
  have step : ((n:ℝ)+1)*(1-D (n+1)) - n*(1-D n) = 1-lower n := by
    simp only [lower, D, B_succ, Nat.cast_succ]
    field_simp [show 2*(n:ℝ)+2 ≠ 0 by positivity]
    ring
  simp only [Nat.cast_succ]
  linarith

/-- Every positive grid level lies above the lower zero of the Hurwitz value at −1. -/
theorem grid_displacement_gt_hurwitz {n : ℕ} (hn : 1 ≤ n) :
    (1 - 1 / Real.sqrt 3) / 2 < (n:ℝ)*(1-D n) := by
  apply lt_of_lt_of_le _ (grid_displacement_strictMono.monotone hn)
  have hs : Real.sqrt 3 < 40 / 23 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hi : (23:ℝ)/40 < 1 / Real.sqrt 3 := by
    apply (lt_div_iff₀ (by positivity)).2
    linarith
  have hb : B 1 = 1/2 := by
    norm_num [B, Nat.centralBinom, Nat.choose]
  simp only [Nat.cast_one, one_mul, D, hb]
  linarith [Real.pi_lt_d2]

/-- The first binomial correction from the Barnes–Dottie normalization, at every scale. -/
theorem quarter_limit : Tendsto (fun n : ℕ => n*(1-D n)) atTop (𝓝 (1/4 : ℝ)) := by
  have z := D_tendsto.div_atTop
    (((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1:ℝ)))).const_mul_atTop
      (show (0:ℝ)<4 by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (D_tendsto.div_const 4) _
    (fun n => (quarter_bounds n).1) (fun n => (quarter_bounds n).2)
  simpa using (D_tendsto.div_const 4).add z

end
end SuperZeta.Barnes
