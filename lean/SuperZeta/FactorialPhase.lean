import SuperZeta.StirlingCorrection
import Mathlib.Data.Complex.Exponential

/-! The exact adjacent factorial phase, including the first Dottie half-turn. -/
namespace SuperZeta.StirlingCorrection
open Real
noncomputable section

def increment (n : ℕ) : ℝ := 1/(4*(n:ℝ)*(n+1))

theorem D_ratio {n : ℕ} (hn : 0<n) :
    Barnes.D (n+1) / Barnes.D n = 1+increment n := by
  have hp : (n:ℝ) ≠ 0 := by positivity
  unfold increment
  field_simp [(D_pos hn).ne', hp, show (n:ℝ)+1 ≠ 0 by positivity]
  linear_combination Barnes.D_increment n

theorem log_D_increment {n : ℕ} (hn : 0<n) :
    log (Barnes.D (n+1)) - log (Barnes.D n) = log (1+increment n) := by
  rw [← log_div (D_pos (Nat.succ_pos n)).ne' (D_pos hn).ne', D_ratio hn]

/-- The factorial increment adds to the exact log-radius increment. -/
theorem log_C_increment {R : ℕ → ℝ} {n : ℕ} (hn : 0<n)
    (hr : 0<R n) (hr' : 0<R (n+1)) :
    log (C R (n+1)) - log (C R n) = log (1+increment n) +
      (log (R (n+1)/(2*π*((n:ℝ)+1))) - log (R n/(2*π*n))) := by
  have hnext : 0<n+1 := Nat.succ_pos n
  rw [C_eq R hnext, C_eq R hn, log_mul (by positivity) (D_pos hnext).ne',
    log_mul (by positivity) (D_pos hn).ne', Nat.cast_succ]
  linear_combination log_D_increment hn

/-- The positive-real complex power attached to a spectral factor. -/
def phaseFactor (w : ℂ) (x : ℝ) : ℂ := Complex.exp (-(w/2)*(log x:ℂ))

theorem phaseFactor_eq_cpow {w : ℂ} {x : ℝ} (hx : 0<x) :
    phaseFactor w x = (x:ℂ)^(-(w/2)) := by
  rw [phaseFactor, Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le, mul_comm]

private theorem exp_unit (z : ℂ) :
    Complex.exp z / (‖Complex.exp z‖:ℂ) = Complex.exp ((z.im:ℂ)*Complex.I) := by
  rw [Complex.norm_exp, Complex.ofReal_exp,
    div_eq_iff (Complex.exp_ne_zero _), ← Complex.exp_add]
  congr 1
  rw [add_comm, Complex.re_add_im]

/-- The normalized quotient has exactly this signed phase modulo 2π. -/
theorem phaseFactor_quotient (w : ℂ) (x y : ℝ) :
    (phaseFactor w y/phaseFactor w x) / (‖phaseFactor w y/phaseFactor w x‖:ℂ) =
      Complex.exp ((↑(-w.im/2*(log y-log x)):ℂ)*Complex.I) := by
  rw [phaseFactor, phaseFactor, ← Complex.exp_sub, exp_unit]
  congr 2
  push_cast
  have e : (-(w/2)*(log y:ℂ) - -(w/2)*(log x:ℂ)) =
      (-w)*((log y-log x:ℝ)/2:ℝ) := by push_cast; ring
  rw [e]
  simp [Complex.mul_im]
  ring

/-- The exact squared horizontal-to-vertical ratio of the archived witnesses. -/
def witnessRatio : ℝ := (0.00000004749479070945369 / 0.509892982511772)^2

def heightDelta : ℝ := 160 * log (1+witnessRatio)

def dottieHeight : ℝ := 2*π/heightDelta

theorem heightDelta_pos : 0 < heightDelta := by
  have h : 1 < 1+witnessRatio := by norm_num [witnessRatio]
  unfold heightDelta
  exact mul_pos (by norm_num) (log_pos h)

private theorem log_one_add_bounds {v : ℝ} (hv : 0≤v) :
    v/(1+v) ≤ log (1+v) ∧ log (1+v) ≤ v := by
  have hh : 0<1+v := by linarith
  have hg : v/(1+v) = 1-(1+v)⁻¹ := by field_simp [hh.ne']
  rw [hg]
  exact ⟨one_sub_inv_le_log_of_pos hh, by simpa using log_le_sub_one_of_pos hh⟩

private theorem half_turn {a b : ℝ} (below : heightDelta < a) (above : b < heightDelta) :
    π < dottieHeight/2*a ∧ dottieHeight/2*b < π := by
  have h : dottieHeight/2=π/heightDelta := by unfold dottieHeight; ring
  rw [h]
  have p : 0 < π/heightDelta := div_pos pi_pos heightDelta_pos
  have q : π/heightDelta*heightDelta=π := div_mul_cancel₀ _ heightDelta_pos.ne'
  exact ⟨lt_of_eq_of_lt q.symm (mul_lt_mul_of_pos_left below p),
    lt_of_lt_of_eq (mul_lt_mul_of_pos_left above p) q⟩

/-- The first factorial half-turn comparison is reduced to rational inequalities.
It uses the exact terminating decimals of the two reflected parameters. -/
theorem dottie_factorial_bracket :
    π < dottieHeight/2*log (1+increment 424367) ∧
    dottieHeight/2*log (1+increment 424368) < π := by
  have q0 : 0≤witnessRatio := sq_nonneg _
  have hlow (n : ℕ) : increment n/(1+increment n) ≤ log (1+increment n) :=
    (log_one_add_bounds (by unfold increment; positivity)).1
  have hupp (n : ℕ) : log (1+increment n) ≤ increment n :=
    (log_one_add_bounds (by unfold increment; positivity)).2
  have below : heightDelta < log (1+increment 424367) := by
    calc
      heightDelta ≤ 160*witnessRatio :=
        mul_le_mul_of_nonneg_left (log_one_add_bounds q0).2 (by norm_num)
      _ < increment 424367/(1+increment 424367) := by norm_num [witnessRatio,increment]
      _ ≤ _ := hlow _
  have above : log (1+increment 424368) < heightDelta := by
    calc
      _ ≤ increment 424368 := hupp _
      _ < 160*(witnessRatio/(1+witnessRatio)) := by norm_num [witnessRatio,increment]
      _ ≤ heightDelta := mul_le_mul_of_nonneg_left (log_one_add_bounds q0).1 (by norm_num)
  exact half_turn below above

/-- Logarithmic increment of the radius after division by the \(2πn\) grid. -/
def radialIncrement (R : ℕ → ℝ) (n : ℕ) : ℝ :=
  log (R (n+1)/(2*π*((n:ℝ)+1))) - log (R n/(2*π*n))

/-- The full half-turn bracket follows from two rational enclosures for the
radial increments. The archived interval calculation supplies the enclosures. -/
theorem dottie_quartet_bracket {R : ℕ → ℝ} (hr : ∀ n, 0<R n)
    (left : (-2510834912:ℝ)/10^25 ≤ radialIncrement R 424329)
    (right : radialIncrement R 424330 ≤ (-2510818022:ℝ)/10^25) :
    π < dottieHeight/2*(log (C R 424330)-log (C R 424329)) ∧
    dottieHeight/2*(log (C R 424331)-log (C R 424330)) < π := by
  rw [log_C_increment (n:=424329) (by norm_num) (hr _) (hr _),
    log_C_increment (n:=424330) (by norm_num) (hr _) (hr _)]
  have q0 : 0≤witnessRatio := sq_nonneg _
  apply half_turn
  · calc
      heightDelta ≤ 160*witnessRatio :=
        mul_le_mul_of_nonneg_left (log_one_add_bounds q0).2 (by norm_num)
      _ < increment 424329/(1+increment 424329) + (-2510834912:ℝ)/10^25 := by
        norm_num [witnessRatio, increment]
      _ ≤ _ := add_le_add (log_one_add_bounds (by unfold increment; positivity)).1 left
  · calc
      _ ≤ increment 424330 + (-2510818022:ℝ)/10^25 :=
        add_le_add (log_one_add_bounds (by unfold increment; positivity)).2 right
      _ < 160*(witnessRatio/(1+witnessRatio)) := by norm_num [witnessRatio, increment]
      _ ≤ heightDelta := mul_le_mul_of_nonneg_left (log_one_add_bounds q0).1 (by norm_num)

end
end SuperZeta.StirlingCorrection
