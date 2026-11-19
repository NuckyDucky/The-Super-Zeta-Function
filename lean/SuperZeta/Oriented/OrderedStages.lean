import SuperZeta.SpireDisk
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Actual exponents invert the ordered stages. On the centerline, the native
return derivative can be read from those exponents, and a signed nonreal
characteristic root decodes the phase of that derivative. -/

noncomputable section

namespace DottieOriented

open Complex SuperZeta.Reciprocal
open scoped ComplexConjugate Topology NNReal

/-- The ordered phase packet `(U,V)` recovers the predecessor `(P,Q)`. -/
def recoverInput (L : ℂ) (uv : ℂ × ℂ) : ℂ × ℂ := (-uv.2 / L, uv.1 / L)

theorem recoverInput_lifts {L : ℂ} (hL : L ≠ 0) (p : ℂ × ℂ) :
    recoverInput L (lifts L p) = p := by
  rcases p with ⟨p, q⟩
  apply Prod.ext <;> simp [recoverInput, lifts, hL, mul_comm]

theorem lifts_recoverInput {L : ℂ} (hL : L ≠ 0) (uv : ℂ × ℂ) :
    lifts L (recoverInput L uv) = uv := by
  apply Prod.ext
  · change L * (uv.1 / L) = uv.1
    rw [mul_comm, div_mul_cancel₀ _ hL]
  · change -L * (-uv.2 / L) = uv.2
    rw [neg_div, neg_mul_neg, mul_comm, div_mul_cancel₀ _ hL]

theorem forward_of_lifts (L : ℂ) (p : ℂ × ℂ) :
    step L p = (exp (lifts L p).1, exp (lifts L p).2) := rfl

/-- For the positive-rooted scalar return, undo the outer stage first.
The two actual exponents are kept in the order in which they were produced. -/
theorem rewind_scalar_stages {L : ℂ} (hL : L ≠ 0) (p : ℂ) :
    let innerLift := -L * p
    let outerLift := L * exp innerLift
    outerLift / L = exp innerLift ∧ innerLift / (-L) = p ∧
      exp outerLift = scalarReturn L p := by
  dsimp only
  exact ⟨by rw [mul_comm, mul_div_cancel_right₀ _ hL],
    by rw [mul_comm, mul_div_cancel_right₀ _ (neg_ne_zero.mpr hL)], rfl⟩

/-- A sheet is recorded relative to the principal logarithm of the output. -/
def sheetLog (w : ℂ) (k : ℤ) : ℂ := log w + (k : ℂ) * (2 * Real.pi * I)

theorem sheetLog_exp {w : ℂ} (hw : w ≠ 0) (k : ℤ) : exp (sheetLog w k) = w := by
  apply Eq.trans (exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩) (exp_log hw)

theorem sheetLog_injective (w : ℂ) : Function.Injective (sheetLog w) := by
  intro k j h
  have hcast := mul_right_cancel₀ two_pi_I_ne_zero (add_left_cancel h)
  exact_mod_cast hcast

/-- Exactly one sheet label specifies a given actual exponent. -/
theorem existsUnique_sheetLog (z : ℂ) : ∃! k : ℤ, sheetLog (exp z) k = z := by
  have he : exp z = exp (log (exp z)) := (exp_log (exp_ne_zero z)).symm
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.mp he
  exact ⟨k, hk.symm, fun j hj => sheetLog_injective _ (hj.trans hk)⟩

/-- Every choice of the two stage sheets unpacks to a valid predecessor. -/
theorem step_recoverInput_sheets {L p q : ℂ}
    (hL : L ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (k j : ℤ) :
    step L (recoverInput L (sheetLog p k, sheetLog q j)) = (p, q) := by
  rw [forward_of_lifts, lifts_recoverInput hL]
  exact Prod.ext (sheetLog_exp hp k) (sheetLog_exp hq j)

/-- From a true predecessor both sheet labels are uniquely determined. -/
theorem unique_step_sheets (L : ℂ) (p : ℂ × ℂ) :
    ∃! kj : ℤ × ℤ,
      (sheetLog (step L p).1 kj.1, sheetLog (step L p).2 kj.2) = lifts L p := by
  obtain ⟨k, hk, huk⟩ := existsUnique_sheetLog (lifts L p).1
  obtain ⟨j, hj, huj⟩ := existsUnique_sheetLog (lifts L p).2
  rw [forward_of_lifts]
  refine ⟨(k, j), Prod.ext hk hj, ?_⟩
  intro kj h
  exact Prod.ext (huk _ (congrArg Prod.fst h)) (huj _ (congrArg Prod.snd h))

/-- The exponent packets in reverse chronological order. -/
def orbitLifts (L : ℂ) (start : ℂ × ℂ) : ℕ → List (ℂ × ℂ)
  | 0 => []
  | n + 1 => lifts L ((step L)^[n] start) :: orbitLifts L start n

/-- Keep the endpoint and read each actual exponent packet backwards. -/
def reverseHistory (L : ℂ) : (ℂ × ℂ) → List (ℂ × ℂ) → List (ℂ × ℂ)
  | current, [] => [current]
  | current, uv :: rest => current :: reverseHistory L (recoverInput L uv) rest

/-- The true history, newest point first. -/
def orbitHistory (L : ℂ) (start : ℂ × ℂ) : ℕ → List (ℂ × ℂ)
  | 0 => [start]
  | n + 1 => (step L)^[n + 1] start :: orbitHistory L start n

theorem reverseHistory_orbit {L : ℂ} (hL : L ≠ 0) (start : ℂ × ℂ) (n : ℕ) :
    reverseHistory L ((step L)^[n] start) (orbitLifts L start n) = orbitHistory L start n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbitLifts, reverseHistory, recoverInput_lifts hL, orbitHistory, ih]

open SuperZeta.SpireDisk (alternating run run_alternating stage)

/-- Actual arguments used by a list of scalar exponential stages, in forward order. -/
def exponentTrace : List ℂ → ℂ → List ℂ
  | [], _ => []
  | a :: rates, z => (a * z) :: exponentTrace rates (stage a z)

theorem run_derivative_from_lifts (rates : List ℂ) (z : ℂ) :
    HasDerivAt (run rates) (rates.prod * exp (exponentTrace rates z).sum) z := by
  induction rates generalizing z with
  | nil => simpa [run, exponentTrace] using hasDerivAt_id z
  | cons a rates ih =>
    have ha : HasDerivAt (stage a) (a * stage a z) z := by
      simpa [stage, mul_comm] using ((hasDerivAt_id z).const_mul a).cexp
    have h := (ih (stage a z)).comp z ha
    convert h using 1
    simp only [List.prod_cons, exponentTrace, List.sum_cons, exp_add, stage]
    ring

private theorem alternating_prod (L : ℂ) (n : ℕ) :
    (alternating L n).prod = (-(L ^ 2)) ^ n := by
  induction n with
  | zero => simp [alternating]
  | succ n ih =>
    simp only [alternating, List.prod_cons, ih, pow_succ]
    ring

/-- One full positive-rooted scalar lap of the calibrated centerline cap. -/
def capReturn (y : ℝ) : ℂ → ℂ := (scalarReturn (I * (y : ℂ)))^[320]

theorem capReturn_derivative_from_lifts (y : ℝ) (p : ℂ) :
    deriv (capReturn y) p =
      (y : ℂ)^640 * exp (exponentTrace (alternating (I * (y : ℂ)) 320) p).sum := by
  have hr : run (alternating (I * (y : ℂ)) 320) = capReturn y :=
    funext (run_alternating _ _)
  rw [← hr, (run_derivative_from_lifts _ _).deriv, alternating_prod]
  rw [mul_pow, I_sq, neg_mul, neg_neg, one_mul, ← pow_mul]

theorem capReturn_derivative_ne_zero {y : ℝ} (hy : y ≠ 0) (p : ℂ) :
    deriv (capReturn y) p ≠ 0 := by
  rw [capReturn_derivative_from_lifts]
  exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hy)) (exp_ne_zero _)

/-- The complete return angle in radians, in the principal argument interval. -/
def nativeAngle (y : ℝ) (p : ℂ) : ℝ := arg (deriv (capReturn y) p)

def nativeMark (y : ℝ) (p : ℂ) : ℂ := exp ((nativeAngle y p : ℂ) * I)

theorem nativeMark_eq_unit {y : ℝ} (hy : y ≠ 0) (p : ℂ) :
    nativeMark y p = deriv (capReturn y) p / (‖deriv (capReturn y) p‖ : ℂ) := by
  have hμ := capReturn_derivative_ne_zero hy p
  apply (eq_div_iff (by exact_mod_cast norm_ne_zero_iff.mpr hμ)).2
  rw [mul_comm]
  exact norm_mul_exp_arg_mul_I _

/-- The positive real rate product contributes zero angle. The complete native
mark is the exponential of the unwrapped sum of stage arguments. -/
theorem nativeMark_from_lifts {y : ℝ} (hy : y ≠ 0) (p : ℂ) :
    nativeMark y p = exp
      (((exponentTrace (alternating (I * (y : ℂ)) 320) p).sum.im : ℂ) * I) := by
  let W := (exponentTrace (alternating (I * (y : ℂ)) 320) p).sum
  have hypos : 0 < y ^ 640 := by
    rw [show (640 : ℕ) = 2 * 320 by decide, pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hy) _
  have hpos := mul_pos hypos (Real.exp_pos W.re)
  have hfactor : deriv (capReturn y) p = (↑(y ^ 640 * Real.exp W.re) : ℂ) * exp ((W.im : ℂ) * I) := by
    rw [capReturn_derivative_from_lifts]
    change (y : ℂ) ^ 640 * exp W = _
    rw [ofReal_mul, ofReal_pow, ofReal_exp, mul_assoc, ← exp_add, re_add_im]
  have hn : ‖deriv (capReturn y) p‖ = y ^ 640 * Real.exp W.re := by
    rw [hfactor, norm_mul, norm_real, Real.norm_of_nonneg hpos.le, norm_exp]
    simp
  have hn0 : (↑(y ^ 640 * Real.exp W.re) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [nativeMark_eq_unit hy, hn, hfactor, mul_comm, mul_div_cancel_right₀ _ hn0]

/-- The root is selected by the marked seed on the calibrated branch. -/
def capRoot (y : ℝ) : ℂ :=
  lim (Filter.map (fun n : ℕ => (capReturn y)^[n] 1) Filter.atTop)

set_option maxRecDepth 4096 in
/-- Trap estimates give one cap root in the calibrated set and convergence
of the marked seed `1` under complete scalar laps. -/
theorem cap_root_of_contraction {y : ℝ} {D : Set ℂ} {K : ℝ≥0}
    (hclosed : IsClosed D) (hcap : (1 : ℂ) ∈ D)
    (hmap : Set.MapsTo (capReturn y) D D)
    (hcontract : ContractingWith K (hmap.restrict (capReturn y) D D)) :
    capRoot y ∈ D ∧ capReturn y (capRoot y) = capRoot y ∧
      Filter.Tendsto (fun n : ℕ => (capReturn y)^[n] 1) Filter.atTop (𝓝 (capRoot y)) ∧
      ∀ q ∈ D, capReturn y q = q → q = capRoot y := by
  obtain ⟨p, hp, hfixed, hlim, _⟩ := hcontract.exists_fixedPoint' hclosed.isComplete
    hmap hcap (edist_ne_top _ _)
  have hroot : capRoot y = p := lim_eq hlim
  rw [hroot]
  refine ⟨hp, hfixed, hlim, ?_⟩
  intro q hq hqfixed
  have hps : Function.IsFixedPt (hmap.restrict (capReturn y) D D) (⟨p, hp⟩ : D) := by
    apply Subtype.ext
    change capReturn y p = p
    exact hfixed
  have hqs : Function.IsFixedPt (hmap.restrict (capReturn y) D D) (⟨q, hq⟩ : D) := by
    apply Subtype.ext
    change capReturn y q = q
    exact hqfixed
  exact congrArg Subtype.val (hcontract.fixedPoint_unique' hqs hps)

theorem centerline_lifts_conj (y : ℝ) (p : ℂ) :
    (lifts (I * (y : ℂ)) (p, conj p)).2 = conj (lifts (I * (y : ℂ)) (p, conj p)).1 := by
  simp [lifts]

theorem centerline_even_stages (y : ℝ) (p : ℂ) (n : ℕ) :
    (step (I * (y : ℂ)))^[2 * n] (p, conj p) =
      ((scalarReturn (I * (y : ℂ)))^[n] p, conj ((scalarReturn (I * (y : ℂ)))^[n] p)) := by
  let embed : ℂ → ℂ × ℂ := fun z => (z, conj z)
  let g := scalarReturn (I * (y : ℂ))
  let s := step (I * (y : ℂ))
  have hstep : Function.Semiconj embed g (s^[2]) := by
    intro z
    change (g z, conj (g z)) = s (s (z, conj z))
    dsimp only [s, g]
    rw [centerline_step, centerline_step, halfStep_squared]
  rw [Function.iterate_mul]
  exact (hstep.iterate_right n p).symm

/-- A scalar cap root produces the actual ordered return rooted at `(p,conj p)`. -/
theorem cap_root_ordered_return {y : ℝ} {p : ℂ} (hp : capReturn y p = p) :
    Function.IsPeriodicPt (step (I * (y : ℂ))) 640 (p, conj p) := by
  change (step (I * (y : ℂ)))^[640] (p, conj p) = (p, conj p)
  rw [show (640 : ℕ) = 2 * 320 by decide, centerline_even_stages]
  change (capReturn y p, conj (capReturn y p)) = (p, conj p)
  rw [hp]

/-- The scalar period certificate determines the primitive ordered clock. -/
theorem cap_root_ordered_period {y : ℝ} {p : ℂ}
    (hp : Function.minimalPeriod (scalarReturn (I * (y : ℂ))) p = 320) :
    Function.minimalPeriod (step (I * (y : ℂ))) (p, conj p) = 640 := by
  let n := Function.minimalPeriod (step (I * (y : ℂ))) (p, conj p)
  have he : 320 = n / n.gcd 2 := hp.symm.trans (centerline_scalar_period y p)
  have hm : 320 * n.gcd 2 = n := by
    rw [he, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  change n = 640
  rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right n 2) with h | h
  · rw [h, mul_one] at hm
    rw [← hm] at h
    have hfalse : Nat.gcd 320 2 ≠ 1 := by decide
    exact (hfalse h).elim
  · rw [← hm, h]

/-- A signed nonreal characteristic root retains the stage mark. -/
def decodeMark (σ : ℝ) (u : ℂ) : ℂ :=
  (σ : ℂ) * exp (-(u.re : ℂ) * I) *
    ((u.re / Real.cosh u.im : ℝ) - (u.im / Real.sinh u.im : ℝ) * I)

/-- The signed equation and the decoded-mark equality are equivalent on the
nonreal root domain. The angle is determined modulo the exponential period. -/
theorem signed_root_iff_decodeMark {σ φ : ℝ} {u : ℂ}
    (hσ : σ = 1 ∨ σ = -1) (hu : u.im ≠ 0) :
    u = (σ : ℂ) * cos (u - (φ : ℂ)) ↔ decodeMark σ u = exp (-(φ : ℂ) * I) := by
  let t : ℝ := u.re - φ
  let C : ℝ := Real.cosh u.im
  let S : ℝ := Real.sinh u.im
  let w : ℂ := (u.re / C : ℝ) - (u.im / S : ℝ) * I
  have hC : C ≠ 0 := (Real.cosh_pos _).ne'
  have hS : S ≠ 0 := Real.sinh_ne_zero.mpr hu
  have hσ0 : (σ : ℂ) ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ2 : (σ : ℂ) * (σ : ℂ) = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hcos : cos (u - (φ : ℂ)) =
      (Real.cos t * C : ℝ) - (Real.sin t * S : ℝ) * I := by
    rw [Complex.cos_eq]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero, ← ofReal_cos, ← ofReal_cosh,
      ← ofReal_sin, ← ofReal_sinh, ← ofReal_mul]
    rfl
  have hexp : exp ((t : ℂ) * I) = (Real.cos t : ℂ) + (Real.sin t : ℂ) * I := by
    rw [exp_mul_I, ofReal_cos, ofReal_sin]
  have hnormalize : u = (σ : ℂ) * cos (u - (φ : ℂ)) ↔ w = (σ : ℂ) * exp ((t : ℂ) * I) := by
    rw [hcos, hexp, Complex.ext_iff, Complex.ext_iff]
    simp only [w, mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, add_re, add_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, zero_sub, mul_one, add_zero, zero_add, neg_zero]
    constructor
    · rintro ⟨hr, hi⟩
      exact ⟨(div_eq_iff hC).2 (by rw [hr]; ring),
        (neg_eq_iff_eq_neg.mpr ((div_eq_iff hS).2 (by rw [hi]; ring)))⟩
    · rintro ⟨hr, hi⟩
      exact ⟨by rw [(div_eq_iff hC).1 hr]; ring,
        by rw [(div_eq_iff hS).1 (neg_eq_iff_eq_neg.mp hi)]; ring⟩
  have hrotate : (σ : ℂ) * exp (-(u.re : ℂ) * I) * ((σ : ℂ) * exp ((t : ℂ) * I)) =
      exp (-(φ : ℂ) * I) := by
    calc
      _ = ((σ : ℂ) * (σ : ℂ)) * (exp (-(u.re : ℂ) * I) * exp ((t : ℂ) * I)) := by ring
      _ = exp (-(φ : ℂ) * I) := by rw [hσ2, one_mul, ← exp_add]; congr 1; dsimp [t]; push_cast; ring
  rw [hnormalize]
  change w = (σ : ℂ) * exp ((t : ℂ) * I) ↔
    (σ : ℂ) * exp (-(u.re : ℂ) * I) * w = exp (-(φ : ℂ) * I)
  rw [← hrotate]
  exact (mul_right_inj' (mul_ne_zero hσ0 (exp_ne_zero _))).symm

theorem decode_native_angle {σ : ℝ} {u p : ℂ} {y : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hu : u.im ≠ 0)
    (hroot : u = (σ : ℂ) * cos (u + (nativeAngle y p : ℂ))) :
    (decodeMark σ u).arg = nativeAngle y p := by
  have h := (signed_root_iff_decodeMark (φ := -nativeAngle y p) hσ hu).mp
    (by simpa [sub_neg_eq_add] using hroot)
  have hprincipal : nativeAngle y p ∈ Set.Ioc (-Real.pi) Real.pi := arg_mem_Ioc _
  rw [h, ofReal_neg, neg_neg, exp_mul_I]
  exact arg_cos_add_sin_mul_I hprincipal

end DottieOriented
