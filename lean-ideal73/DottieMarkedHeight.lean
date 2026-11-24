import DottieHeightTransport
import SuperZeta.Reciprocal
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! The height carried by the marked reciprocal cycle. The two scalar
returns keep their own initial phases and tangent logarithms. -/

namespace SuperZeta.StirlingCorrection

open Complex Function Set SuperZeta.Reciprocal
open scoped Topology
noncomputable section

/-- The actual lifted output of an exponential arrow has constant derivative. -/
theorem lifted_arrow_hasDerivAt (r z : ℂ) :
    HasDerivAt (fun a : ℂ => r*a) r z := by
  simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul r

theorem marked_arrow_log_increment (p : ℕ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Real.log (‖(⟨x,y⟩ : ℂ)‖^p / y^p) = (p:ℝ)*dottieLogModulus x y := by
  rw [← div_pow, Real.log_pow, ← dottie_log_modulus_eq_log_ratio x hy]

theorem height_from_marked_arrow (p k : ℕ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    dottieModulusHeight p k (dottieLogModulus x y) =
      2*Real.pi*(k:ℝ) / Real.log (‖(⟨x,y⟩ : ℂ)‖^p / y^p) := by
  rw [marked_arrow_log_increment p x hy, dottieModulusHeight, div_div]

/-- Two primitive 320-returns give one primitive 640-clock for the original
ordered map, even away from the conjugate diagonal. -/
theorem ordered_clock_640 {L P Q : ℂ}
    (hP : minimalPeriod (scalarReturn L) P = 320)
    (hQ : minimalPeriod (scalarReturn (-L)) Q = 320) :
    minimalPeriod (step L) (P,Q) = 640 := by
  have htwo : (step L)^[2] = Prod.map (scalarReturn L) (scalarReturn (-L)) := by
    funext z
    simpa [Function.iterate_succ_apply', Prod.map] using step_twice L z
  have hclock : minimalPeriod ((step L)^[2]) (P,Q) = 320 := by
    rw [htwo, minimalPeriod_prodMap, hP, hQ, Nat.lcm_self]
  let m := minimalPeriod (step L) (P,Q)
  have hdiv : m / Nat.gcd m 2 = 320 := by
    rw [minimalPeriod_iterate_eq_div_gcd (by decide : 2 ≠ 0)] at hclock
    exact hclock
  have hmul := Nat.div_mul_cancel (Nat.gcd_dvd_left m 2)
  rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right m 2) with h | h
  · rw [h, Nat.div_one] at hdiv
    rw [hdiv] at h
    norm_num at h
  · rw [hdiv, h] at hmul
    exact hmul.symm

theorem scalar_period_320_of_divisor_exclusions {f : ℂ → ℂ} {z : ℂ}
    (h320 : IsPeriodicPt f 320 z) (h160 : ¬ IsPeriodicPt f 160 z)
    (h64 : ¬ IsPeriodicPt f 64 z) : minimalPeriod f z = 320 := by
  have hdvd := h320.minimalPeriod_dvd
  have hle := Nat.le_of_dvd (by decide : 0 < 320) hdvd
  have hnum : ∀ n : Fin 321, n.val ∣ 320 → ¬n.val ∣ 160 →
      ¬n.val ∣ 64 → n.val = 320 := by decide +kernel
  exact hnum ⟨minimalPeriod f z, Nat.lt_succ_of_le hle⟩ hdvd
    (fun h => h160 (isPeriodicPt_iff_minimalPeriod_dvd.mpr h))
    (fun h => h64 (isPeriodicPt_iff_minimalPeriod_dvd.mpr h))

/-- The two summands after the constant logs are the lifted outputs of
the negative arrow and then the positive arrow. -/
def rootedStepTangentLog (L z : ℂ) : ℂ :=
  log L + log (-L) + (-L*z + L*exp (-L*z))

def rootedReturnTangentLog (L z : ℂ) : ℕ → ℂ
  | 0 => 0
  | n+1 => rootedStepTangentLog L ((scalarReturn L)^[n] z) + rootedReturnTangentLog L z n

theorem exp_rootedStepTangentLog {L : ℂ} (hL : L ≠ 0) (z : ℂ) :
    exp (rootedStepTangentLog L z) = -L^2 * exp (-L*z) * scalarReturn L z := by
  simp only [rootedStepTangentLog, scalarReturn, Complex.exp_add, exp_log hL,
    exp_log (neg_ne_zero.mpr hL)]
  ring

theorem rootedReturn_hasDerivAt {L : ℂ} (hL : L ≠ 0) (z : ℂ) (p : ℕ) :
    HasDerivAt (scalarReturn L)^[p] (exp (rootedReturnTangentLog L z p)) z := by
  induction p with
  | zero => simpa [rootedReturnTangentLog] using hasDerivAt_id z
  | succ n ih =>
    rw [Function.iterate_succ', rootedReturnTangentLog, Complex.exp_add,
      exp_rootedStepTangentLog hL]
    exact (scalar_hasDerivAt L ((scalarReturn L)^[n] z)).comp z ih

def HasRootedWinding (L z : ℂ) (p : ℕ) (k : ℤ) : Prop :=
  (rootedReturnTangentLog L z p).im - (deriv (scalarReturn L)^[p] z).arg =
    2*Real.pi*(k:ℝ)

/-- A single enclosure for the lifted imaginary part certifies the integer
winding of the actual derivative. -/
theorem rootedWinding_of_im_bounds {L : ℂ} (hL : L ≠ 0) (z : ℂ) (p : ℕ) (k : ℤ)
    (hlo : -Real.pi < (rootedReturnTangentLog L z p).im - 2*Real.pi*(k:ℝ))
    (hhi : (rootedReturnTangentLog L z p).im - 2*Real.pi*(k:ℝ) ≤ Real.pi) :
    HasRootedWinding L z p k := by
  let a := rootedReturnTangentLog L z p
  let b := a - (k:ℂ)*(2*Real.pi*I)
  have him : b.im = a.im - 2*Real.pi*(k:ℝ) := by
    simp [b, Complex.sub_im, Complex.mul_im, Complex.mul_re]
    ring
  have hexp : exp b = exp a :=
    exp_eq_exp_iff_exists_int.mpr ⟨-k, by push_cast; dsimp [b]; ring⟩
  have hlog := log_exp (x := b) (by rw [him]; exact hlo) (by rw [him]; exact hhi)
  rw [hexp, ← (rootedReturn_hasDerivAt hL z p).deriv] at hlog
  have ha := congrArg Complex.im hlog
  rw [Complex.log_im] at ha
  unfold HasRootedWinding
  rw [ha, him]
  dsimp [a]
  ring

/-- The inverse selects the unique positive flank for each height in the
proved band. The same complex input lies in its measuring disk. -/
theorem dottie_height_covers_witness_band {w : ℂ}
    (hre : w.re ∈ Icc (1/2 + 1/2048) (1/2 + 63/2048))
    (him : w.im + 1/512 ∈ Icc (dottieHeight - 10^8) (dottieHeight + 10^8)) :
    ∃! x : ℝ,
      0 < x ∧
      x ∈ Icc (archivedDottieFlank - dottieFlankWidth)
        (archivedDottieFlank + dottieFlankWidth) ∧
      dottieHeightAtFlank x = w.im + 1/512 ∧
      w ∈ Metric.closedBall (QuarticModel.archivedRightCenter (dottieHeightAtFlank x))
        (31/2048) := by
  let T := w.im + 1/512
  let x := dottieFlankAtHeight archivedDottieMidIm T
  have hT : 0 < T := by
    change 0 < w.im + 1/512
    linarith only [him.1, dottieHeight_enclosure.1]
  have hy : 0 < archivedDottieMidIm := by norm_num
  have hx := dottieFlankAtHeight_pos hy hT
  have hband := dottieFlankAtHeight_witness_band him
  have hheight : dottieHeightAtFlank x = T := dottieFlankHeight_inverse hy hT
  refine ⟨x, ⟨hx, hband, hheight, ?_⟩, ?_⟩
  · rw [hheight, Metric.mem_closedBall, dist_eq_norm]
    have hd : w - QuarticModel.archivedRightCenter T = ((w.re - 33/64 : ℝ):ℂ) := by
      apply Complex.ext
      · rfl
      · change w.im - (w.im + 1/512 - 1/512) = 0
        ring
    rw [hd, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hre.1], by linarith [hre.2]⟩
  · intro z hz
    exact (dottieFlankHeight_strictAntiOn hy).injOn hz.1 hx (hz.2.2.1.trans hheight.symm)

/-- A scalar phase selected by the launch at one. The return clock starts
after the cap orbit enters its trapping disk. -/
def ScalarCapCaptured (L z : ℂ) (period : ℕ) : Prop :=
  ∃ N : ℕ, Filter.Tendsto
    (fun k : ℕ => (((scalarReturn L)^[period])^[k]) (((scalarReturn L)^[N]) 1))
    Filter.atTop (𝓝 z)

structure MarkedDottiePair (L P Q : ℂ) (winding : ℤ) : Prop where
  periodP : minimalPeriod (scalarReturn L) P = 320
  periodQ : minimalPeriod (scalarReturn (-L)) Q = 320
  captureP : ScalarCapCaptured L P 320
  captureQ : ScalarCapCaptured (-L) Q 320
  windingP : HasRootedWinding L P 320 winding
  windingQ : HasRootedWinding (-L) Q 320 winding

def dottieWitnessLift (right : Bool) (x : ℝ) : ℂ :=
  ⟨if right then x else -x, archivedDottieMidIm⟩

def dottieWitnessWinding (right : Bool) : ℤ := if right then -1 else 1

/-- A marked return certificate on the flank strip gives both original
phase addresses at the selected height and the original ordered clock. -/
theorem dottie_band_selects_marked_returns {w : ℂ}
    (hre : w.re ∈ Icc (1/2 + 1/2048) (1/2 + 63/2048))
    (him : w.im + 1/512 ∈ Icc (dottieHeight - 10^8) (dottieHeight + 10^8))
    (hmarked : ∀ x ∈ Icc (archivedDottieFlank - dottieFlankWidth)
        (archivedDottieFlank + dottieFlankWidth), ∀ right : Bool,
        ∃ P Q, MarkedDottiePair (dottieWitnessLift right x) P Q (dottieWitnessWinding right)) :
    ∃ x, dottieHeightAtFlank x = w.im + 1/512 ∧
      w ∈ Metric.closedBall (QuarticModel.archivedRightCenter (dottieHeightAtFlank x)) (31/2048) ∧
      ∀ right : Bool, ∃ P Q,
        MarkedDottiePair (dottieWitnessLift right x) P Q (dottieWitnessWinding right) ∧
        minimalPeriod (step (dottieWitnessLift right x)) (P,Q) = 640 := by
  obtain ⟨x, ⟨_, hx, hheight, hregion⟩, _⟩ := dottie_height_covers_witness_band hre him
  refine ⟨x, hheight, hregion, fun right => ?_⟩
  obtain ⟨P, Q, hpair⟩ := hmarked x hx right
  exact ⟨P,Q,hpair,ordered_clock_640 hpair.periodP hpair.periodQ⟩

#print axioms lifted_arrow_hasDerivAt
#print axioms height_from_marked_arrow
#print axioms ordered_clock_640
#print axioms scalar_period_320_of_divisor_exclusions
#print axioms rootedReturn_hasDerivAt
#print axioms rootedWinding_of_im_bounds
#print axioms dottie_height_covers_witness_band
#print axioms dottie_band_selects_marked_returns

end
end SuperZeta.StirlingCorrection
