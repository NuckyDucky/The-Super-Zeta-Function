import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Ring

/-! The ordered reciprocal exponential map, its cap, its two scalar returns,
and its actual logarithmic lifts. The source is Nick's logarithmic-lift
manuscript, equations (pair recurrence) and (scalar return). -/

noncomputable section

namespace SuperZeta.Reciprocal

open Complex
open scoped ComplexConjugate Topology NNReal

/-- The ordered phase update. The positive stage reads the second phase. -/
def step (L : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (exp (L * p.2), exp (-L * p.1))

/-- The positive-rooted scalar return, in its original order. -/
def scalarReturn (L z : ℂ) : ℂ := exp (L * exp (-L * z))

theorem step_twice (L : ℂ) (p : ℂ × ℂ) :
    step L (step L p) = (scalarReturn L p.1, scalarReturn (-L) p.2) := by
  simp [step, scalarReturn]

/-- The marked centerline half-step, whose square returns to its original phase. -/
def halfStep (y : ℝ) (z : ℂ) : ℂ := exp ((Complex.I * ↑y) * conj z)

theorem halfStep_squared (y : ℝ) (z : ℂ) :
    halfStep y (halfStep y z) = scalarReturn (Complex.I * ↑y) z := by
  simp [halfStep, scalarReturn, ← Complex.exp_conj]

theorem centerline_step (y : ℝ) (z : ℂ) :
    step (Complex.I * ↑y) (z, conj z) = (halfStep y z, conj (halfStep y z)) := by
  simp [step, halfStep, ← Complex.exp_conj]

/-- Diagonal embedding preserves the primitive period of the marked half-step. -/
theorem centerline_pair_period (y : ℝ) (z : ℂ) :
    Function.minimalPeriod (step (Complex.I * ↑y)) (z, conj z) =
    Function.minimalPeriod (halfStep y) z := by
  let embed : ℂ → ℂ × ℂ := fun w => (w, conj w)
  have he : Function.Semiconj embed (halfStep y) (step (Complex.I * ↑y)) :=
    fun w => (centerline_step y w).symm
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change (step (Complex.I * ↑y))^[n] (embed z) = embed z ↔ (halfStep y)^[n] z = z
  rw [← (he.iterate_right n z)]
  exact ⟨fun e => congrArg Prod.fst e, congrArg embed⟩

/-- The primitive scalar clock runs at p/gcd(p,2) on the invariant diagonal. -/
theorem centerline_scalar_period (y : ℝ) (z : ℂ) :
    let p := Function.minimalPeriod (step (Complex.I * ↑y)) (z, conj z)
    Function.minimalPeriod (scalarReturn (Complex.I * ↑y)) z = p / Nat.gcd p 2 := by
  dsimp only
  rw [centerline_pair_period]
  have hr : scalarReturn (Complex.I * ↑y) = (halfStep y)^[2] :=
    funext fun w => (halfStep_squared y w).symm
  rw [hr]
  exact Function.minimalPeriod_iterate_eq_div_gcd (by decide : 2 ≠ 0)

/-- The three named period windows, conditional on their physical period
certificate. The numerical enclosure of each witness is a separate result. -/
theorem witness_clocks (y : ℝ) (z : ℂ) :
    let p := Function.minimalPeriod (step (Complex.I * ↑y)) (z, conj z)
    let q := Function.minimalPeriod (scalarReturn (Complex.I * ↑y)) z
    (p = 639 → q = 639) ∧ (p = 640 → q = 320) ∧ (p = 641 → q = 641) := by
  dsimp only
  have h := centerline_scalar_period y z
  dsimp only at h
  rw [h]
  exact ⟨fun e => by rw [e]; decide, fun e => by rw [e]; decide, fun e => by rw [e]; decide⟩

/-- The affine coordinate and the general two-base return in the foundations manuscript. -/
def translate (κ c L z : ℂ) : ℂ := κ + c * L * z
def twoBaseReturn (L c z : ℂ) : ℂ := exp (L * exp (c * L * z))
def additiveStage (κ z : ℂ) : ℂ := exp z + κ

theorem reciprocal_slice (L z : ℂ) : twoBaseReturn L (-1) z = scalarReturn L z := by
  simp [twoBaseReturn, scalarReturn]

theorem translate_bijective {c L : ℂ} (κ : ℂ) (hc : c ≠ 0) (hL : L ≠ 0) :
    Function.Bijective (translate κ c L) := by
  have h := mul_ne_zero hc hL
  constructor
  · intro z w e
    exact mul_left_cancel₀ h (add_left_cancel e)
  · intro w
    refine ⟨(w-κ)/(c*L), ?_⟩
    unfold translate
    rw [mul_comm (c*L), div_mul_cancel₀ _ h]
    ring

/-- Intertwining identity, with a bijective affine coordinate and the ordered
outer parameter κ and inner parameter κ + δ explicit. -/
theorem translated_two_base (κ δ z : ℂ) :
    translate κ (exp δ) (exp κ) (twoBaseReturn (exp κ) (exp δ) z) =
    additiveStage κ (additiveStage (κ+δ) (translate κ (exp δ) (exp κ) z)) := by
  simp only [translate, twoBaseReturn, additiveStage, Complex.exp_add]
  ring

/-- The forward orbit marked by the cap (1,1). -/
def capOrbit (L : ℂ) : ℕ → ℂ × ℂ
  | 0 => (1, 1)
  | n + 1 => step L (capOrbit L n)

/-- Certificate interface for the original paired orbit. A primitive period
and capture of the marked point follow from contraction on a closed trapping
region, an orbit entry, and the exclusion of every proper positive divisor. -/
theorem cap_capture {L : ℂ} {p N : ℕ} (hp : 0 < p) {D : Set (ℂ × ℂ)}
    (hclosed : IsClosed D) (hmap : Set.MapsTo (step L)^[p] D D)
    {K : ℝ≥0} (hcontract : ContractingWith K (hmap.restrict ((step L)^[p]) D D))
    (hentry : capOrbit L N ∈ D)
    (hexclude : ∀ z ∈ D, ∀ q : ℕ, q ∣ p → 0 < q → q < p → ¬ Function.IsPeriodicPt (step L) q z) :
    ∃ z ∈ D, Function.minimalPeriod (step L) z = p ∧
      Filter.Tendsto (fun k : ℕ => ((step L)^[p])^[k] (capOrbit L N)) Filter.atTop (𝓝 z) := by
  obtain ⟨z, hz, hfixed, hlim, _⟩ :=
    hcontract.exists_fixedPoint' hclosed.isComplete hmap hentry (edist_ne_top _ _)
  have hper : Function.IsPeriodicPt (step L) p z := hfixed
  have hdvd := hper.minimalPeriod_dvd
  have hpos := hper.minimalPeriod_pos hp
  refine ⟨z, hz, (Nat.le_of_dvd hp hdvd).antisymm ?_, hlim⟩
  exact le_of_not_gt fun h => hexclude z hz _ hdvd hpos h (Function.isPeriodicPt_minimalPeriod _ _)

theorem cap_even (L : ℂ) (n : ℕ) :
    capOrbit L (2 * n) = ((scalarReturn L)^[n] 1, (scalarReturn (-L))^[n] 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ]
    change step L (step L (capOrbit L (2*n))) = _
    rw [step_twice, ih]
    simp only [Function.iterate_succ_apply']

/-- The odd marked orbit follows the second cap, zero, under the same return. -/
theorem cap_odd (L : ℂ) (n : ℕ) :
    (capOrbit L (2*n+1)).1 = (scalarReturn L)^[n+1] 0 := by
  induction n with
  | zero => simp [capOrbit, step, scalarReturn]
  | succ n ih =>
    calc (capOrbit L (2*(n+1)+1)).1 = scalarReturn L (capOrbit L (2*n+1)).1 := by
           rw [Nat.mul_succ]; rfl
         _ = (scalarReturn L)^[n+1+1] 0 := by rw [ih, Function.iterate_succ_apply' _ (n+1)]

/-- Parameter negation exchanges the two ordered phases at every finite time. -/
theorem cap_neg (L : ℂ) (n : ℕ) : capOrbit (-L) n = (capOrbit L n).swap := by
  induction n with
  | zero => rfl
  | succ n ih => simp [capOrbit, ih, step, Prod.swap]

def conjugatePair (p : ℂ × ℂ) : ℂ × ℂ := (conj p.1, conj p.2)

/-- Conjugation acts at every finite time; together with cap_neg this
also describes reflection across the imaginary parameter axis. -/
theorem cap_conj (L : ℂ) (n : ℕ) : capOrbit (conj L) n = conjugatePair (capOrbit L n) := by
  induction n with
  | zero => simp [capOrbit, conjugatePair]
  | succ n ih => simp [capOrbit, ih, conjugatePair, step, ← Complex.exp_conj]

/-- Actual exponents along the ordered pair, making no logarithm branch choice. -/
def lifts (L : ℂ) (p : ℂ × ℂ) : ℂ × ℂ := (L * p.2, -L * p.1)

theorem fixed_iff (L P M : ℂ) :
    step L (P, M) = (P, M) ↔ P = exp (L * M) ∧ M = exp (-L * P) := by
  simp [step, Prod.ext_iff, eq_comm]

theorem scalar_hasDerivAt (L z : ℂ) :
    HasDerivAt (scalarReturn L) (-L^2 * exp (-L*z) * scalarReturn L z) z := by
  have h := ((((hasDerivAt_id z).const_mul (-L)).cexp.const_mul L).cexp)
  change HasDerivAt (scalarReturn L)
    (scalarReturn L z * (L * (exp (-L*z) * (-L*1)))) z at h
  convert h using 1
  ring

/-- At a fixed pair, the return multiplier is the product of the lifted exponents. -/
theorem fixed_return_multiplier {L P M : ℂ} (hp : step L (P, M) = (P, M)) :
    scalarReturn L P = P ∧
    deriv (scalarReturn L) P = (lifts L (P, M)).1 * (lifts L (P, M)).2 := by
  obtain ⟨hP, hM⟩ := (fixed_iff L P M).mp hp
  have hret : scalarReturn L P = P := by
    unfold scalarReturn
    rw [← hM, ← hP]
  refine ⟨hret, ?_⟩
  rw [(scalar_hasDerivAt L P).deriv, hret, ← hM]
  dsimp [lifts]
  ring

/-- Eliminating the lift gives a balanced pair of exponential terms. -/
theorem fixed_balance {L P M : ℂ} (hp : step L (P, M) = (P, M)) :
    let q := lifts L (P, M)
    q.1 * exp q.1 + q.2 * exp q.2 = 0 := by
  obtain ⟨hP, hM⟩ := (fixed_iff L P M).mp hp
  dsimp [lifts]
  rw [← hP, ← hM]
  ring

/-- A balanced lifted pair of multiplier one satisfies the characteristic
equation that generates the reciprocal quartets. -/
theorem parabolic_characteristic {U V : ℂ}
    (hUV : U * V = 1) (hb : U * exp U + V * exp V = 0) :
    U^2 * exp (U - U⁻¹) = -1 := by
  have hU : U ≠ 0 := by
    intro h
    simp [h] at hUV
  have hv : V = U⁻¹ := by
    calc V = U⁻¹ * (U * V) := by rw [← mul_assoc, inv_mul_cancel₀ hU, one_mul]
         _ = U⁻¹ := by rw [hUV, mul_one]
  rw [← hv, Complex.exp_sub, ← mul_div_assoc]
  apply (div_eq_iff (Complex.exp_ne_zero V)).2
  have hbal : U * exp U = -(V * exp V) := eq_neg_of_add_eq_zero_left hb
  calc U^2 * exp U = U * (U * exp U) := by ring
       _ = U * (-(V * exp V)) := by rw [hbal]
       _ = -1 * exp V := by rw [mul_neg, ← mul_assoc, hUV]; ring

end SuperZeta.Reciprocal
