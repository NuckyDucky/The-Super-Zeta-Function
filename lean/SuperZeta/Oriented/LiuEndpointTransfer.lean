import SuperZeta.Oriented.LiuConnection
import SuperZeta.Multiplicity
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.Ring

/-!
Liu's November 13 preprint gives the polynomial in §7 after Theorem 7.2.
Bebel's QuasiRiemannTracker PR 143, source c74d855c3bdfceeee059501aea76c8b1627b9abd,
proves nonvanishing for all Dirichlet characters at its unique root in (13/15,7/8).
The local library uses Lean 4.19.0. The tracker's separately certified build uses 4.34.1.
The argument H below has the upstream theorem's mathematical type and is an
ordinary proof argument. This file declares no external proof as an axiom.
-/

namespace LiuTurnTransfer

open DottieOriented.LiuConnection Complex Filter Set
open scoped Topology
noncomputable section

def paperPolynomial (x : ℝ) : ℝ :=
  487371101862528*x^9 - 4126408710053184*x^8 + 15517896164111592*x^7
  - 34020380857037616*x^6 + 47916748658170215*x^5 - 44964545308854309*x^4
  + 28111661257098222*x^3 - 11291220876239226*x^2 + 2643837682856883*x
  - 274959111914881

def trackerPolynomial (x : ℝ) : ℝ :=
  -274959111914881 + x * (2643837682856883 + x * (-11291220876239226 +
  x * (28111661257098222 + x * (-44964545308854309 + x * (47916748658170215 +
  x * (-34020380857037616 + x * (15517896164111592 +
  x * (-4126408710053184 + x * 487371101862528))))))))

theorem same_polynomial (x : ℝ) : paperPolynomial x = trackerPolynomial x := by
  unfold paperPolynomial trackerPolynomial
  ring

theorem factored_contact (x : ℝ) :
    paperPolynomial x = 7*(7-6*x)^4*(9*x-7)^5 -
      3888*19^5*(15*x-13)^4*(1-x)^5 := by
  unfold paperPolynomial
  ring

def contact : ℝ :=
  sInf {x : ℝ | 13/15 < x ∧ x < 7/8 ∧ trackerPolynomial x = 0}

theorem same_contact :
    contact = sInf {x : ℝ | 13/15 < x ∧ x < 7/8 ∧ paperPolynomial x = 0} := by
  simp only [contact, same_polynomial]

/-- Right endpoint of the rational enclosure proved in Candidate.bound_le. -/
def trackerUpper : ℝ :=
  9908119238306612133369374975000622988619121777878229799765263366946606045502455625911569003364955967645745531862430068266267717 /
  11345012023616779600791582323373494582287250283647959965785871011074347975117040113347744503437234376916434871293982689424818700

theorem reflected_floor (h : contact ≤ trackerUpper) :
    (12665414389 : ℝ)/10^11 < 1-contact := by
  have hcompare : trackerUpper < 1-(12665414389 : ℝ)/10^11 := by norm_num [trackerUpper]
  linarith

/-- Exact rational signs around Liu's endpoint, checked in the local kernel. -/
theorem rational_bracket_signs :
    0 < paperPolynomial (87334585610671857 / 10^17) ∧
    paperPolynomial (87334585610671858 / 10^17) < 0 := by
  norm_num [paperPolynomial]

/-- This is the statement proved as Candidate.bound in the external certificate. -/
def DirichletBound (B : ℝ) : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {w : ℂ},
    B < w.re → ¬(χ = 1 ∧ w = 1) → DirichletCharacter.LFunction χ w ≠ 0

/-- Applies the all-moduli statement to the actual Riemann zeta function. -/
theorem riemann_specialization {B : ℝ} (H : DirichletBound B) {w : ℂ}
    (h : B < w.re) (hp : w ≠ 1) : riemannZeta w ≠ 0 := by
  simpa only [DirichletCharacter.LFunction_modOne_eq] using
    H (q := 1) (1 : DirichletCharacter ℂ 1) h (fun he => hp he.2)

private theorem reflected_zero {w : ℂ} (hpos : 0 < w.re) (hp : w ≠ 1)
    (hz : riemannZeta w = 0) : riemannZeta (1-w) = 0 := by
  have hnat (n : ℕ) : w ≠ -(n : ℂ) := by
    intro he
    have h := congrArg Complex.re he
    simp at h
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [riemannZeta_one_sub hnat hp, hz, mul_zero]

/-- Both endpoints for the two actual shifted Hurwitz sums, in the s-coordinate.
The only non-library nonvanishing input H is exactly the all-Dirichlet bound above. -/
theorem both_orientations_in_strip {B : ℝ} (H : DirichletBound B)
    {a : ℝ} (ha : a = Real.pi/6 ∨ a = -(Real.pi/6)) {s : ℂ}
    (hs : 0 < s.re) (hp : 2*s ≠ 1)
    (hz : reference (1/2-a/Real.pi) (2*s) = 0) :
    (1-B)/2 ≤ s.re ∧ s.re ≤ B/2 := by
  have hb : 1/2-a/Real.pi = 1/3 ∨ 1/2-a/Real.pi = 2/3 := by
    rcases ha with rfl | rfl
    · exact Or.inl native_third_shifts.1
    · exact Or.inr native_third_shifts.2
  have hpos : 0 < (2*s).re := by simp [two_mul]; linarith
  have hzero := (reference_zero_iff hb hpos hp).mp hz
  have hleft := reflected_zero hpos hp hzero
  have hright : (2*s).re ≤ B := le_of_not_gt (fun h => riemann_specialization H h hp hzero)
  have href : 1-2*s ≠ 1 := by
    intro he
    have he' := congrArg Complex.re he
    simp at he'
    linarith
  have hlow : (1-2*s).re ≤ B := le_of_not_gt (fun h => riemann_specialization H h href hleft)
  simp [two_mul] at hright hlow
  constructor <;> linarith

theorem at_liu_endpoint (H : DirichletBound contact)
    {a : ℝ} (ha : a = Real.pi/6 ∨ a = -(Real.pi/6)) {s : ℂ}
    (hs : 0 < s.re) (hp : 2*s ≠ 1)
    (hz : reference (1/2-a/Real.pi) (2*s) = 0) :
    (1-contact)/2 ≤ s.re ∧ s.re ≤ contact/2 :=
  both_orientations_in_strip H ha hs hp hz

private def thirdFactor (w : ℂ) : ℂ := (Real.pi : ℂ)^(-w)*((3 : ℂ)^w-1)

private theorem thirdFactor_analytic (w : ℂ) : AnalyticAt ℂ thirdFactor w := by
  unfold thirdFactor
  simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    Complex.cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0)]
  fun_prop

/-- Orders agree for the actual shifted references. No zero-free boundary is an input. -/
theorem reference_orders {b : ℝ} (hb : b = 1/3 ∨ b = 2/3) {w : ℂ}
    (hw : 0 < w.re) (hp : w ≠ 1) :
    ∃ h : AnalyticAt ℂ (reference b) w, h.order = (SuperZeta.Multiplicity.analytic_zeta hp).order := by
  have hfactor := thirdFactor_analytic w
  have hzeta := SuperZeta.Multiplicity.analytic_zeta hp
  have hprod := hfactor.mul hzeta
  have hnear : (thirdFactor * riemannZeta) =ᶠ[𝓝 w] reference b := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hp] with z hz
    change thirdFactor z * riemannZeta z = reference b z
    rw [reference_at_thirds hb hz, thirdFactor, mul_assoc]
  refine ⟨hprod.congr hnear, ?_⟩
  rw [hprod.order_congr hnear, AnalyticAt.order_mul]
  have hne : thirdFactor w ≠ 0 :=
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (three_factor_ne_zero hw)
  rw [hfactor.order_eq_zero_iff.mpr hne, zero_add]

theorem reference_orders_at_twice {b : ℝ} (hb : b = 1/3 ∨ b = 2/3) {s : ℂ}
    (hpos : 0 < (2*s).re) (hp : 2*s ≠ 1) :
    ∃ h : AnalyticAt ℂ (fun z : ℂ => reference b (2*z)) s,
      h.order = (SuperZeta.Multiplicity.analytic_zeta hp).order := by
  obtain ⟨h, horder⟩ := reference_orders hb hpos hp
  exact ⟨h.comp (SuperZeta.Multiplicity.scale_analytic 2 s),
    (SuperZeta.Multiplicity.scale_order (by norm_num : (2 : ℂ) ≠ 0) h).trans horder⟩

def nativeReference (a : ℝ) := reference (1/2-a/Real.pi)

/-- The two Hurwitz summands exchange places when the native angle reverses. -/
theorem native_even (a : ℝ) : nativeReference (-a) = nativeReference a := by
  funext w
  let b : ℝ := 1/2-a/Real.pi
  have h : 1/2-(-a)/Real.pi = 1-b := by dsimp [b]; ring
  unfold nativeReference reference
  rw [h, sub_sub_cancel, add_comm]

/-- A differentiable zero path gives an actual zero path at the opposite angle.
Running the same positive angular increment there reverses the tangent vector. -/
theorem reflected_zero_path {a : ℝ} {z : ℝ → ℂ} {V : ℂ}
    (hz : ∀ᶠ t in 𝓝 a, nativeReference t (z t) = 0) (hv : HasDerivAt z V a) :
    (∀ᶠ t in 𝓝 (-a), nativeReference t (z (-t)) = 0) ∧
    HasDerivAt (fun t : ℝ => z (-t)) (-V) (-a) := by
  constructor
  · have hflip : Tendsto (fun t : ℝ => -t) (𝓝 (-a)) (𝓝 a) := by
      simpa only [neg_neg] using (continuous_neg.continuousAt (x := -a)).tendsto
    filter_upwards [hflip.eventually hz] with t ht
    simpa only [native_even] using ht
  · have h : HasDerivAt z V (0-(-a)) := by simpa using hv
    simpa using h.comp_const_sub 0 (-a)

/-- Nonvanishing of the arithmetic quotient used in the angular-speed formula.
This holds for every character mod 3 and hence for the odd character used there. -/
theorem angular_arithmetic_quotient_ne_zero (χ : DirichletCharacter ℂ 3) {w : ℂ}
    (hw : 0 < w.re) :
    χ.LFunction (1+w) / (1-(3:ℂ)^(-w)) ≠ 0 := by
  have hr : 1 < (1+w).re := by simp [hw]
  have hnum : χ.LFunction (1+w) ≠ 0 := by
    rw [χ.LFunction_eq_LSeries hr]
    exact χ.LSeries_ne_zero_of_one_lt_re hr
  have hden : 1-(3:ℂ)^(-w) ≠ 0 := by
    apply sub_ne_zero.mpr
    rw [Complex.cpow_neg]
    intro h
    have hpow : (3:ℂ)^w = 1 := by simpa using congrArg Inv.inv h.symm
    exact (three_factor_ne_zero hw) (sub_eq_zero.mpr hpow)
  exact div_ne_zero hnum hden

end
end LiuTurnTransfer

#print axioms LiuTurnTransfer.same_polynomial
#print axioms LiuTurnTransfer.same_contact
#print axioms LiuTurnTransfer.factored_contact
#print axioms LiuTurnTransfer.rational_bracket_signs
#print axioms LiuTurnTransfer.reflected_floor
#print axioms LiuTurnTransfer.at_liu_endpoint
#print axioms LiuTurnTransfer.reference_orders_at_twice
#print axioms LiuTurnTransfer.reflected_zero_path
#print axioms LiuTurnTransfer.angular_arithmetic_quotient_ne_zero
