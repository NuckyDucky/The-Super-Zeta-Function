import SuperZeta.Reciprocal
import Mathlib.Analysis.Calculus.MeanValue

/-! Disk propagation used in the marked spire's finite calculation. -/
noncomputable section
namespace SuperZeta.SpireDisk
open Complex
open scoped NNReal

structure Disk where
  center : ℂ
  radius : ℝ
  nonneg : 0 ≤ radius

def Disk.contains (d : Disk) (z : ℂ) : Prop := ‖z-d.center‖ ≤ d.radius
def stage (a z : ℂ) := exp (a*z)

/-- A certificate may round its next center arbitrarily. The first term
charges this rounding and the second bounds the nonlinear image radius. -/
def encloses (a : ℂ) (d b : Disk) : Prop :=
  ‖stage a d.center - b.center‖ +
    ‖stage a d.center‖*(Real.exp (‖a‖*d.radius)-1) ≤ b.radius

theorem propagate {a : ℂ} {d b : Disk} (he : encloses a d b)
    {z : ℂ} (hz : d.contains z) : b.contains (stage a z) := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (a*(z-d.center)) 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  have harg : ‖a*(z-d.center)‖ ≤ ‖a‖*d.radius := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
  have hdiff : stage a z - stage a d.center =
      stage a d.center*(exp (a*(z-d.center))-1) := by
    unfold stage
    rw [mul_sub, ← exp_add]
    ring_nf
  have hdist : ‖stage a z-stage a d.center‖ ≤ ‖stage a d.center‖*
      (Real.exp (‖a‖*d.radius)-1) := by
    rw [hdiff, norm_mul]
    exact mul_le_mul_of_nonneg_left (h.trans (sub_le_sub_right (Real.exp_le_exp.mpr harg) 1))
      (norm_nonneg _)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (stage a d.center) _).trans
    ((add_le_add_right hdist _).trans (by simpa [encloses, add_comm] using he))

private theorem norm_in {b : Disk} {z : ℂ} (h : b.contains z) : ‖z‖ ≤ ‖b.center‖+b.radius := by
  calc ‖z‖ = ‖z-b.center + b.center‖ := by rw [sub_add_cancel]
       _ ≤ _ := (norm_add_le _ _).trans (by linarith only [show ‖z-b.center‖ ≤ b.radius from h])

/-- Each enclosed exponential contributes its measured derivative factor. -/
theorem stage_bound {a : ℂ} {d b : Disk} (he : encloses a d b)
    {z : ℂ} (hz : d.contains z) :
    HasDerivAt (stage a) (a*stage a z) z ∧
    ‖a*stage a z‖ ≤ ‖a‖*(‖b.center‖+b.radius) := by
  constructor
  · simpa [stage, mul_comm] using ((hasDerivAt_id z).const_mul a).cexp
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_in (propagate he hz)) (norm_nonneg _)

def run : List ℂ → ℂ → ℂ
  | [], z => z
  | a :: tail, z => run tail (stage a z)

inductive Chain : List ℂ → Disk → Disk → ℝ → Prop where
  | nil (d : Disk) : Chain [] d d 1
  | cons {a d b tail dest C} : encloses a d b → Chain tail b dest C →
      Chain (a::tail) d dest (C*(‖a‖*(‖b.center‖+b.radius)))

/-- Product bound along the complete ordered sequence in a certificate. -/
theorem chain_sound {rates d b C} (chain : Chain rates d b C)
    {z : ℂ} (hz : d.contains z) :
    b.contains (run rates z) ∧ ∃ v : ℂ, HasDerivAt (run rates) v z ∧ ‖v‖ ≤ C := by
  induction chain generalizing z with
  | nil => exact ⟨hz, 1, hasDerivAt_id z, by simp⟩
  | @cons a d b tail dest C h _ ih =>
    obtain ⟨hout, v, hv, hnorm⟩ := ih (propagate h hz)
    obtain ⟨hs, hb⟩ := stage_bound h hz
    exact ⟨hout, v*(a*stage a z), hv.comp z hs, by
      rw [norm_mul]; exact mul_le_mul hnorm hb (norm_nonneg _) ((norm_nonneg v).trans hnorm)⟩

/-- The two signs in the archived scalar loop give the original return. -/
theorem run_pair (L z : ℂ) : run [-L,L] z = Reciprocal.scalarReturn L z := rfl

/-- The derivative bound for the entire chain controls every pair in its source disk. -/
theorem chain_lipschitz {rates d b C} (h : Chain rates d b C)
    {x y : ℂ} (hx : d.contains x) (hy : d.contains y) :
    ‖run rates y-run rates x‖ ≤ C*‖y-x‖ := by
  let S := Metric.closedBall d.center d.radius
  have hcert (z : ℂ) (hz : z ∈ S) := (chain_sound h (z:=z)
    (by simpa [S,Metric.mem_closedBall,dist_eq_norm,Disk.contains] using hz)).2
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s:=S)
    (f':=deriv (run rates))
  · intro z hz
    obtain ⟨v, hv, _⟩ := hcert z hz
    rw [hv.deriv]
    exact hv.hasDerivWithinAt
  · intro z hz
    obtain ⟨v, hv, hn⟩ := hcert z hz
    rwa [hv.deriv]
  · exact convex_closedBall _ _
  · simpa [S, Metric.mem_closedBall, dist_eq_norm] using hx
  · simpa [S, Metric.mem_closedBall, dist_eq_norm] using hy

/-- A common even scalar clock doubles when the two phases are read in order.
This applies both on and off the centerline. -/
theorem paired_period_of_even {L P M : ℂ} {k : ℕ} (hk : Even k)
    (hP : Function.minimalPeriod (Reciprocal.scalarReturn L) P = k)
    (hM : Function.minimalPeriod (Reciprocal.scalarReturn (-L)) M = k) :
    Function.minimalPeriod (Reciprocal.step L) (P,M) = 2*k := by
  let f := Reciprocal.step L
  let p := Function.minimalPeriod f (P,M)
  have hs : f^[2] = Prod.map (Reciprocal.scalarReturn L) (Reciprocal.scalarReturn (-L)) :=
    funext (Reciprocal.step_twice L)
  have hm : Function.minimalPeriod f^[2] (P,M) = k := by
    rw [hs, ← hP]
    apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
    intro n
    rw [Function.isPeriodicPt_prodMap]
    simp only [Function.isPeriodicPt_iff_minimalPeriod_dvd, hM, hP, and_self]
  have hq : p / p.gcd 2 = k := (Function.minimalPeriod_iterate_eq_div_gcd (f:=f) (x:=(P,M))
    (by decide : 2≠0)).symm.trans hm
  have hg : p.gcd 2 ∣ 2 := Nat.gcd_dvd_right _ _
  have he : k * p.gcd 2 = p := by
    rw [← hq, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  rcases (Nat.dvd_prime Nat.prime_two).mp hg with h | h
  · rw [h, mul_one] at he
    have h2 : 2 ∣ p := he ▸ even_iff_two_dvd.mp hk
    rw [Nat.gcd_eq_right h2] at h
    contradiction
  · change p = 2*k
    rw [h] at he
    omega

/-- The alternating rate list starts with −L, as in the enclosure script. -/
def alternating (L : ℂ) : ℕ → List ℂ
  | 0 => []
  | n+1 => -L :: L :: alternating L n

theorem run_alternating (L : ℂ) (n : ℕ) (z : ℂ) :
    run (alternating L n) z = (Reciprocal.scalarReturn L)^[n] z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => exact ih (Reciprocal.scalarReturn L z)

theorem disjoint_excludes {L : ℂ} {n : ℕ} {d b : Disk} {K : ℝ}
    (hc : Chain (alternating L n) d b K)
    (hsep : d.radius+b.radius < ‖d.center-b.center‖) {z : ℂ} (hz : d.contains z) :
    ¬ Function.IsPeriodicPt (Reciprocal.scalarReturn L) n z := by
  intro hp
  have hb := (chain_sound hc hz).1
  rw [run_alternating, hp.eq] at hb
  have hdist := norm_sub_le_norm_sub_add_norm_sub d.center z b.center
  rw [norm_sub_rev d.center z] at hdist
  unfold Disk.contains at hz hb
  linarith

set_option maxRecDepth 4096 in
/-- A direct interface for the archived scalar certificate. An enclosure of
the full return bounds the Lipschitz constant; the center residual traps the
disk. Excluding return times 64 and 160 suffices for primitive period 320. -/
theorem spire_capture {L entry : ℂ} {d b : Disk} {C : ℝ≥0}
    (hfull : Chain (alternating L 320) d b C) (hC : C < 1)
    (hres : ‖(Reciprocal.scalarReturn L)^[320] d.center - d.center‖ + C*d.radius ≤ d.radius)
    (hentry : d.contains entry)
    (hshort : ∀ z, d.contains z →
      ¬ Function.IsPeriodicPt (Reciprocal.scalarReturn L) 64 z ∧
      ¬ Function.IsPeriodicPt (Reciprocal.scalarReturn L) 160 z) :
    ∃ z, d.contains z ∧ Function.minimalPeriod (Reciprocal.scalarReturn L) z = 320 ∧
      Filter.Tendsto (fun k : ℕ => ((Reciprocal.scalarReturn L)^[320])^[k] entry)
        Filter.atTop (nhds z) := by
  let g := Reciprocal.scalarReturn L
  let D := Metric.closedBall d.center d.radius
  have mem {x : ℂ} : x ∈ D ↔ d.contains x := by simp [D, Metric.mem_closedBall, dist_eq_norm, Disk.contains]
  have hl {x y : ℂ} (hx : x ∈ D) (hy : y ∈ D) : ‖g^[320] y-g^[320] x‖ ≤ C*‖y-x‖ := by
    simpa only [run_alternating, g] using chain_lipschitz hfull (mem.mp hx) (mem.mp hy)
  have hmap : Set.MapsTo g^[320] D D := by
    intro x hx
    apply mem.mpr
    have hc : d.center ∈ D := Metric.mem_closedBall_self d.nonneg
    have ht := norm_sub_le_norm_sub_add_norm_sub (g^[320] x) (g^[320] d.center) d.center
    have hb := mul_le_mul_of_nonneg_left (mem.mp hx) C.coe_nonneg
    change ‖g^[320] x-d.center‖ ≤ d.radius
    change ‖g^[320] d.center-d.center‖ + _ ≤ _ at hres
    linarith only [ht, hl hc hx, hb, hres]
  have hcontract : ContractingWith C (hmap.restrict (g^[320]) D D) :=
    ⟨hC, LipschitzWith.of_dist_le_mul (fun x y => by
      change dist (g^[320] x.val) (g^[320] y.val) ≤ (C:ℝ)*dist x.val y.val
      simpa only [dist_eq_norm] using hl y.property x.property)⟩
  obtain ⟨z, hz, hfixed, hlim, _⟩ := hcontract.exists_fixedPoint' Metric.isClosed_closedBall.isComplete
    hmap (mem.mpr hentry) (edist_ne_top _ _)
  have hp : Function.IsPeriodicPt g 320 z := hfixed
  let m := Function.minimalPeriod g z
  have hdiv : m ∣ 320 := hp.minimalPeriod_dvd
  have hm : m < 321 := by have := Nat.le_of_dvd (by decide : 0<320) hdiv; omega
  have cases320 : ∀ i : Fin 321, i.val ∣ 320 → i.val = 320 ∨ i.val ∣ 64 ∨ i.val ∣ 160 := by decide
  obtain h | h | h := cases320 ⟨m,hm⟩ hdiv
  · exact ⟨z, mem.mp hz, h, hlim⟩
  · exact False.elim ((hshort z (mem.mp hz)).1 (Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr h))
  · exact False.elim ((hshort z (mem.mp hz)).2 (Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr h))

end SuperZeta.SpireDisk
