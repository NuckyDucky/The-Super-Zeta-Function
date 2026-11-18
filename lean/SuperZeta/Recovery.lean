import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite-window recovery and cumulative checkpoints

The finite-window archive bounds the root-removed function on the boundary
of a cell. The main theorem propagates that boundary observation through
the cell using the maximum modulus principle. Isolating a simple zero,
certifying the boundary inequality, and bounding approximation errors are
inputs supplied by the numerical part of the research.
-/

namespace SuperZeta.Recovery

open Bornology Filter Set
open scoped Topology

/-- Remove the unique simple zero and apply the maximum modulus principle
to the reciprocal. The bound applies on the whole closed cell. -/
theorem cell_lower_bound {G : ℂ → ℂ} {U : Set ℂ} {ρ : ℂ} {c : ℝ}
    (hU : IsBounded U) (hopen : IsOpen U) (hρ : ρ ∈ U)
    (hG : DiffContOnCl ℂ G U) (hzero : G ρ = 0) (hsimple : deriv G ρ ≠ 0)
    (hunique : ∀ z ∈ closure U, G z = 0 → z = ρ) (hc : 0 < c)
    (boundary : ∀ z ∈ frontier U, c ≤ ‖G z‖ / ‖z - ρ‖)
    {z : ℂ} (hz : z ∈ closure U) : c * ‖z - ρ‖ ≤ ‖G z‖ := by
  have hn := hopen.mem_nhds hρ
  have hQ : DiffContOnCl ℂ (dslope G ρ) U :=
    ⟨(Complex.differentiableOn_dslope hn).2 hG.1,
      (continuousOn_dslope (Filter.mem_of_superset hn subset_closure)).2
        ⟨hG.2, hG.1.differentiableAt hn⟩⟩
  have factor (x : ℂ) : (x - ρ) * dslope G ρ x = G x := by
    simpa [smul_eq_mul, hzero] using sub_smul_dslope G ρ x
  have hne (x : ℂ) (hx : x ∈ closure U) : dslope G ρ x ≠ 0 := by
    rcases eq_or_ne x ρ with rfl | h
    · simpa [dslope_same] using hsimple
    · intro hq
      exact h (hunique x hx (by rw [← factor x, hq, mul_zero]))
  have hb (x : ℂ) (hx : x ∈ frontier U) : ‖(dslope G ρ x)⁻¹‖ ≤ c⁻¹ := by
    have h := boundary x hx
    have hdist : ‖x - ρ‖ ≠ 0 := by
      intro he
      rw [he, div_zero] at h
      exact (not_le_of_gt hc) h
    rw [← factor x, norm_mul, mul_div_cancel_left₀ _ hdist] at h
    rw [norm_inv]
    exact (inv_le_inv₀ (hc.trans_le h) hc).2 h
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hU (hQ.inv hne) hb hz
  change ‖(dslope G ρ z)⁻¹‖ ≤ c⁻¹ at hmax
  rw [norm_inv] at hmax
  have hmin := (inv_le_inv₀ (norm_pos_iff.mpr (hne z hz)) hc).1 hmax
  calc
    c * ‖z - ρ‖ ≤ ‖dslope G ρ z‖ * ‖z - ρ‖ :=
      mul_le_mul_of_nonneg_right hmin (norm_nonneg _)
    _ = ‖G z‖ := by rw [← factor z, norm_mul, mul_comm]

/-- A Riemann-plane lower bound gains exactly a factor of two in the
superzeta variable. -/
theorem doubled_distance {F : ℂ → ℂ} (s ρ : ℂ) (c : ℝ)
    (h : c * ‖2*s - ρ‖ ≤ ‖F s‖) : (2*c) * ‖s-ρ/2‖ ≤ ‖F s‖ := by
  rw [show 2*s-ρ = 2*(s-ρ/2) by ring, norm_mul] at h
  norm_num at h
  linarith

/-- Applies to a finite-model root or to a nonzero approximate residual. -/
theorem residual_distance {κ η : ℝ} {s ρ f approximation : ℂ}
    (hκ : 0 < κ) (hlower : κ * ‖s-ρ‖ ≤ ‖f‖)
    (herror : ‖f - approximation‖ ≤ η) :
    ‖s-ρ‖ ≤ (η + ‖approximation‖) / κ := by
  apply (le_div_iff₀ hκ).2
  have htri : ‖f‖ ≤ ‖f - approximation‖ + ‖approximation‖ := by
    simpa using norm_add_le (f-approximation) approximation
  linarith [mul_comm κ ‖s-ρ‖]

/-- Horizontal displacement from a critical-line root gives a lower bound
throughout its cell. -/
theorem horizontal_residual {κ : ℝ} {s ρ f : ℂ}
    (hκ : 0 ≤ κ) (hρ : ρ.re = 1/4) (h : κ * ‖s-ρ‖ ≤ ‖f‖) :
    κ * |s.re-1/4| ≤ ‖f‖ := by
  have hb := Complex.abs_re_le_norm (s-ρ)
  rw [Complex.sub_re, hρ] at hb
  exact (mul_le_mul_of_nonneg_left hb hκ).trans h

/-- Exact finite-block identity for the regrouped Mellin kernel from NATIVE.md.
It applies at every complex kernel value away from its denominator pole. -/
theorem finite_block_remainder (g h : ℂ) (hg : g ≠ 0) (hp : 1+g*h ≠ 0) (J : ℕ) :
    let r := g*h / (1+g*h)
    (∑ j ∈ Finset.range J, r^(j+1)/g) + h*r^J = h := by
  let r := g*h/(1+g*h)
  change (∑ j ∈ Finset.range J, r^(j+1)/g) + h*r^J = h
  have step : r/g + h*r = h := by
    dsimp [r]
    field_simp
    ring
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ r n]
    calc
      _ = (∑ j ∈ Finset.range n, r^(j+1)/g) + (r/g+h*r)*r^n := by ring
      _ = h := by rw [step, ih]

/-- Exact rational arithmetic translating the two archived seven-block
uniform errors to the published distance tolerances. -/
theorem seven_block_tolerances :
    ((0.000077762 : ℝ) / (925/256) < 0.0000216) ∧
    ((0.000118312 : ℝ) / (2407/512) < 0.0000252) := by norm_num

/-- Away from the assigned disk a sufficiently accurate approximant has no
zero. This implication uses the norm inequality and does not require the
approximant itself to be holomorphic. -/
theorem nonzero_outside_disk {κ η radius : ℝ} {s ρ f approximation : ℂ}
    (hκ : 0 < κ) (hlower : κ * ‖s-ρ‖ ≤ ‖f‖)
    (herror : ‖f-approximation‖ ≤ η) (hsmall : η < κ * radius)
    (outside : radius ≤ ‖s-ρ‖) : approximation ≠ 0 := by
  intro he
  rw [he, sub_zero] at herror
  exact (not_le_of_gt hsmall)
    ((mul_le_mul_of_nonneg_left outside hκ.le).trans (hlower.trans herror))

/-- A reflected pair already in a finite census forces a cumulative
discrepancy of at least two at every checkpoint containing both members. -/
theorem discrepancy_of_pair {ι : Type*} (zeros : Finset ι)
    (onLine : ι → Prop) [DecidablePred onLine] {a b : ι}
    (ha : a ∈ zeros) (hb : b ∈ zeros) (hab : a ≠ b)
    (hOffA : ¬ onLine a) (hOffB : ¬ onLine b) :
    2 ≤ zeros.card - (zeros.filter onLine).card := by
  have htwo : 1 < (zeros.filter (fun i => ¬ onLine i)).card :=
    Finset.one_lt_card.mpr
      ⟨a, Finset.mem_filter.mpr ⟨ha, hOffA⟩, b, Finset.mem_filter.mpr ⟨hb, hOffB⟩, hab⟩
  have hsum := Finset.filter_card_add_filter_neg_card_eq_card (s := zeros) onLine
  omega

/-- Cumulative counts at cofinal heights. An index can distinguish
occurrences of a multiple zero. Each finite set lists occurrences up to its
checkpoint; equality with the cardinality of the on-line subset forces
every eligible occurrence to be on the line. -/
theorem on_line_of_cofinal_counts {ι : Type*}
    (height : ι → ℝ) (onLine : ι → Prop) [DecidablePred onLine]
    (T : ℕ → ℝ) (zeros : ℕ → Finset ι)
    (cofinal : ∀ h : ℝ, ∃ k, h ≤ T k)
    (complete : ∀ i k, height i ≤ T k → i ∈ zeros k)
    (count : ∀ k, (zeros k).card = ((zeros k).filter onLine).card)
    (i : ι) : onLine i := by
  obtain ⟨k, hk⟩ := cofinal (height i)
  have heq : (zeros k).filter onLine = zeros k :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (count k).le
  have hi := complete i k hk
  rw [← heq] at hi
  exact (Finset.mem_filter.mp hi).2

end SuperZeta.Recovery
