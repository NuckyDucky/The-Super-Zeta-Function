import SuperZeta.QuartetRadius
import SuperZeta.Stieltjes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.PSeries

/-! Uniform bounds for the indexed nonunit q=1 cosine roots. -/
namespace SuperZeta.RootBounds
open SuperZeta.QuartetRadius Real Complex
noncomputable section

def x (t : ℝ) := Real.cosh t * Real.sin (θ t)
def u (t : ℝ) : ℂ := ⟨x t,t⟩

private lemma angle_data {t : ℝ} (ht : 0<t) :
    0 ≤ Real.sin (θ t) ∧ Real.sinh t * Real.cos (θ t) = -t := by
  have hs := Real.sinh_pos_iff.mpr ht
  have ha : 0 ≤ a t := div_nonneg ht.le hs.le
  have hb : a t ≤ 1 := (div_le_one hs).mpr (Real.self_le_sinh_iff.mpr ht.le)
  constructor
  · rw [θ,Real.sin_arccos]; positivity
  · rw [θ,Real.cos_arccos (by linarith) (by linarith),a]
    field_simp [hs.ne']

/-- This coordinate is the actual root associated to the polar exponential phase. -/
theorem original_coordinate {t : ℝ} (ht : 0<t) :
    Quartet.coordinate (polarPhase t) = u t := by
  have hc := (angle_data ht).2
  rw [Real.sinh_eq] at hc
  unfold Quartet.coordinate polarPhase
  rw [← Complex.exp_neg, div_eq_iff (by simp : 2*Complex.I ≠ 0)]
  apply Complex.ext
  · simp [u, Complex.exp_re, Complex.mul_re]
    linarith
  · simp [u, x, Complex.exp_im, Complex.mul_im, Real.cosh_eq]
    ring

theorem x_lower {t : ℝ} {n : ℕ} (hn : 0<n) (he : level t = 2*π*n) : (n:ℝ) ≤ x t := by
  have hθ := Real.arccos_le_pi (-a t)
  change θ t ≤ π at hθ
  change 2*(θ t + x t) - π = _ at he
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [Real.pi_gt_three, mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (sub_nonneg.mpr hn')]

/-- A global geometric estimate from the first two positive terms of sinh(t). -/
theorem height_bound {t : ℝ} (ht : 0<t) : t^2 ≤ 2*x t := by
  obtain ⟨hsin,hcos⟩ := angle_data ht
  have h := sum_le_hasSum (Finset.range 2) (fun n _ => by positivity) (Real.hasSum_sinh t)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hs := Real.sinh_pos_iff.mpr ht
  have hg : Real.sinh t ≤ Real.cosh t := by
    rw [Real.sinh_eq,Real.cosh_eq]; linarith [Real.exp_pos (-t)]
  have hx : 0 ≤ x t := mul_nonneg (Real.cosh_pos _).le hsin
  have hxs := mul_le_mul_of_nonneg_right hg hsin
  change _ ≤ x t at hxs
  have hxs2 := pow_le_pow_left₀ (mul_nonneg hs.le hsin) hxs 2
  have hcircle := congrArg (fun y : ℝ => Real.sinh t ^2 * y) (Real.sin_sq_add_cos_sq (θ t))
  have hcos2 := congrArg (fun y : ℝ => y^2) hcos
  have hsq := pow_le_pow_left₀ (by positivity) h 2
  have h4 : t^4 ≤ 3*(x t)^2 := by
    nlinarith only [hsq, hxs2, hcircle, hcos2, sq_nonneg (t^3)]
  by_contra! hbad
  nlinarith only [h4, sq_nonneg (x t), mul_self_lt_mul_self (by linarith : 0 ≤ 2*x t) hbad]

private lemma u_square_norm (t : ℝ) : ‖u t^2‖ = x t^2+t^2 := by
  rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
  simp [u, pow_two]

private lemma sq_components (t : ℝ) :
    (u t^2).re=x t^2-t^2 ∧ (u t^2).im=2*x t*t := by
  simp [u,pow_two,Complex.mul_re,Complex.mul_im]
  ring

theorem squared_off_cut {t : ℝ} {n : ℕ} (hn : 0<n) (ht : 0<t) (he : level t=2*π*n) :
    u t^2 ∈ Complex.slitPlane := by
  right
  rw [(sq_components t).2]
  have h := x_lower hn he
  have hx : 0<x t := lt_of_lt_of_le (by exact_mod_cast hn) h
  positivity

/-- For every indexed root, including the first, the Stieltjes resolvent has
the same half-angle bound, with the concrete constant 1/2. -/
theorem resolvent_margin {t : ℝ} {n : ℕ} (hn : 0<n) (ht : 0<t) (he : level t=2*π*n)
    (r : ℝ) (hr : 0≤r) : (1/2:ℝ)*(r+‖u t^2‖) ≤ ‖(r:ℂ)+u t^2‖ := by
  have hx := x_lower hn he
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hx1 := h1.trans hx
  have hb := height_bound ht
  have hang : 0 ≤ ‖u t^2‖+2*(u t^2).re := by
    rw [u_square_norm, (sq_components t).1]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (show 0≤x t by linarith)]
  let z := u t^2
  have ez : ‖(r:ℂ)+z‖^2 = r^2+2*r*z.re+‖z‖^2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  change 1/2*(r+‖z‖) ≤ ‖(r:ℂ)+z‖
  by_contra! bad
  have hh := mul_self_lt_mul_self (norm_nonneg _) bad
  nlinarith only [hh,ez,sq_nonneg (r-‖z‖),
    mul_nonneg hr (show 0≤‖z‖+2*z.re from hang)]

/-- Square-norm growth suffices for spectral convergence throughout Re(s)>1/2. -/
theorem norm_series {t : ℕ → ℝ} (roots : ∀ n, level (t n)=2*π*(n+1))
    {σ : ℝ} (hσ : 1/2<σ) : Summable fun n => ‖u (t n)^2‖^(-σ) := by
  have hs : Summable (fun n : ℕ => (n:ℝ)^(-2*σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) _ (hs.comp_injective Nat.succ_injective)
  intro n
  have hx := x_lower (Nat.succ_pos n) (by simpa using roots n)
  have hp : 0 < ((n+1:ℕ):ℝ) := by positivity
  change _ ≤ ((n+1:ℕ):ℝ)^(-2*σ)
  rw [show -2*σ = (2:ℝ)*(-σ) by ring, Real.rpow_mul hp.le, Real.rpow_two]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  rw [u_square_norm]
  nlinarith [pow_le_pow_left₀ hp.le hx 2,sq_nonneg (t n)]

theorem squared_real_growth {t : ℝ} {n : ℕ} (hn : 4≤n) (ht : 0<t)
    (he : level t=2*π*n) : (n:ℝ)^2/2 ≤ (u t^2).re := by
  have hx := x_lower (by omega : 0<n) he
  have h4 : (4:ℝ)≤x t := le_trans (by exact_mod_cast hn) hx
  rw [(sq_components t).1]
  nlinarith [height_bound ht, pow_le_pow_left₀ (Nat.cast_nonneg n) hx 2,
    mul_nonneg (sub_nonneg.mpr h4) (show 0≤x t by linarith)]

open scoped ComplexConjugate
open MeasureTheory Set

/-- Dottie's squared root once, and each of the two squared roots from every
nonunit quartet once. Index zero in a natural-number branch means level one. -/
def family (d : ℝ) (t : ℕ → ℝ) : Unit ⊕ (ℕ ⊕ ℕ) → ℂ :=
  Sum.elim (fun _ => ((d^2:ℝ):ℂ)) (Sum.elim (fun n => u (t n)^2) (fun n => conj (u (t n)^2)))

private lemma join_sums {α β : Type*} (f : α ⊕ β → ℝ)
    (h : Summable (f ∘ Sum.inl)) (k : Summable (f ∘ Sum.inr)) : Summable f :=
  (HasSum.sum (f:=f) h.hasSum k.hasSum).summable

/-- The countable Stieltjes formula instantiated on both conjugate branches
and the positive distinguished square. This step only needs positivity of d. -/
theorem indexed_stieltjes {d : ℝ} (hd : 0<d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ level (t n)=2*π*(n+1))
    {s : ℂ} (hs : 1/2<s.re) (hs' : s.re<1) :
    HasSum (fun j => (family d t j)^(-s))
      (Complex.sin ((π:ℂ)*s)/(π:ℂ)*
        ∫ r in Ioi (0:ℝ), (r:ℂ)^(-s)*(∑' j, ((r:ℂ)+family d t j)⁻¹)) := by
  have pos (n : ℕ) := squared_off_cut (Nat.succ_pos n) (roots n).1 (by simpa using (roots n).2)
  have margin (n : ℕ) := resolvent_margin (Nat.succ_pos n) (roots n).1 (by simpa using (roots n).2)
  have hpos : 0<d^2 := by positivity
  apply Stieltjes.countable_slit _ _ (by linarith) hs' (d:=1/2) (by norm_num)
  · rintro (_ | n | n) r hr
    · change 1/2*(r+‖((d^2:ℝ):ℂ)‖) ≤ ‖(r:ℂ)+((d^2:ℝ):ℂ)‖
      rw [Complex.norm_of_nonneg hpos.le, ← ofReal_add, Complex.norm_of_nonneg (by positivity)]
      linarith
    · exact margin n r hr
    · change 1/2*(r+‖conj (u (t n)^2)‖) ≤ ‖(r:ℂ)+conj (u (t n)^2)‖
      rw [← Complex.conj_ofReal r, ←map_add, Complex.norm_conj, Complex.norm_conj]
      exact margin n r hr
  · have h := norm_series (fun n => (roots n).2) hs
    refine join_sums _ (hasSum_fintype _).summable ?_
    refine join_sums _ ?_ ?_
    · exact h
    · change Summable (fun n => ‖conj (u (t n)^2)‖^(-s.re))
      simpa only [Complex.norm_conj] using h
  · rintro (_ | n | n)
    · left; exact hpos
    · exact pos n
    · rcases pos n with h | h
      · left; exact h
      · right
        change (conj (u (t n)^2)).im ≠ 0
        simpa only [Complex.conj_im, neg_ne_zero] using h

end
end SuperZeta.RootBounds
