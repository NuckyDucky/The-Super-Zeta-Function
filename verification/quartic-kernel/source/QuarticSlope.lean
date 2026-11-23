import GaussianSideIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set
namespace QuarticSlope

noncomputable section

set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

private theorem error_nonneg {f g : ℝ → ℝ} (h0 : f 0 = 0)
    (hd : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, 0 ≤ x → 0 ≤ g x)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hc : Differentiable ℝ f := fun y => (hd y).differentiableAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0:ℝ)) hc.continuous.continuousOn
    hc.differentiableOn (fun y hy => by rw [(hd y).deriv]; exact hg y (interior_subset hy))
  simpa only [h0] using hm (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr (le_refl _)) hx hx

private def err1 (x : ℝ) : ℝ := (x) - Real.sin x
private theorem err1_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err1 x := by
  apply error_nonneg (g := fun y => 1 - Real.cos y)
  · norm_num [err1]
  · intro x
    unfold err1
    exact (hasDerivAt_id x).sub (Real.hasDerivAt_sin x)
  · exact fun y _ => sub_nonneg.mpr (Real.cos_le_one y)
  · exact hx

private def err2 (x : ℝ) : ℝ := Real.cos x - (1 - x^2/2)
private theorem err2_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err2 x := by
  apply error_nonneg (g := err1)
  · norm_num [err2]
  · intro x
    unfold err2 err1
    convert (Real.hasDerivAt_cos x).sub ((hasDerivAt_const x (1:ℝ)).sub (((hasDerivAt_id x).pow 2).div_const 2)) using 1 <;> simp [id] <;> ring
  · exact err1_nonneg
  · exact hx

private def err3 (x : ℝ) : ℝ := Real.sin x - (x - x^3/6)
private theorem err3_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err3 x := by
  apply error_nonneg (g := err2)
  · norm_num [err3]
  · intro x
    unfold err3 err2
    convert (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 6)) using 1 <;> simp [id] <;> ring
  · exact err2_nonneg
  · exact hx

private def err4 (x : ℝ) : ℝ := (1 - x^2/2 + x^4/24) - Real.cos x
private theorem err4_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err4 x := by
  apply error_nonneg (g := err3)
  · norm_num [err4]
  · intro x
    unfold err4 err3
    convert (((hasDerivAt_const x (1:ℝ)).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 4).div_const 24)).sub (Real.hasDerivAt_cos x) using 1 <;> simp [id] <;> ring
  · exact err3_nonneg
  · exact hx

private def err5 (x : ℝ) : ℝ := (x - x^3/6 + x^5/120) - Real.sin x
private theorem err5_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err5 x := by
  apply error_nonneg (g := err4)
  · norm_num [err5]
  · intro x
    unfold err5 err4
    convert (((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 6)).add (((hasDerivAt_id x).pow 5).div_const 120)).sub (Real.hasDerivAt_sin x) using 1 <;> simp [id] <;> ring
  · exact err4_nonneg
  · exact hx

private def err6 (x : ℝ) : ℝ := Real.cos x - (1 - x^2/2 + x^4/24 - x^6/720)
private theorem err6_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err6 x := by
  apply error_nonneg (g := err5)
  · norm_num [err6]
  · intro x
    unfold err6 err5
    convert (Real.hasDerivAt_cos x).sub ((((hasDerivAt_const x (1:ℝ)).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 4).div_const 24)).sub (((hasDerivAt_id x).pow 6).div_const 720)) using 1 <;> simp [id] <;> ring
  · exact err5_nonneg
  · exact hx

private def err7 (x : ℝ) : ℝ := Real.sin x - (x - x^3/6 + x^5/120 - x^7/5040)
private theorem err7_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err7 x := by
  apply error_nonneg (g := err6)
  · norm_num [err7]
  · intro x
    unfold err7 err6
    convert (Real.hasDerivAt_sin x).sub ((((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 6)).add (((hasDerivAt_id x).pow 5).div_const 120)).sub (((hasDerivAt_id x).pow 7).div_const 5040)) using 1 <;> simp [id] <;> ring
  · exact err6_nonneg
  · exact hx

private def err8 (x : ℝ) : ℝ := (1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320) - Real.cos x
private theorem err8_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err8 x := by
  apply error_nonneg (g := err7)
  · norm_num [err8]
  · intro x
    unfold err8 err7
    convert (((((hasDerivAt_const x (1:ℝ)).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 4).div_const 24)).sub (((hasDerivAt_id x).pow 6).div_const 720)).add (((hasDerivAt_id x).pow 8).div_const 40320)).sub (Real.hasDerivAt_cos x) using 1 <;> simp [id] <;> ring
  · exact err7_nonneg
  · exact hx

private def err9 (x : ℝ) : ℝ := (x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880) - Real.sin x
private theorem err9_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err9 x := by
  apply error_nonneg (g := err8)
  · norm_num [err9]
  · intro x
    unfold err9 err8
    convert (((((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 6)).add (((hasDerivAt_id x).pow 5).div_const 120)).sub (((hasDerivAt_id x).pow 7).div_const 5040)).add (((hasDerivAt_id x).pow 9).div_const 362880)).sub (Real.hasDerivAt_sin x) using 1 <;> simp [id] <;> ring
  · exact err8_nonneg
  · exact hx

private def err10 (x : ℝ) : ℝ := Real.cos x - (1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 - x^10/3628800)
private theorem err10_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err10 x := by
  apply error_nonneg (g := err9)
  · norm_num [err10]
  · intro x
    unfold err10 err9
    convert (Real.hasDerivAt_cos x).sub ((((((hasDerivAt_const x (1:ℝ)).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 4).div_const 24)).sub (((hasDerivAt_id x).pow 6).div_const 720)).add (((hasDerivAt_id x).pow 8).div_const 40320)).sub (((hasDerivAt_id x).pow 10).div_const 3628800)) using 1 <;> simp [id] <;> ring
  · exact err9_nonneg
  · exact hx

private def err11 (x : ℝ) : ℝ := Real.sin x - (x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800)
private theorem err11_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ err11 x := by
  apply error_nonneg (g := err10)
  · norm_num [err11]
  · intro x
    unfold err11 err10
    convert (Real.hasDerivAt_sin x).sub ((((((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 6)).add (((hasDerivAt_id x).pow 5).div_const 120)).sub (((hasDerivAt_id x).pow 7).div_const 5040)).add (((hasDerivAt_id x).pow 9).div_const 362880)).sub (((hasDerivAt_id x).pow 11).div_const 39916800)) using 1 <;> simp [id] <;> ring
  · exact err10_nonneg
  · exact hx


def lowerPoly (x : ℝ) : ℝ :=
  1 - x^2/6 + x^4/120 - x^6/5040 + x^8/362880 - x^10/39916800

theorem poly_le_sinc {x : ℝ} (hx : 0 ≤ x) :
    lowerPoly x ≤ GaussianSideIntegral.sinc x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x
    norm_num [lowerPoly, GaussianSideIntegral.sinc]
  · rw [GaussianSideIntegral.sinc, if_neg h.ne']
    apply (le_div_iff₀ h).2
    have he := err11_nonneg x h.le
    unfold err11 at he
    unfold lowerPoly
    linarith only [he, show (1-x^2/6+x^4/120-x^6/5040+x^8/362880-x^10/39916800)*x =
      x-x^3/6+x^5/120-x^7/5040+x^9/362880-x^11/39916800 by ring]

theorem poly_antitone : AntitoneOn lowerPoly (Icc (0 : ℝ) 4) := by
  have hd (x : ℝ) : HasDerivAt lowerPoly
      (-x * (123264+32192*(16-x^2)+2064*(16-x^2)^2+24*(16-x^2)^3+(16-x^2)^4)/3991680) x := by
    unfold lowerPoly
    have h := hasDerivAt_id x
    convert (((((hasDerivAt_const x (1:ℝ)).sub ((h.pow 2).div_const 6)).add
      ((h.pow 4).div_const 120)).sub ((h.pow 6).div_const 5040)).add
      ((h.pow 8).div_const 362880)).sub ((h.pow 10).div_const 39916800) using 1 <;>
      simp [id] <;> ring
  have hh : Differentiable ℝ lowerPoly := fun x => (hd x).differentiableAt
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 4) hh.continuous.continuousOn
    hh.differentiableOn fun x hx => ?_
  rw [(hd x).deriv]
  have h := interior_subset hx
  have hx0 : 0 ≤ x := h.1
  have hx1 : x ≤ 4 := h.2
  have hx2 : 0 ≤ 16-x^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (show 0 ≤ 4+x by linarith)]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx0)
    (by positivity)) (by norm_num)

theorem sinc_abs (y : ℝ) : GaussianSideIntegral.sinc |y| = GaussianSideIntegral.sinc y := by
  by_cases h : 0 ≤ y
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]
    by_cases hn : y = 0
    · simp [hn]
    · simp [GaussianSideIntegral.sinc, hn, Real.sin_neg]

theorem uniform_sinc_lower (y Y : ℝ) (hy : |y| ≤ Y) :
    (if Y ≤ 4 then lowerPoly Y else -(1/4 : ℝ)) ≤ GaussianSideIntegral.sinc y := by
  rw [← sinc_abs y]
  by_cases hY : Y ≤ 4
  · rw [if_pos hY]
    refine (poly_antitone ⟨abs_nonneg y, hy.trans hY⟩ ⟨(abs_nonneg y).trans hy, hY⟩ hy).trans
      (poly_le_sinc (abs_nonneg y))
  · rw [if_neg hY]
    by_cases hx : |y| ≤ 4
    · have hp : -(1/4 : ℝ) ≤ lowerPoly 4 := by norm_num [lowerPoly]
      exact hp.trans ((poly_antitone ⟨abs_nonneg y,hx⟩ ⟨by norm_num,le_rfl⟩ hx).trans
        (poly_le_sinc (abs_nonneg y)))
    · have hy0 : 0 < |y| := lt_trans (by norm_num : (0:ℝ) < 4) (lt_of_not_ge hx)
      rw [GaussianSideIntegral.sinc, if_neg hy0.ne']
      apply (le_div_iff₀ hy0).2
      linarith [Real.neg_one_le_sin |y|, lt_of_not_ge hx]

#print axioms uniform_sinc_lower
end
end QuarticSlope
