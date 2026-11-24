import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Sublinear logarithmic growth of the determinant on exhausting circles. -/
namespace SuperZeta.Factorization
open Filter
open scoped Topology

theorem growth_lt {R : ℝ} (h : 0<R) :
    Real.exp (2*Real.sqrt R)+R < Real.exp (2*Real.sqrt R+2) := by
  have hs := Real.sqrt_nonneg R
  have hsq := Real.sq_sqrt h.le
  have base : Real.sqrt R ≤ Real.exp (Real.sqrt R) := (Real.add_one_le_exp _).trans' (by linarith)
  have hle : R ≤ Real.exp (2*Real.sqrt R) := by
    rw [two_mul,Real.exp_add]
    nlinarith [mul_self_le_mul_self hs base]
  rw [Real.exp_add]
  have htwo := Real.add_one_le_exp (2:ℝ)
  nlinarith [Real.exp_pos (2*Real.sqrt R),
    mul_pos (Real.exp_pos (2*Real.sqrt R)) (show 0 < Real.exp 2-2 by linarith)]

theorem log_bound_tendsto {R : ℕ → ℝ} (hR : ∀ k, 0<R k) (htop : Tendsto R atTop atTop)
    (a : ℝ) :
    Tendsto (fun k => 2*(2*Real.sqrt (R k)+2)*a/(R k/2-a)) atTop (𝓝 0) := by
  have ht : Tendsto (fun k => (R k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hsqt : Tendsto Real.sqrt atTop atTop := by
    change Tendsto (fun x => Real.sqrt x) atTop atTop
    simpa only [Real.sqrt_eq_rpow] using (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2))
  have hst : Tendsto (fun k => (Real.sqrt (R k))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (hsqt.comp htop)
  have hnum : Tendsto (fun k => 2*(2*(Real.sqrt (R k))⁻¹+2*(R k)⁻¹)*a) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hst).add
      (tendsto_const_nhds.mul ht))).mul (tendsto_const_nhds (x:=a))
  have hden : Tendsto (fun k => 1/2-a*(R k)⁻¹) atTop (𝓝 (1/2:ℝ)) := by
    simpa using (tendsto_const_nhds (x:=(1/2:ℝ))).sub ((tendsto_const_nhds (x:=a)).mul ht)
  apply (show Tendsto (fun k => (2*(2*(Real.sqrt (R k))⁻¹+2*(R k)⁻¹)*a) /
      (1/2-a*(R k)⁻¹)) atTop (𝓝 0) by
    simpa [Pi.div_def] using hnum.div hden (by norm_num : (1/2:ℝ)≠0)).congr
  intro k
  have hr := (hR k).ne'
  have hs := (Real.sqrt_pos.mpr (hR k)).ne'
  have hsq := Real.sq_sqrt (hR k).le
  have hn : (Real.sqrt (R k))⁻¹ = Real.sqrt (R k) * (R k)⁻¹ := by
    field_simp
    exact hsq.symm
  rw [hn]
  rw [show (1/2-a*(R k)⁻¹) = (R k/2-a)/(R k) by field_simp]
  rw [div_div_eq_mul_div]
  congr 1
  field_simp

end SuperZeta.Factorization
