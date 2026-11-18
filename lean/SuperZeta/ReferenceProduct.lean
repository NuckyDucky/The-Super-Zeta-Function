import SuperZeta.Reference
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Recover the reference cosine product on the positive spectral ray from Euler's sine product. -/
noncomputable section
namespace SuperZeta.Reference
open Complex Filter
open scoped Topology

private def factor (a : ℝ) (n : ℕ) := 1+a^2/((n:ℝ)+1)^2

private theorem increments (a : ℝ) : Summable (fun n : ℕ => a^2/((n:ℝ)+1)^2) := by
  have h := (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).comp_injective Nat.succ_injective
  simpa [Function.comp_def,div_eq_mul_inv] using h.mul_left (a^2)

private theorem full_product {a : ℝ} (ha : a ≠ 0) :
    HasProd (factor a) (Real.sinh (Real.pi*a)/(Real.pi*a)) := by
  have h := Complex.tendsto_euler_sin_prod ((a:ℂ)*I)
  have hm (j : ℕ) : (1:ℂ)-((a:ℂ)*I)^2/((j:ℂ)+1)^2 = (factor a j:ℂ) := by
    unfold factor
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  simp_rw [hm] at h
  have hpre := (Complex.continuous_im.tendsto _).comp h
  have hreal : Tendsto (fun n : ℕ => (Real.pi*a)*∏ j ∈ Finset.range n, factor a j)
      atTop (𝓝 (Real.sinh (Real.pi*a))) := by
    simpa [Function.comp_def, ← Complex.ofReal_prod, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.sin_mul_I, ← Complex.ofReal_sinh, Complex.mul_im, Complex.mul_re] using hpre
  have h0 : Real.pi*a ≠ 0 := mul_ne_zero Real.pi_ne_zero ha
  apply (Multipliable.hasProd_iff_tendsto_nat (Real.multipliable_one_add_of_summable (increments a))).mpr
  simpa [h0] using hreal.div_const (Real.pi*a)

/-- Product over the positive squared roots, once each. Squaring gives
the determinant with its reference multiplicities. -/
theorem reference_ray_product (x : ℝ) :
    HasProd (fun n : ℕ => 1+x^2/eigenvalue n) (Real.cosh x) := by
  by_cases hx : x = 0
  · subst x; simpa using (hasProd_one : HasProd (fun _ : ℕ => (1:ℝ)) 1)
  let a := x/Real.pi
  have hxpi : Real.pi*a = x := by dsimp [a]; field_simp
  have ha : a ≠ 0 := div_ne_zero hx Real.pi_ne_zero
  have hdouble := full_product (a:=2*a) (mul_ne_zero (by norm_num) ha)
  have hsingle := full_product ha
  have ho (k : ℕ) : factor (2*a) (2*k+1) = factor a k := by
    unfold factor; push_cast; ring_nf; field_simp; ring
  have he (k : ℕ) : factor (2*a) (2*k) = 1+x^2/eigenvalue k := by
    unfold factor eigenvalue; dsimp [a]; push_cast
    field_simp [Real.pi_ne_zero, show (2:ℝ)*k+1 ≠ 0 by positivity,
      show (k:ℝ)+1/2 ≠ 0 by positivity]
    ring
  have ev : Multipliable fun k : ℕ => factor (2*a) (2*k) :=
    Real.multipliable_one_add_of_summable ((increments (2*a)).comp_injective (by intro i j h; omega))
  have odd : HasProd (fun k : ℕ => factor (2*a) (2*k+1)) (Real.sinh (Real.pi*a)/(Real.pi*a)) := by
    simpa only [ho] using hsingle
  have hv := (ev.hasProd.even_mul_odd odd).unique hdouble
  have h2 : Real.pi*(2*a)=2*x := by rw [← hxpi]; ring
  rw [hxpi,h2,Real.sinh_two_mul] at hv
  have hs : Real.sinh x ≠ 0 := by simpa using hx
  have key : ∏' k : ℕ, factor (2*a) (2*k) = Real.cosh x := by
    field_simp [hx] at hv
    apply mul_right_cancel₀ (mul_ne_zero hs hx)
    linarith only [show (∏' k : ℕ, factor (2*a) (2*k))*(Real.sinh x*x)*2 = Real.cosh x*(Real.sinh x*x)*2 by linear_combination hv]
  have result := ev.hasProd
  rw [key] at result
  simpa only [he] using result

end SuperZeta.Reference
