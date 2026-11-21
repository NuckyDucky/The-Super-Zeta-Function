import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace ScaleAndShape

noncomputable def difference (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  a * f (x / a) - f x

theorem compose_scales (a b x : ℝ) (f : ℝ → ℝ) :
    difference (a * b) f x = a * difference b f (x / a) + difference a f x := by
  simp only [difference, div_div]
  ring

theorem any_linear_term (a c x : ℝ) (ha : a ≠ 0) :
    difference a (fun y => c * y) x = 0 := by
  unfold difference
  field_simp
  ring

theorem any_integer_scale (q : ℕ) (hq : 1 < q) (s : ℂ) (hs : s.re < 1) :
    (q : ℂ) ^ (1 - s) - 1 ≠ 0 := by
  intro he
  have h := congrArg norm (sub_eq_zero.mp he)
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < q), norm_one] at h
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have h' := Real.one_lt_rpow hq' (sub_pos.mpr hs)
  simpa using (ne_of_gt h') (by simpa using h)

theorem inverse_basis_on_unit_circle (z : ℂ) (hz : z * (starRingEnd ℂ) z = 1) :
    -1 / z = -(starRingEnd ℂ) z := by
  have h : z ≠ 0 := by intro h; simp [h] at hz
  apply (div_eq_iff h).2
  rw [neg_mul, mul_comm, hz]

#print axioms compose_scales
#print axioms any_linear_term
#print axioms any_integer_scale
#print axioms inverse_basis_on_unit_circle

end ScaleAndShape
