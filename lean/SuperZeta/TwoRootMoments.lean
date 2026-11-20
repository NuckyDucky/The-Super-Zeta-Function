import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! First and second power sums of an unordered pair of zeros counted with
multiplicity. Reflection invariance and continuity of the power sums are
explicit hypotheses. Evaluating power sums by contour integration is separate. -/

namespace SuperZeta.TwoRootMoments
noncomputable section

/-- The squared full gap expressed in the first two power sums. -/
noncomputable def discriminant (s₁ s₂ : ℂ) : ℂ := 2 * s₂ - s₁ ^ 2

theorem discriminant_eq (x y : ℂ) :
    discriminant (x+y) (x^2+y^2) = (x-y)^2 := by unfold discriminant; ring

theorem squared_half_gap (x y : ℂ) :
    ((x-y)/2)^2 = discriminant (x+y) (x^2+y^2)/4 := by rw [discriminant_eq]; ring

theorem quadratic_from_moments (x y z : ℂ) :
    z^2 - (x+y)*z + ((x+y)^2 - (x^2+y^2))/2 = (z-x)*(z-y) := by ring

/-- The quadratic reconstructed from two moments determines both entries up to exchange. -/
theorem moments_determine_pair {x y u v : ℂ} (h₁ : x+y = u+v) (h₂ : x^2+y^2 = u^2+v^2) :
    (x=u ∧ y=v) ∨ (x=v ∧ y=u) := by
  have hx : (x-u)*(x-v)=0 := by
    rw [← quadratic_from_moments, ← h₁, ← h₂, quadratic_from_moments]
    simp
  rcases mul_eq_zero.mp hx with h | h
  · obtain rfl := sub_eq_zero.mp h
    exact Or.inl ⟨rfl, add_left_cancel h₁⟩
  · obtain rfl := sub_eq_zero.mp h
    rw [add_comm u x] at h₁
    exact Or.inr ⟨rfl, add_left_cancel h₁⟩

/-- Reflection in the Riemann critical line. -/
noncomputable def reflect (z : ℂ) : ℂ := 1 - star z

private theorem reflect_twice (z : ℂ) : reflect (reflect z) = z := by simp [reflect]

theorem reflect_fixed_iff (z : ℂ) : reflect z = z ↔ z.re = 1 / 2 := by
  constructor
  · intro h
    have h' := congrArg Complex.re h
    simp [reflect, Complex.star_def] at h'
    linarith
  · intro h
    apply Complex.ext <;> norm_num [reflect, Complex.star_def, h]

/-- The underlying set maps into itself. Repeated entries are counted twice in the moments. -/
def ReflectionInvariant (x y : ℂ) : Prop := Set.MapsTo reflect {x, y} {x, y}

theorem fixed_or_exchanged {x y : ℂ} (h : ReflectionInvariant x y) :
    (reflect x = x ∧ reflect y = y) ∨ (reflect x = y ∧ reflect y = x) := by
  have hx : reflect x = x ∨ reflect x = y := by simpa using h (by simp : x ∈ ({x, y} : Set ℂ))
  have hy : reflect y = x ∨ reflect y = y := by simpa using h (by simp : y ∈ ({x, y} : Set ℂ))
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · have hxy := congrArg reflect hy
      rw [reflect_twice, hx] at hxy
      exact Or.inl ⟨hx, hy.trans hxy.symm⟩
    · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, by rw [← hx, reflect_twice]⟩

private theorem gap_components (x y : ℂ) :
    (discriminant (x+y) (x^2+y^2)).re = (x.re-y.re)^2 - (x.im-y.im)^2 ∧
    (discriminant (x+y) (x^2+y^2)).im = 2*(x.re-y.re)*(x.im-y.im) := by
  rw [discriminant_eq]
  constructor
  · simp [pow_two, Complex.mul_re]
  · simp [pow_two, Complex.mul_im]
    ring

private theorem exchanged_coords {x y : ℂ} (h : reflect x = y) :
    y.re = 1-x.re ∧ y.im = x.im := by
  rw [← h]
  simp [reflect, Complex.star_def]

theorem discriminant_real {x y : ℂ} (h : ReflectionInvariant x y) :
    (discriminant (x+y) (x^2+y^2)).im = 0 := by
  rw [(gap_components x y).2]
  rcases fixed_or_exchanged h with ⟨hx, hy⟩ | ⟨hx, _⟩
  · rw [(reflect_fixed_iff x).1 hx, (reflect_fixed_iff y).1 hy]
    ring
  · rw [(exchanged_coords hx).2]
    ring

theorem discriminant_pos_iff {x y : ℂ} (h : ReflectionInvariant x y) :
    0 < (discriminant (x+y) (x^2+y^2)).re ↔ x.im = y.im ∧ x.re ≠ y.re := by
  rw [(gap_components x y).1]
  constructor
  · intro hp
    rcases fixed_or_exchanged h with ⟨hx, hy⟩ | ⟨hx, _⟩
    · rw [(reflect_fixed_iff x).1 hx, (reflect_fixed_iff y).1 hy] at hp
      nlinarith [sq_nonneg (x.im-y.im)]
    · refine ⟨(exchanged_coords hx).2.symm, ?_⟩
      intro e
      rw [e] at hp
      nlinarith [sq_nonneg (x.im-y.im)]
  · rintro ⟨hi, hr⟩
    rw [hi, sub_self, zero_pow (by decide : 2 ≠ 0), sub_zero]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hr)

theorem discriminant_neg_iff {x y : ℂ} (h : ReflectionInvariant x y) :
    (discriminant (x+y) (x^2+y^2)).re < 0 ↔
      x.re = 1/2 ∧ y.re = 1/2 ∧ x.im ≠ y.im := by
  rw [(gap_components x y).1]
  constructor
  · intro hn
    rcases fixed_or_exchanged h with ⟨hx, hy⟩ | ⟨hx, _⟩
    · refine ⟨(reflect_fixed_iff x).1 hx, (reflect_fixed_iff y).1 hy, ?_⟩
      intro e
      rw [e] at hn
      nlinarith [sq_nonneg (x.re-y.re)]
    · rw [(exchanged_coords hx).2] at hn
      nlinarith [sq_nonneg (x.re-y.re)]
  · rintro ⟨hx, hy, hi⟩
    rw [hx, hy]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hi)]

theorem discriminant_zero_iff {x y : ℂ} (h : ReflectionInvariant x y) :
    (discriminant (x+y) (x^2+y^2)).re = 0 ↔ x=y := by
  constructor
  · intro hr
    have hz : discriminant (x+y) (x^2+y^2) = 0 := Complex.ext hr (discriminant_real h)
    rwa [discriminant_eq, sq_eq_zero_iff, sub_eq_zero] at hz
  · rintro rfl
    simp [discriminant_eq]

/-- The two zeros need no continuous ordering. A change of sign in the real
discriminant of continuous moments forces a repeated critical-line zero. -/
theorem sign_change_forces_collision {a b : ℝ} (hab : a ≤ b)
    (s₁ s₂ : ℝ → ℂ) (h₁ : ContinuousOn s₁ (Set.Icc a b)) (h₂ : ContinuousOn s₂ (Set.Icc a b))
    (roots : ∀ t ∈ Set.Icc a b, ∃ x y : ℂ, ReflectionInvariant x y ∧
      s₁ t = x+y ∧ s₂ t = x^2+y^2)
    (hopposite : (discriminant (s₁ a) (s₂ a)).re * (discriminant (s₁ b) (s₂ b)).re < 0) :
    ∃ t ∈ Set.Ioo a b, ∃ z : ℂ, z.re = 1/2 ∧ s₁ t = z+z ∧ s₂ t = z^2+z^2 := by
  let d := fun t => (discriminant (s₁ t) (s₂ t)).re
  have hd : ContinuousOn d (Set.Icc a b) :=
    Complex.continuous_re.comp_continuousOn ((continuousOn_const.mul h₂).sub (h₁.pow 2))
  change d a * d b < 0 at hopposite
  have him : (0 : ℝ) ∈ d '' Set.Icc a b := by
    rcases mul_neg_iff.mp hopposite with h | h
    all_goals first | exact intermediate_value_Icc hab hd ⟨h.1.le, h.2.le⟩
                    | exact intermediate_value_Icc' hab hd ⟨h.2.le, h.1.le⟩
  obtain ⟨t, ht, hzero⟩ := him
  have ht' : t ∈ Set.Ioo a b := by
    refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩ <;>
      intro he <;> subst t <;> simp [hzero] at hopposite
  obtain ⟨x, y, hr, hs, hq⟩ := roots t ht
  change (discriminant (s₁ t) (s₂ t)).re = 0 at hzero
  rw [hs, hq] at hzero
  obtain rfl := (discriminant_zero_iff hr).1 hzero
  obtain hh | hh := fixed_or_exchanged hr
  all_goals exact ⟨t, ht', x, (reflect_fixed_iff x).1 hh.1, hs, hq⟩

/-- A positive real part is preserved on taking a complex reciprocal. -/
theorem reciprocal_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < z⁻¹.re := by
  have hn : z ≠ 0 := by intro h; simp [h] at hz
  rw [Complex.inv_re]
  exact div_pos hz (Complex.normSq_pos.mpr hn)

end
end SuperZeta.TwoRootMoments
