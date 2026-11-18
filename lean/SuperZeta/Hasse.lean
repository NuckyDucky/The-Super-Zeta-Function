import SuperZeta.Meme
import Mathlib.Data.Rat.Lemmas

/-! The explicit rational two-covering and the squareclass exclusion for the
six-coefficient quartic. The global Mordell–Weil squareclass bound is a
hypothesis in the final implication. -/
namespace SuperZeta.Hasse

def quartic {R : Type*} [CommRing R] (x v : R) : R :=
  961000*x^4-1039740*x^3*v-1810543*x^2*v^2+644010*x*v^3+1813853*v^4

def coverK (x v : ℚ) : ℚ := 212505*x^2-666190*x*v+432252*v^2

def coverM (x v : ℚ) : ℚ :=
  529733615650*x^4-1561869979515*x^3*v+879427559295*x^2*v^2+
  1338999985416*x*v^3-1347558035330*v^4

def OnCubic (X z : ℚ) : Prop := z^2 = X^3+5028677*X^2-305545084240*X

theorem affine_discriminant (x : ℝ) :
    quartic x 1 = Meme.discriminant (Meme.numerator x) (Meme.denominator x) := by
  rw [Meme.coefficient_quartic]
  simp [quartic]

theorem real_point : ∃ y : ℝ, y^2 = quartic (0:ℝ) 1 := by
  exact ⟨Real.sqrt _, Real.sq_sqrt (by norm_num [quartic])⟩

theorem cover_identity (x v : ℚ) :
    -16*(coverK x v)^4 + 4*5028677*(coverK x v)^2*quartic x v +
      305545084240*(quartic x v)^2 = 4*(coverM x v)^2 := by
  unfold coverK coverM quartic
  ring

private theorem no_zero_height {x v y : ℚ} (hn : x ≠ 0 ∨ v ≠ 0)
    (h : y^2 = quartic x v) : y ≠ 0 := by
  intro hy
  let N := 465*x^2-183*x*v-659*v^2
  let D := 155*x^2+396*x*v-936*v^2
  have hnorm : quartic x v = (N-D)^2 + 4*N^2 := by
    dsimp only [quartic,N,D]
    ring
  rw [hy, zero_pow (by decide), hnorm] at h
  have hN : N = 0 := by nlinarith [sq_nonneg (N-D), sq_nonneg N]
  have hD : D = 0 := by rw [hN] at h; nlinarith [sq_nonneg D]
  have rel : v*(2149*v-1371*x) = 0 := by
    dsimp only [N,D] at hN hD
    linear_combination hN-3*hD
  rcases mul_eq_zero.mp rel with hv | he
  · subst v
    dsimp only [N] at hN
    have hx : x = 0 := by nlinarith [sq_nonneg x]
    simp [hx] at hn
  · have hx : x = (2149/1371)*v := by linarith
    dsimp only [D] at hD
    rw [hx] at hD
    have hv : v = 0 := by nlinarith [sq_nonneg v]
    simp [hx,hv] at hn

private theorem nonsquare_between {t n : ℕ} (hl : t*t<n) (hu : n<(t+1)*(t+1)) :
    ¬ IsSquare (n:ℚ) := by
  rw [Rat.isSquare_natCast_iff]
  rintro ⟨r,rfl⟩
  by_cases h : r ≤ t
  · exact (not_le_of_gt hl) (Nat.mul_le_mul h h)
  · exact (not_le_of_gt hu) (Nat.mul_le_mul (by omega) (by omega))

private theorem coverK_ne_zero {x v : ℚ} (hn : x ≠ 0 ∨ v ≠ 0) : coverK x v ≠ 0 := by
  intro hk
  by_cases hv : v = 0
  · subst v
    simp [coverK] at hk
    simp [hk] at hn
  have hdisc : (425010*x-666190*v)^2 = 76386271060*v^2 := by
    unfold coverK at hk
    linear_combination 850020*hk
  have hs : IsSquare (76386271060:ℚ) := by
    refine ⟨(425010*x-666190*v)/v, ?_⟩
    field_simp
    linear_combination -hdisc
  exact nonsquare_between (t:=276380) (n:=76386271060) (by decide) (by decide) hs

/-- Any rational projective solution to the quartic produces a rational
cubic point whose nonzero abscissa has squareclass minus one. -/
theorem quartic_forces_negative_square {x v y : ℚ} (hn : x ≠ 0 ∨ v ≠ 0)
    (h : y^2 = quartic x v) :
    ∃ X z r : ℚ, OnCubic X z ∧ r ≠ 0 ∧ X = -r^2 := by
  have hy := no_zero_height hn h
  have hk := coverK_ne_zero hn
  let k := coverK x v
  let m := coverM x v
  have hc := cover_identity x v
  rw [← h] at hc
  change -16*k^4+4*5028677*k^2*y^2+305545084240*(y^2)^2 = 4*m^2 at hc
  refine ⟨-4*k^2/y^2, 4*k*m/y^3, 2*k/y, ?_, div_ne_zero (mul_ne_zero (by norm_num) hk) hy, ?_⟩
  · unfold OnCubic
    field_simp
    linear_combination -4*k^2*y^12*hc
  · ring

/-- The two negative classes of the descent table exclude a negative square. -/
private theorem negative_class_exclusion {a r c : ℚ}
    (ha : ¬ IsSquare a) (hr : r ≠ 0) (h : -r^2 = -a*c^2) : False := by
  have hc : c ≠ 0 := by rintro rfl; simp [hr] at h
  apply ha
  refine ⟨r/c, ?_⟩
  field_simp
  linarith only [h]

/-- A conditional reduction of global pointlessness to the four-squareclass
containment supplied by arithmetic descent. -/
theorem obstructed_by_four_classes
    (classes : ∀ X z : ℚ, OnCubic X z → X ≠ 0 → ∃ c : ℚ,
      X = c^2 ∨ X = 115*c^2 ∨ X = -19096567765*c^2 ∨ X = -166057111*c^2)
    {x v y : ℚ} (hn : x ≠ 0 ∨ v ≠ 0) : y^2 ≠ quartic x v := by
  intro h
  obtain ⟨X,z,r,onE,hr,rfl⟩ := quartic_forces_negative_square hn h
  obtain ⟨c,hc|hc|hc|hc⟩ := classes _ _ onE (neg_ne_zero.mpr (pow_ne_zero 2 hr))
  · nlinarith [sq_pos_of_ne_zero hr, sq_nonneg c]
  · nlinarith [sq_pos_of_ne_zero hr, sq_nonneg c]
  · exact negative_class_exclusion
      (nonsquare_between (t:=138190) (n:=19096567765) (by decide) (by decide)) hr hc
  · exact negative_class_exclusion
      (nonsquare_between (t:=12886) (n:=166057111) (by decide) (by decide)) hr hc

end SuperZeta.Hasse
