import QuarticGridTail

open Set

namespace QuarticGrid

noncomputable def expPoly (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 10, y^i / i.factorial

noncomputable def expLo (m : ℕ) (y : ℝ) : ℝ := (2.718281828:ℝ)^m * expPoly y
noncomputable def expHi (m : ℕ) (y : ℝ) : ℝ :=
  (2.718281829:ℝ)^m * (expPoly y + (11:ℝ)/36288000)

theorem exp_bounds (m : ℕ) {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 1) :
    expLo m y ≤ Real.exp ((m:ℝ)+y) ∧ Real.exp ((m:ℝ)+y) ≤ expHi m y := by
  have hL := Real.sum_le_exp_of_nonneg hy 10
  have hU := Real.exp_bound' hy hy' (show (0:ℕ)<10 by decide)
  have hp : y^10 ≤ 1 := by simpa using pow_le_pow_left₀ hy hy' 10
  have hs : expPoly y ≤ Real.exp y ∧ Real.exp y ≤ expPoly y + 11/36288000 := by
    constructor
    · exact hL
    · norm_num [Nat.factorial] at hU
      unfold expPoly
      linarith
  have hpn : 0 ≤ expPoly y := Finset.sum_nonneg (fun _ _ => by positivity)
  have hlow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.718281828)
    (by linarith [Real.exp_one_gt_d9] : (2.718281828:ℝ) ≤ Real.exp 1) m
  have hhigh := pow_le_pow_left₀ (Real.exp_pos 1).le
    (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ (2.718281829:ℝ)) m
  rw [Real.exp_add, show Real.exp (m:ℝ) = Real.exp 1^m by rw [← Real.exp_nat_mul,mul_one]]
  constructor
  · exact mul_le_mul hlow hs.1 hpn (pow_nonneg (Real.exp_pos 1).le _)
  · exact mul_le_mul hhigh hs.2 (Real.exp_pos _).le (by positivity)

theorem scale_bounds : (1638902 : ℝ) < QuarticKernel.scale ∧ QuarticKernel.scale < 1638903 := by
  have hD : (26509772707289:ℝ) = QuarticKernel.conductorNorm := by
    norm_num [QuarticKernel.conductorNorm]
  have hs : (5148764 : ℝ) < Real.sqrt (QuarticKernel.conductorNorm:ℝ) ∧
      Real.sqrt (QuarticKernel.conductorNorm:ℝ) < (5148765 : ℝ) := by
    rw [← hD]
    constructor
    · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_lt (by norm_num : (0:ℝ) ≤ 26509772707289)
        (by norm_num : (0:ℝ) ≤ 5148765)).2 (by norm_num)
  unfold QuarticKernel.scale
  refine ⟨(lt_div_iff₀ Real.pi_pos).2 ?_,(div_lt_iff₀ Real.pi_pos).2 ?_⟩
  · linarith [hs.1, Real.pi_lt_d20]
  · linarith [hs.2, Real.pi_gt_d20]

private theorem theta_first_term_ratio {u q e : ℝ} (hu : 0 < u)
    (hq : q < 1) (hrq : Real.exp (-u) ≤ q)
    (he : 0 ≤ e) (hb : 1 ≤ (1+e)*(1-q)^2) :
    (1-e)*Real.exp (-u) ≤ QuarticKernel.theta u ∧
      QuarticKernel.theta u ≤ (1+e)*Real.exp (-u) := by
  let r := Real.exp (-u)
  have hr : 0 < r := Real.exp_pos _
  have hsq : (1-q)^2 ≤ (1-r)^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hq.le) (sub_le_sub_left hrq _) 2
  have hs := hb.trans (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 1+e))
  have hbr : r/(1-r)^2 ≤ (1+e)*r := by
    apply (div_le_iff₀ (pow_pos (sub_pos.mpr (hrq.trans_lt hq)) 2)).2
    nlinarith only [mul_le_mul_of_nonneg_right hs hr.le]
  have ht := abs_le.mp (QuarticKernel.theta_first_term hu)
  change -(r/(1-r)^2-r) ≤ _ ∧ _ ≤ r/(1-r)^2-r at ht
  change (1-e)*r ≤ _ ∧ _ ≤ (1+e)*r
  constructor <;> linarith only [hbr,ht.1,ht.2]

theorem pointwise_from_gap {x dlo dhi q e : ℝ} (hu : 0 < Real.exp x / QuarticKernel.scale)
    (hq : q < 1) (hrq : Real.exp (-(Real.exp x / QuarticKernel.scale)) ≤ q)
    (he : 0 ≤ e) (he' : e ≤ 1) (hb : 1 ≤ (1+e)*(1-q)^2)
    (hlo : dlo ≤ Real.exp x / QuarticKernel.scale - x/2)
    (hhi : Real.exp x / QuarticKernel.scale - x/2 ≤ dhi) :
    (1-e)/Real.exp dhi ≤ QuarticKernel.kernel x ∧
      QuarticKernel.kernel x ≤ (1+e)/Real.exp dlo := by
  let u := Real.exp x / QuarticKernel.scale
  have hθ := theta_first_term_ratio hu hq hrq he hb
  have hl := mul_le_mul_of_nonneg_left hθ.1 (Real.exp_pos (x/2)).le
  have hh := mul_le_mul_of_nonneg_left hθ.2 (Real.exp_pos (x/2)).le
  have hr (c : ℝ) :
      Real.exp (x/2)*(c*Real.exp (-u)) = c*Real.exp (-(u-x/2)) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  change Real.exp (x/2)*((1-e)*Real.exp (-u)) ≤ QuarticKernel.kernel x at hl
  change QuarticKernel.kernel x ≤ Real.exp (x/2)*((1+e)*Real.exp (-u)) at hh
  rw [hr] at hl hh
  simp only [Real.exp_neg, div_eq_mul_inv] at hl hh ⊢
  constructor
  · exact (mul_le_mul_of_nonneg_left ((inv_le_inv₀ (Real.exp_pos _) (Real.exp_pos _)).2
      (Real.exp_le_exp.mpr hhi)) (sub_nonneg.mpr he')).trans hl
  · exact hh.trans (mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ (Real.exp_pos _) (Real.exp_pos _)).2 (Real.exp_le_exp.mpr hlo)) (by positivity))

private theorem u_lower {x u : ℝ} (hu : 0 ≤ u) (ha : u*1638903 ≤ Real.exp x) :
    u ≤ Real.exp x/QuarticKernel.scale := by
  apply (le_div_iff₀ QuarticKernel.scale_pos).2
  exact (mul_le_mul_of_nonneg_left scale_bounds.2.le hu).trans ha

private theorem u_upper {x u : ℝ} (hu : 0 ≤ u) (ha : Real.exp x ≤ u*1638902) :
    Real.exp x/QuarticKernel.scale ≤ u := by
  apply (div_le_iff₀ QuarticKernel.scale_pos).2
  exact ha.trans (mul_le_mul_of_nonneg_left scale_bounds.1.le hu)

private theorem gap_mono {a b : ℝ} (hab : a ≤ b)
    (h : 1/2 ≤ Real.exp a/QuarticKernel.scale) :
    Real.exp a/QuarticKernel.scale-a/2 ≤ Real.exp b/QuarticKernel.scale-b/2 := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (b-a))
    (div_nonneg (Real.exp_pos a).le QuarticKernel.scale_pos.le)
  have ha : Real.exp (b-a)*(Real.exp a/QuarticKernel.scale) =
      Real.exp b/QuarticKernel.scale := by
    rw [← mul_div_assoc, ← Real.exp_add, show b-a+a=b by ring]
  rw [ha] at hh
  linarith [mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hab)]

/-- Check a cell using rational Taylor enclosures at its two endpoints. -/
theorem check_pointwise_cell {a b uLo uHi q e L U : ℝ}
    (hU0 : 0 ≤ uHi)
    (hu : 1/2 ≤ uLo) (hq : 0 < q) (hq' : q < 1) (he : 0 ≤ e) (he' : e ≤ 1)
    (hratio : 1 ≤ (1+e)*(1-q)^2)
    (hat : uLo*1638903 ≤ Real.exp a) (hbt : Real.exp b ≤ uHi*1638902)
    (hrat : q⁻¹ ≤ Real.exp uLo)
    (hLower : L*Real.exp (uHi-b/2) ≤ 1-e)
    (hUpper : 1+e ≤ U*Real.exp (uLo-a/2)) :
    ∀ x ∈ Icc a b, L ≤ QuarticKernel.kernel x ∧ QuarticKernel.kernel x ≤ U := by
  intro x hx
  have ha := u_lower (by linarith : 0 ≤ uLo) hat
  have hb := u_upper hU0 hbt
  have hx₀ : uLo ≤ Real.exp x/QuarticKernel.scale := ha.trans
    (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hx.1) QuarticKernel.scale_pos.le)
  have hqexp : Real.exp (-(Real.exp x/QuarticKernel.scale)) ≤ q := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hq]
    exact hrat.trans (Real.exp_le_exp.mpr hx₀)
  have hgl := (sub_le_sub_right ha _).trans (gap_mono hx.1 (hu.trans ha))
  have hgh := (gap_mono hx.2 (hu.trans hx₀)).trans (sub_le_sub_right hb _)
  have hK := pointwise_from_gap (div_pos (Real.exp_pos x) QuarticKernel.scale_pos)
    hq' hqexp he he' hratio hgl hgh
  exact ⟨((le_div_iff₀ (Real.exp_pos _)).2 hLower).trans hK.1,
    hK.2.trans ((div_le_iff₀ (Real.exp_pos _)).2 hUpper)⟩

#print axioms exp_bounds
#print axioms scale_bounds
#print axioms pointwise_from_gap
#print axioms check_pointwise_cell

end QuarticGrid
