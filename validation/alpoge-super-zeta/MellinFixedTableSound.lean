import MellinFixedDensity
import MellinFixedTable
import MellinIntegerMoment

/-! Numerical enclosures at the exact quadrature coordinates. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.MellinFixed

open MellinInteger SuperZeta.CauchyPanelQuadrature

private theorem middle_range {i : Nat} (hl : 576 ≤ i) (hr : i < 2304) (j : Fin 25) :
    -23 ≤ (mellinPanelNode i j:ℝ) ∧ (mellinPanelNode i j:ℝ) ≤ 4 := by
  have hi : (576:ℝ) ≤ i := by exact_mod_cast hl
  have hi' : (i:ℝ) ≤ 2303 := by exact_mod_cast Nat.le_of_lt_succ hr
  have hn : |(node j:ℝ)| ≤ 1 := by exact_mod_cast (rule_certified.1 j).1
  obtain ⟨hL,hR⟩ := abs_le.mp hn
  norm_num [mellinPanelNode, mellinPanelCenter]
  exact ⟨by linarith only [hi,hL], by linarith only [hi',hR]⟩

theorem checkTableNode_correct {i : Nat} (hl : 576 ≤ i) (hr : i < 2304) (j : Fin 25)
    (h : checkTableNode i j.val = true) (b : Bool) :
    |finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ) -
      (sampleReading fixedColumns b i j:ℝ)| ≤ 1/10^14 := by
  let n := coordinateNumerator i j.val
  let v := (fixedColumns (i/64) j.val).getD (i%64) (0,0)
  have hh : checkDensity n v.1 v.2 = true := h
  have heq : (mellinPanelNode i j:ℝ) = (n:ℝ)/524288 := by
    rw [coordinate_eq]
    push_cast
    rfl
  have hb := middle_range hl hr j
  rw [heq] at hb
  have hu : |(n:ℝ)/524288| ≤ 128 := abs_le.mpr ⟨by linarith only [hb.1], by linarith only [hb.2]⟩
  have he4 : Real.exp 4 ≤ 128 := by
    have he1 : Real.exp 1 ≤ 3 := by linarith only [Real.exp_one_lt_d9]
    rw [show (4:ℝ) = ((4:ℕ):ℝ)*1 by norm_num, Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_pos _).le he1 _).trans (by norm_num)
  have he := (Real.exp_le_exp.mpr hb.2).trans he4
  have hs := checkDensity_correct n v.1 v.2 hu he hh
  rw [heq, sampleReading]
  push_cast
  cases b
  · simpa only [sampleAt, component, Bool.false_eq_true, if_false, v] using hs.1
  · simpa only [sampleAt, component, if_true, v] using hs.2

theorem checkTablePanel_correct {i : Nat} (hl : 576 ≤ i) (hr : i < 2304)
    (h : checkTablePanel i = true) (b : Bool) (j : Fin 25) :
    |finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ) -
      (sampleReading fixedColumns b i j:ℝ)| ≤ 1/10^14 :=
  checkTableNode_correct hl hr j
    (List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt)) b

theorem audited_panel_enclosures {i : Nat} (h : i ∈ auditedPanels) (b : Bool) (j : Fin 25) :
    |finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ) -
      (sampleReading fixedColumns b i j:ℝ)| ≤ 1/10^14 := by
  have hx : 576 ≤ i ∧ i < 2304 := by
    simp only [auditedPanels, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide
  exact checkTablePanel_correct hx.1 hx.2 (List.all_eq_true.mp audited_panels_checked i h) b j

#print axioms checkTablePanel_correct
#print axioms audited_panel_enclosures

end DottieOriented.NativeSpectrum.MellinFixed
end
