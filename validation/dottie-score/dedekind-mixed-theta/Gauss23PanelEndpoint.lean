import DedekindDiscriminant23GaussEndpoint

/-! Assemble checked endpoint bounds without recomputing a whole quadrature in the kernel. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

def gauss23PanelEnd (m d : ℤ) (positive : Bool) (j : ℕ) : ℤ :=
  let box := gauss23CriticalPanelBox m d j
  if positive then box.lo else box.hi

private theorem sum_eq_panelEnds (f : ℕ → ℤ) (ends : List ℤ)
    (h : ∀ j : Fin 16, f j.val = ends.getD j.val 0) :
    (∑ j ∈ Finset.range 16, f j) = ∑ j ∈ Finset.range 16, ends.getD j 0 := by
  apply Finset.sum_congr rfl
  intro j hj
  exact h ⟨j, Finset.mem_range.mp hj⟩

theorem gauss23_clearsError_of_panel_ends (m d : ℤ) (positive : Bool) (ends : List ℤ)
    (hEnds : ∀ j : Fin 16, gauss23PanelEnd m d positive j.val = ends.getD j.val 0)
    (hBudget : if positive then 200000 < ∑ j ∈ Finset.range 16, ends.getD j 0
      else (∑ j ∈ Finset.range 16, ends.getD j 0) < -200000) :
    gauss23ClearsError m d positive := by
  cases positive
  · simp only [gauss23PanelEnd, Bool.false_eq_true, ↓reduceIte] at hEnds
    simp only [Bool.false_eq_true, ↓reduceIte] at hBudget
    simp only [gauss23ClearsError, Bool.false_eq_true, ↓reduceIte]
    rw [gauss23_criticalValueBox_eq_sums]
    exact lt_of_eq_of_lt
      (sum_eq_panelEnds (fun j ↦ (gauss23CriticalPanelBox m d j).hi) ends hEnds) hBudget
  · simp only [gauss23PanelEnd, ↓reduceIte] at hEnds
    simp only [↓reduceIte] at hBudget
    simp only [gauss23ClearsError, ↓reduceIte]
    rw [gauss23_criticalValueBox_eq_sums]
    exact lt_of_lt_of_eq hBudget
      (sum_eq_panelEnds (fun j ↦ (gauss23CriticalPanelBox m d j).lo) ends hEnds).symm

#print axioms gauss23_clearsError_of_panel_ends

end FieldTarget
