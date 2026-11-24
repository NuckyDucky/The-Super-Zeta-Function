import MellinIntegerMoment
import MellinOuterSamples
import MellinIntegerTable

/-! The checked integer sums and the analytically enclosed outer samples. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.MellinInteger

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem total_caps :
    totalValue fixedTotals false 0 ≤ -11567/10^10 ∧
    totalValue fixedTotals true 0 ≤ -27415/10^11 ∧
    ∀ k : Fin 3, |totalValue fixedTotals false (k.val+1)| ≤ 268/10^8 ∧
      |totalValue fixedTotals true (k.val+1)| ≤ 402/10^8 := by
  decide +kernel

theorem rational_sample_sums_checked :
    rationalMellinMoment (sampleReading fixedColumns false) 0 ≤ -11567/10^10 ∧
    rationalMellinMoment (sampleReading fixedColumns true) 0 ≤ -27415/10^11 ∧
    ∀ k : ℕ, 0 < k → k < 4 →
      |rationalMellinMoment (sampleReading fixedColumns false) k| ≤ 268/10^8 ∧
      |rationalMellinMoment (sampleReading fixedColumns true) k| ≤ 402/10^8 := by
  have heq (b : Bool) (k : Nat) (hk : k < 4) :
      rationalMellinMoment (sampleReading fixedColumns b) k = totalValue fixedTotals b k :=
    sample_moment_from_blocks _ _ _ fixedColumns_checked fixedTotals_checked b k hk
  refine ⟨?_, ?_, ?_⟩
  · rw [heq false 0 (by decide)]
    exact total_caps.1
  · rw [heq true 0 (by decide)]
    exact total_caps.2.1
  · intro k hp hk
    rw [heq false k hk, heq true k hk]
    have h : (k-1)+1 = k := by omega
    have hf := total_caps.2.2 (⟨k-1, by omega⟩ : Fin 3)
    simpa only [h] using hf

theorem firstDisk_correctionGap_from_checked_sums
    (hnode : ∀ b i, i < 2368 → ∀ j : Fin 25,
      |finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ) -
        (sampleReading fixedColumns b i j:ℝ)| ≤ 1/10^14)
    {s : ℂ} (hs : s ∈ Metric.closedBall firstCenter firstRadius) :
    (11600:ℝ) < ‖correctionGap s‖ :=
  firstDisk_correctionGap_lower_of_rational_samples (sampleReading fixedColumns)
    hnode rational_sample_sums_checked.1 rational_sample_sums_checked.2.1
    rational_sample_sums_checked.2.2 hs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem left_columns_zero :
    ∀ B : Fin 9, ∀ j : Fin 25, fixedColumns B.val j.val = List.replicate 64 (0,0) := by
  decide +kernel

private theorem right_columns_zero :
    ∀ j : Fin 25, fixedColumns 36 j.val = List.replicate 64 (0,0) := by
  decide +kernel

private theorem get_zero (count i : Nat) :
    (List.replicate count ((0,0):Sample)).getD i (0,0) = (0,0) := by
  induction count generalizing i with
  | zero => rfl
  | succ n ih =>
    cases i
    · rw [List.replicate_succ, List.getD_cons_zero]
    · rw [List.replicate_succ, List.getD_cons_succ, ih]

private theorem sampleReading_zero_of_column (b : Bool) (i : Nat) (j : Fin 25)
    (hc : fixedColumns (i/64) j.val = List.replicate 64 (0,0)) :
    sampleReading fixedColumns b i j = 0 := by
  rw [sampleReading, hc, sampleAt, get_zero]
  cases b <;> norm_num [component]

theorem outer_sample_enclosures (b : Bool) (i : Nat) (hi : i < 2368) (j : Fin 25)
    (hOuter : i < 576 ∨ 2304 ≤ i) :
    |finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ) -
      (sampleReading fixedColumns b i j:ℝ)| ≤ 1/10^14 := by
  rcases hOuter with hl | hr
  · have hb : i/64 < 9 := by omega
    have hz := sampleReading_zero_of_column b i j (left_columns_zero ⟨i/64,hb⟩ j)
    simpa only [hz, Rat.cast_zero, sub_zero] using left_node_zero_enclosure b hl j
  · have hb : i/64 = 36 := by omega
    have hz := sampleReading_zero_of_column b i j (by rw [hb]; exact right_columns_zero j)
    simpa only [hz, Rat.cast_zero, sub_zero] using right_node_zero_enclosure b hr j

theorem firstDisk_correctionGap_from_middle_samples
    (hnode : ∀ b i, 576 ≤ i → i < 2304 → ∀ j : Fin 25,
      |finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ) -
        (sampleReading fixedColumns b i j:ℝ)| ≤ 1/10^14)
    {s : ℂ} (hs : s ∈ Metric.closedBall firstCenter firstRadius) :
    (11600:ℝ) < ‖correctionGap s‖ := by
  refine firstDisk_correctionGap_from_checked_sums ?_ hs
  intro b i hi j
  by_cases hl : i < 576
  · exact outer_sample_enclosures b i hi j (.inl hl)
  by_cases hr : 2304 ≤ i
  · exact outer_sample_enclosures b i hi j (.inr hr)
  exact hnode b i (Nat.le_of_not_lt hl) (Nat.lt_of_not_ge hr) j

#print axioms total_caps
#print axioms rational_sample_sums_checked
#print axioms firstDisk_correctionGap_from_checked_sums
#print axioms outer_sample_enclosures
#print axioms firstDisk_correctionGap_from_middle_samples

end DottieOriented.NativeSpectrum.MellinInteger
end
