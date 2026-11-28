import DedekindDiscriminant23GaussEndpoint

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

private theorem phasePiBoxes : ∀ i : Fin 27,
    let k := (i.val : ℤ) - 13
    let b := mul (constant (2 * k)) piBox
    2 * k * 3141592653589793238462643 - 200000 ≤ b.lo ∧ b.hi ≤ 2 * k * 3141592653589793238462643 + 200000 := by
  decide +kernel

theorem gauss23_reduced_phase_in_unit (a : Box)
    (hlo : -80 * scale ≤ a.lo) (hhi : a.hi ≤ 80 * scale)
    (horder : a.lo ≤ a.hi) (hwidth : a.hi ≤ a.lo + 1) :
    inUnit (divInt (reducedPhase a) 4) = true := by
  let k := phaseTurn a
  have hkDef : k = (a.lo + 3141592653589793238462643) / (2 * 3141592653589793238462643) := rfl
  have hRange : -3141592653589793238462643 ≤ a.lo - 2 * k * 3141592653589793238462643 ∧
      a.lo - 2 * k * 3141592653589793238462643 < 3141592653589793238462643 := by
    omega
  have hk : -13 ≤ k ∧ k ≤ 13 := by
    norm_num [scale] at hlo hhi
    omega
  let i : Fin 27 := ⟨Int.toNat (k + 13), by omega⟩
  have hi : (i.val : ℤ) - 13 = k := by
    dsimp only [i]
    omega
  have hb := phasePiBoxes i
  dsimp only at hb
  rw [hi] at hb
  apply decide_eq_true_iff.mpr
  change -scale ≤ (a.lo + -(mul (constant (2 * k)) piBox).hi) / 4 ∧
    -(-(a.hi + -(mul (constant (2 * k)) piBox).lo) / 4) ≤ scale
  norm_num [scale]
  omega

private theorem fromRatio_phase_limits (n : ℤ) {d : ℤ} (hd : 0 < d)
    (hn : -80 * d ≤ n ∧ n ≤ 80 * d) :
    -80 * scale ≤ (fromRatio n d).lo ∧ (fromRatio n d).hi ≤ 80 * scale ∧
    (fromRatio n d).lo ≤ (fromRatio n d).hi ∧ (fromRatio n d).hi ≤ (fromRatio n d).lo + 1 := by
  have hScale : 0 ≤ scale := by norm_num [scale]
  have hLo : -80 * scale ≤ (n * scale) / d := by
    apply (Int.le_ediv_iff_mul_le hd).mpr
    calc
      (-80 * scale) * d = (-80 * d) * scale := by ring
      _ ≤ n * scale := mul_le_mul_of_nonneg_right hn.1 hScale
  have hHi : -80 * scale ≤ (-(n * scale)) / d := by
    apply (Int.le_ediv_iff_mul_le hd).mpr
    calc
      (-80 * scale) * d = -((80 * d) * scale) := by ring
      _ ≤ -(n * scale) := neg_le_neg (mul_le_mul_of_nonneg_right hn.2 hScale)
  have hContains := ratio_contains n hd
  have hOrder : (fromRatio n d).lo ≤ (fromRatio n d).hi := by
    exact_mod_cast hContains.1.trans hContains.2
  refine ⟨hLo, ?_, hOrder, ?_⟩
  · change -((-(n * scale)) / d) ≤ 80 * scale
    linarith only [hHi]
  · change -((-(n * scale)) / d) ≤ (n * scale) / d + 1
    rw [Int.neg_ediv, Int.sign_eq_one_of_pos hd]
    split <;> omega

theorem gauss23_phaseCheck_of_height (m : ℤ) {d : ℤ} (hd : 0 < d)
    (hT : |(m : ℝ) / d| ≤ 20) (j : Fin 16) (i : Fin 24) :
    gauss23PhaseCheck m d j i = true := by
  let n := m * gauss23NodeNumerator j i
  let D := d * gauss23NodeDenominator
  have hD : 0 < D := mul_pos hd (by norm_num [gauss23NodeDenominator, gauss24Denominator])
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  obtain ⟨hu₀, hu₁⟩ := gauss23_node_limits j i
  have hv : (n : ℝ) / D = ((m : ℝ) / d) * gauss23LogNode j i := by
    simp only [n, D, gauss23LogNode, Int.cast_mul, div_mul_div_comm]
  have hAbs : |(n : ℝ) / D| ≤ 80 := by
    rw [hv, abs_mul, abs_of_nonneg hu₀]
    calc
      |(m : ℝ) / d| * gauss23LogNode j i ≤ 20 * 4 :=
        mul_le_mul hT hu₁ hu₀ (by norm_num)
      _ = 80 := by norm_num
  have hN : -80 * D ≤ n ∧ n ≤ 80 * D := by
    constructor
    · exact_mod_cast (le_div_iff₀ hDR).mp (abs_le.mp hAbs).1
    · exact_mod_cast (div_le_iff₀ hDR).mp (abs_le.mp hAbs).2
  obtain ⟨h₁, h₂, h₃, h₄⟩ := fromRatio_phase_limits n hD hN
  exact gauss23_reduced_phase_in_unit (fromRatio n D) h₁ h₂ h₃ h₄

theorem gauss23_critical_sign_of_interval (m : ℤ) {d : ℤ} (hd : 0 < d) (positive : Bool)
    (hT : |(m : ℝ) / d| ≤ 20) (hcheck : gauss23ClearsError m d positive) :
    if positive then 0 < (discriminant23CharacterFold (gauss23CriticalPoint ((m : ℝ) / d))).re
    else (discriminant23CharacterFold (gauss23CriticalPoint ((m : ℝ) / d))).re < 0 :=
  gauss23_critical_sign_of_check m hd positive hT (gauss23_phaseCheck_of_height m hd hT) hcheck

#print axioms gauss23_reduced_phase_in_unit
#print axioms gauss23_phaseCheck_of_height
#print axioms gauss23_critical_sign_of_interval

end FieldTarget
