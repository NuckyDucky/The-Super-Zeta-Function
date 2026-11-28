import DedekindDiscriminant23GaussPoint

/-! Transfer the directed integer endpoint checks to the actual character. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

def gauss23ClearsError (m d : ℤ) (positive : Bool) : Prop :=
  if positive then 200000 < (gauss23CriticalValueBox m d).lo
  else (gauss23CriticalValueBox m d).hi < -200000

instance (m d : ℤ) (positive : Bool) : Decidable (gauss23ClearsError m d positive) := by
  cases positive <;> simp only [gauss23ClearsError, Bool.false_eq_true, ↓reduceIte] <;> infer_instance

theorem gauss23_critical_sign_of_check (m : ℤ) {d : ℤ} (hd : 0 < d) (positive : Bool)
    (hT : |(m : ℝ) / d| ≤ 20) (hphase : ∀ j i, gauss23PhaseCheck m d j i = true)
    (hcheck : gauss23ClearsError m d positive) :
    if positive then 0 < (discriminant23CharacterFold (gauss23CriticalPoint ((m : ℝ) / d))).re
    else (discriminant23CharacterFold (gauss23CriticalPoint ((m : ℝ) / d))).re < 0 := by
  let w := gauss23CriticalPoint ((m : ℝ) / d)
  have he := discriminant23_gaussReading_error false (w := w)
    (by norm_num [w, gauss23CriticalPoint]) (by norm_num [w, gauss23CriticalPoint]) hT
  have hre := (Complex.abs_re_le_norm _).trans_lt he
  simp only [Bool.false_eq_true, ↓reduceIte, Complex.sub_re] at hre
  rw [gauss23_criticalReading_eq_sum] at hre
  have hBox := gauss23_valueBox_contains m hd hphase
  have hScale : (200000 : ℝ) = scale * (2 / 10 ^ 19 : ℝ) := by norm_num [scale]
  cases positive
  · change (gauss23CriticalValueBox m d).hi < -200000 at hcheck
    have hBound : (↑(gauss23CriticalValueBox m d).hi : ℝ) < -(200000 : ℝ) := by exact_mod_cast hcheck
    rw [hScale, ← mul_neg] at hBound
    have hSign := (mul_lt_mul_iff_right₀ scale_pos).mp (hBox.2.trans_lt hBound)
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (discriminant23CharacterFold w).re < 0
    linarith only [hSign, (abs_lt.mp hre).2]
  · change 200000 < (gauss23CriticalValueBox m d).lo at hcheck
    have hBound : (200000 : ℝ) < (↑(gauss23CriticalValueBox m d).lo : ℝ) := by exact_mod_cast hcheck
    rw [hScale] at hBound
    have hSign := (mul_lt_mul_iff_right₀ scale_pos).mp (hBound.trans_le hBox.1)
    simp only [↓reduceIte]
    change 0 < (discriminant23CharacterFold w).re
    linarith only [hSign, (abs_lt.mp hre).1]

#print axioms gauss23_critical_sign_of_check

end

end FieldTarget
