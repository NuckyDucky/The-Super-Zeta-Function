import MellinFixedElementary
import MellinFixedLog
import NativeDottieMellinExpression

/-! A successful integer check encloses both components of the exact zeroth Mellin density. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.MellinFixed

private theorem determinants_contains {xBox bBox : Box} {x b : ℝ}
    (hx : Contains xBox x) (hb : Contains bBox b)
    (hx0 : 0 ≤ x) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Contains (determinants xBox bBox).1 ((1-b*b)*(1-b*b)+(3+4*(x*x))*(b*b)) ∧
      Contains (determinants xBox bBox).2 (2*(x*b*(1-b*b))) := by
  have ht0 : 0 ≤ 1-b*b := by nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb1)]
  have h3 : Contains (constant 3) (3:ℝ) := by
    simpa only [Int.cast_ofNat] using constant_contains 3
  have h4 : Contains (constant 4) (4:ℝ) := by
    simpa only [Int.cast_ofNat] using constant_contains 4
  have h2 : Contains (constant 2) (2:ℝ) := by
    simpa only [Int.cast_ofNat] using constant_contains 2
  have h1 : Contains (constant 1) (1:ℝ) := by
    simpa only [Int.cast_one] using constant_contains 1
  have hb2 := mul_contains hb hb
  have ht := nonnegative_contains (sub_contains h1 hb2) ht0
  exact ⟨add_contains (mul_contains ht ht)
    (mul_contains (add_contains h3 (mul_contains h4 (mul_contains hx hx))) hb2),
    nonnegative_contains (mul_contains h2 (mul_contains (mul_contains hx hb) ht))
      (by positivity)⟩

private theorem log_of_quotient {A O : ℝ} (hA : 0 < A) (hq0 : 0 ≤ O/A)
    (hq1 : O/A ≤ 1/2) :
    Real.log ((A-O)/(A+O)) = Real.log (1-O/A)-Real.log (1+O/A) := by
  have hpos : 0 < 1+O/A := by linarith
  have hsum : 0 < A+O := by
    have hm := mul_pos hA hpos
    rw [mul_add, mul_one, mul_div_cancel₀ _ hA.ne'] at hm
    exact hm
  have heq : (A-O)/(A+O) = (1-O/A)/(1+O/A) := by
    field_simp [hA.ne', hsum.ne', hpos.ne']
  rw [heq, Real.log_div (by linarith : 1-O/A ≠ 0) hpos.ne']

private theorem checked_option (reject : Prop) [Decidable reject] (admit : Bool)
    (r i : Box) (re im : Int)
    (h : (match (if reject then none else if admit then some (r,i) else none) with
      | none => false
      | some (a,b) => fitsSample a re && fitsSample b im) = true) :
    ¬reject ∧ admit = true ∧ fitsSample r re = true ∧ fitsSample i im = true := by
  by_cases hr : reject
  · simp [hr] at h
  · cases admit <;> simp_all only [if_neg, Bool.false_eq_true, if_false, if_true,
      Bool.and_eq_true_iff, not_false_eq_true, true_and, and_true]

set_option maxRecDepth 4096 in
theorem checkDensity_correct (n re im : Int)
    (hu : |(n:ℝ)/524288| ≤ 128) (he : Real.exp ((n:ℝ)/524288) ≤ 128)
    (hc : checkDensity n re im = true) :
    |finiteCoefficientDensity false 0 ((n:ℝ)/524288) - (re:ℝ)/10^14| ≤ 1/10^14 ∧
      |finiteCoefficientDensity true 0 ((n:ℝ)/524288) - (im:ℝ)/10^14| ≤ 1/10^14 := by
  let u : ℝ := (n:ℝ)/524288
  let x := Real.exp u
  let b := Real.exp (-x)
  let uBox := fromRatio n 524288
  let xBox := expFixed uBox
  let bBox := expFixed (neg xBox)
  let parts := determinants xBox bBox
  let qBox := divPositive parts.2 parts.1
  let phase := mul (fromRatio 7067363 500000) uBox
  let amp := mul (expFixed (divInt (neg uBox) 2)) (logGapFixed qBox)
  let cs := cosSinFixed phase
  have hboxes : densityBoxes n =
      if parts.1.lo ≤ 0 then none else
        if inLogDomain qBox && inUnit (divInt (reducedPhase phase) 4) then
          some (mul amp cs.1, mul amp (neg cs.2))
        else none := by rfl
  let fits : Option (Box × Box) → Bool := fun value => match value with
    | none => false
    | some (r,i) => fitsSample r re && fitsSample i im
  have hfit := congrArg fits hboxes
  have hchecked := hfit.symm.trans hc
  obtain ⟨ha, hd, hrBound, hiBound⟩ := checked_option (parts.1.lo ≤ 0)
    (inLogDomain qBox && inUnit (divInt (reducedPhase phase) 4))
    (mul amp cs.1) (mul amp (neg cs.2)) re im hchecked
  have hU : Contains uBox u := by
    simpa only [Int.cast_ofNat] using ratio_contains n (d := 524288) (by decide)
  have hX : Contains xBox x := expFixed_contains hU hu
  have hbx : |-x| ≤ 128 := by rw [abs_neg, abs_of_pos (Real.exp_pos u)]; exact he
  have hB : Contains bBox b := expFixed_contains (neg_contains hX) hbx
  have hb1 : b ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_pos u).le)
  let A := (1-b*b)*(1-b*b)+(3+4*(x*x))*(b*b)
  let O := 2*(x*b*(1-b*b))
  have hp : Contains parts.1 A ∧ Contains parts.2 O :=
    determinants_contains hX hB (Real.exp_pos u).le (Real.exp_pos (-x)).le hb1
  have haPos : 0 < parts.1.lo := lt_of_not_ge ha
  have hA : 0 < A := by
    have hl : (0:ℝ) < (parts.1.lo:ℝ) := by exact_mod_cast haPos
    exact pos_of_mul_pos_right (hl.trans_le hp.1.1) scale_pos.le
  have hoPos : 0 ≤ parts.2.lo := le_max_left _ _
  have hQ : Contains qBox (O/A) := divPositive_contains hp.2 hp.1 hoPos haPos
  have hdomains := Bool.and_eq_true_iff.mp hd
  have hqRange := logDomain_contains hQ hdomains.1
  have hgap : finiteLogGap x = Real.log (1-O/A)-Real.log (1+O/A) := by
    rw [← log_of_quotient hA hqRange.1 hqRange.2, finiteLogGap]
    simp only [A, O, b, pow_two, mul_assoc]
  have hL : Contains (logGapFixed qBox) (finiteLogGap x) := by
    rw [hgap]
    exact logGapFixed_contains hQ hdomains.1
  have hhalf : Contains (divInt (neg uBox) 2) (-u/2) := by
    simpa only [Int.cast_ofNat] using divInt_contains (neg_contains hU) (d := 2) (by decide)
  have hhalfRange : |-u/2| ≤ 128 := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h : |u| ≤ 128 := hu
    linarith
  have hAmp : Contains amp (Real.exp (-u/2)*finiteLogGap x) :=
    mul_contains (expFixed_contains hhalf hhalfRange) hL
  have hP : Contains phase (7067363/500000*u) := by
    have hω : Contains (fromRatio 7067363 500000) ((7067363:ℝ)/500000) := by
      simpa only [Int.cast_ofNat] using ratio_contains 7067363 (d := 500000) (by decide)
    exact mul_contains hω hU
  have hCS := cosSinFixed_contains hP hdomains.2
  have hr := fitsSample_correct (mul_contains hAmp hCS.1) hrBound
  have hi := fitsSample_correct (mul_contains hAmp (neg_contains hCS.2)) hiBound
  simpa only [finiteCoefficientDensity, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, one_mul, Bool.false_eq_true, if_false, if_true, u, x] using And.intro hr hi

#print axioms checkDensity_correct

end DottieOriented.NativeSpectrum.MellinFixed
end
