import MellinStripQuadrature

/-! Passing from rational node readings to all four finite Mellin moments. -/

noncomputable section

namespace DottieOriented.NativeSpectrum

open SuperZeta.CauchyPanelQuadrature

private theorem mellinPanelNode_mem {i : ℕ} (hi : i < 2368) (j : Fin 25) :
    (-32:ℝ) ≤ (mellinPanelNode i j:ℝ) ∧ (mellinPanelNode i j:ℝ) ≤ 5 := by
  have h0 : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  have h1 : (i:ℝ) ≤ 2367 := by exact_mod_cast Nat.le_of_lt_succ hi
  have hn : |(node j:ℝ)| ≤ 1 := by exact_mod_cast (rule_certified.1 j).1
  obtain ⟨hnl,hnu⟩ := abs_le.mp hn
  norm_num [mellinPanelNode, mellinPanelCenter]
  exact ⟨by linarith only [h0,hnl], by linarith only [h1,hnu]⟩

private theorem density_factor (b : Bool) (k : ℕ) (u : ℝ) :
    finiteCoefficientDensity b k u =
      ((-2*u)^k/k.factorial) * finiteCoefficientDensity b 0 u := by
  simp only [finiteCoefficientDensity, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, one_mul, mul_assoc]

private def momentFactor (k : ℕ) (u : ℚ) : ℚ :=
  (-2*u)^k/k.factorial

def rationalMellinMoment (a : ℕ → Fin 25 → ℚ) (k : ℕ) : ℚ :=
  (1/128)*∑ i ∈ Finset.range 2368, ∑ j : Fin 25,
      weight j * momentFactor k (mellinPanelNode i j) * a i j

theorem mellinRationalSum_error (b : Bool) (k : ℕ) (a : ℕ → Fin 25 → ℚ) {ε : ℝ}
    (h : ∀ i < 2368, ∀ j : Fin 25,
      |finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ) - (a i j:ℝ)| ≤ ε) :
    |mellinQuadratureComponent b k - (rationalMellinMoment a k:ℝ)| ≤
      37*((64:ℝ)^k/k.factorial)*ε := by
  let B := ((64:ℝ)^k/k.factorial)*ε
  have hw (j : Fin 25) : 0 ≤ (weight j:ℝ) := by exact_mod_cast (rule_certified.1 j).2
  have hsum : (∑ j : Fin 25, (weight j:ℝ)) = 2 := by exact_mod_cast rule_certified.2.1
  let K (i : ℕ) (j : Fin 25) : ℝ :=
    (weight j:ℝ) * ((momentFactor k (mellinPanelNode i j)):ℝ)
  let E (i : ℕ) (j : Fin 25) : ℝ :=
    finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ) - (a i j:ℝ)
  have hfact (i : ℕ) (j : Fin 25) :
      finiteCoefficientDensity b k (mellinPanelNode i j:ℝ) =
        ((momentFactor k (mellinPanelNode i j)):ℝ) *
          finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ) := by
    rw [density_factor, momentFactor]
    push_cast
    rfl
  have hrewrite : mellinQuadratureComponent b k - (rationalMellinMoment a k:ℝ) =
      (1/128)*∑ i ∈ Finset.range 2368, ∑ j : Fin 25, K i j * E i j := by
    rw [mellinQuadratureComponent_eq, rationalMellinMoment]
    push_cast
    simp_rw [hfact, ← mul_assoc]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
    rfl
  have hterm (i : ℕ) (hi : i < 2368) (j : Fin 25) :
      |K i j * E i j| ≤ (weight j:ℝ)*B := by
    let u := (mellinPanelNode i j:ℝ)
    have hnode := mellinPanelNode_mem hi j
    have hu : |u| ≤ 32 := abs_le.mpr ⟨hnode.1, hnode.2.trans (by norm_num)⟩
    have h2u : |(-2:ℝ)*u| ≤ 64 := by
      rw [abs_mul, show |(-2:ℝ)| = 2 by norm_num]
      linarith only [hu]
    have hf : |(momentFactor k (mellinPanelNode i j):ℝ)| ≤ (64:ℝ)^k/k.factorial := by
      unfold momentFactor
      push_cast
      rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ k.factorial)]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h2u _) (by positivity)
    simp only [K, B, abs_mul, abs_of_nonneg (hw j)]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hw j)
    exact mul_le_mul hf (h i hi j) (abs_nonneg _) (by positivity)
  have hInner (i : ℕ) (hi : i < 2368) :
      |∑ j : Fin 25, K i j * E i j| ≤ 2*B := by
    calc
      _ ≤ ∑ j : Fin 25, |K i j * E i j| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ (fun j => K i j * E i j)
      _ ≤ ∑ j : Fin 25, (weight j:ℝ)*B := Finset.sum_le_sum fun j _ => hterm i hi j
      _ = _ := by rw [← Finset.sum_mul, hsum]
  have hOuter : |∑ i ∈ Finset.range 2368, ∑ j : Fin 25, K i j * E i j| ≤ 2368*(2*B) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2368, |∑ j : Fin 25, K i j * E i j| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.range 2368) (fun i => ∑ j : Fin 25, K i j * E i j)
      _ ≤ ∑ _i ∈ Finset.range 2368, 2*B :=
        Finset.sum_le_sum fun i hi => hInner i (Finset.mem_range.mp hi)
      _ = _ := by simp
  rw [hrewrite, abs_mul, show |(1/128:ℝ)| = 1/128 by norm_num]
  calc
    _ ≤ (1/128)*(2368*(2*B)) := mul_le_mul_of_nonneg_left hOuter (by norm_num)
    _ = _ := by dsimp [B]; ring

theorem firstDisk_correctionGap_lower_of_rational_samples
    (a : Bool → ℕ → Fin 25 → ℚ)
    (hnode : ∀ b i, i < 2368 → ∀ j : Fin 25,
      |finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ) - (a b i j:ℝ)| ≤ 1/10^14)
    (hr : rationalMellinMoment (a false) 0 ≤ -11567/10^10)
    (hi : rationalMellinMoment (a true) 0 ≤ -27415/10^11)
    (hrest : ∀ k : ℕ, 0 < k → k < 4 →
      |rationalMellinMoment (a false) k| ≤ 268/10^8 ∧
      |rationalMellinMoment (a true) k| ≤ 402/10^8)
    {s : ℂ} (hs : s ∈ Metric.closedBall firstCenter firstRadius) :
    (11600:ℝ) < ‖correctionGap s‖ := by
  have hQ (b : Bool) (k : ℕ) :
      |mellinQuadratureComponent b k - (rationalMellinMoment (a b) k:ℝ)| ≤
        37*((64:ℝ)^k/k.factorial)*(1/10^14) :=
    mellinRationalSum_error b k (a b) (hnode b)
  refine firstDisk_correctionGap_lower_of_quadrature ?_ ?_ ?_ hs
  · have hr' : (rationalMellinMoment (a false) 0:ℝ) ≤ (-11567/10^10:ℝ) := by
      have hk := (show (rationalMellinMoment (a false) 0:ℝ) ≤ ((-11567/10^10:ℚ):ℝ) from Rat.cast_le.mpr hr)
      norm_num at hk ⊢
      exact hk
    have he := (abs_le.mp (hQ false 0)).2
    norm_num at he
    linarith only [hr',he]
  · have hi' : (rationalMellinMoment (a true) 0:ℝ) ≤ (-27415/10^11:ℝ) := by
      have hk := (show (rationalMellinMoment (a true) 0:ℝ) ≤ ((-27415/10^11:ℚ):ℝ) from Rat.cast_le.mpr hi)
      norm_num at hk ⊢
      exact hk
    have he := (abs_le.mp (hQ true 0)).2
    norm_num at he
    linarith only [hi',he]
  · intro k hpos hlt
    have herror : 37*((64:ℝ)^k/k.factorial)*(1/10^14) ≤ 2/10^8 := by
      interval_cases k <;> norm_num [Nat.factorial]
    have habs (b : Bool) : |mellinQuadratureComponent b k| ≤
        |(rationalMellinMoment (a b) k:ℝ)|+2/10^8 := by
      calc
        _ = |(mellinQuadratureComponent b k - (rationalMellinMoment (a b) k:ℝ)) +
            (rationalMellinMoment (a b) k:ℝ)| := by simp
        _ ≤ 2/10^8 + |(rationalMellinMoment (a b) k:ℝ)| :=
          (abs_add_le _ _).trans (add_le_add_right ((hQ b k).trans herror) _)
        _ = _ := add_comm _ _
    have hr' : |(rationalMellinMoment (a false) k:ℝ)| ≤ (268/10^8:ℝ) := by
      have hk := (show (|rationalMellinMoment (a false) k|:ℚ) ≤ (268/10^8:ℚ) from (hrest k hpos hlt).1)
      have hv : ((|rationalMellinMoment (a false) k|:ℚ):ℝ) ≤ ((268/10^8:ℚ):ℝ) := Rat.cast_le.mpr hk
      simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using hv
    have hi' : |(rationalMellinMoment (a true) k:ℝ)| ≤ (402/10^8:ℝ) := by
      have hk := (show (|rationalMellinMoment (a true) k|:ℚ) ≤ (402/10^8:ℚ) from (hrest k hpos hlt).2)
      have hv : ((|rationalMellinMoment (a true) k|:ℚ):ℝ) ≤ ((402/10^8:ℚ):ℝ) := Rat.cast_le.mpr hk
      simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using hv
    exact ⟨by linarith only [habs false,hr'], by linarith only [habs true,hi']⟩

#print axioms mellinRationalSum_error
#print axioms firstDisk_correctionGap_lower_of_rational_samples

end DottieOriented.NativeSpectrum
end
