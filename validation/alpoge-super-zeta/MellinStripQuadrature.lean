import MellinStripBound
import MellinQuadratureRule

/-! The same real integral on a fixed partition, with Lean's strip bound supplying
every Cauchy circle used by the quadrature. -/

noncomputable section

namespace DottieOriented.NativeSpectrum

open MeasureTheory SuperZeta.CauchyPanelQuadrature

def mellinPanelCenter (i : ℕ) : ℚ := -32+(i:ℚ)/64+1/128

def mellinPanelNode (i : ℕ) (j : Fin 25) : ℚ := mellinPanelCenter i + (1/128)*node j

private def panelEdge (i : ℕ) : ℝ := -32+(i:ℝ)/64

private theorem panelCenter_mem {i : ℕ} (hi : i < 2368) :
    (-32:ℝ) ≤ (mellinPanelCenter i:ℝ) ∧ (mellinPanelCenter i:ℝ) ≤ 5 := by
  have hu : (i:ℝ) ≤ 2367 := by exact_mod_cast Nat.le_of_lt_succ hi
  have hlo : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  norm_num [mellinPanelCenter]
  exact ⟨by linarith only [hlo], by linarith only [hu]⟩

private theorem params_of_panel (c : ℝ) (hlo : -32 ≤ c) (hhi : c ≤ 5)
    {z : ℂ} (hz : z ∈ Metric.closedBall (c:ℂ) (8*(1/128))) :
    |z.im| ≤ 1/16 ∧ -(513/16) ≤ z.re ∧ z.re ≤ 81/16 := by
  rw [Metric.mem_closedBall, dist_eq_norm, show (8*(1/128):ℝ) = 1/16 by norm_num] at hz
  have hi := (Complex.abs_im_le_norm (z-(c:ℂ))).trans hz
  have hr := (Complex.abs_re_le_norm (z-(c:ℂ))).trans hz
  rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
  rw [Complex.sub_re, Complex.ofReal_re] at hr
  obtain ⟨hl, hh⟩ := abs_le.mp hr
  exact ⟨hi, by linarith only [hl, hlo], by linarith only [hh, hhi]⟩

private def panelQuadrature (k i : ℕ) : ℂ :=
  (1/128:ℂ)*∑ j : Fin 25, ((weight j:ℝ):ℂ) *
    holomorphicMellinDensity k ((mellinPanelNode i j:ℝ):ℂ)

def mellinQuadrature (k : ℕ) : ℂ := ∑ i ∈ Finset.range 2368, panelQuadrature k i

private def panelError (k : ℕ) : ℝ :=
  (1/128)*(4*mellinStripMajorant k*(1/8)^25/(1-1/8))

private theorem panelQuadrature_error (k : ℕ) {i : ℕ} (hi : i < 2368) :
    ‖(∫ u in (panelEdge i)..(panelEdge (i+1)), holomorphicMellinDensity k (u:ℂ)) -
       panelQuadrature k i‖ ≤ panelError k := by
  let c := (mellinPanelCenter i:ℝ)
  obtain ⟨hlo, hhi⟩ := panelCenter_mem hi
  have hf : DifferentiableOn ℂ (holomorphicMellinDensity k) (Metric.closedBall (c:ℂ) (8*(1/128))) :=
    fun _ hz => (holomorphicMellinDensity_differentiableAt k (params_of_panel c hlo hhi hz).1).differentiableWithinAt
  have hM (z : ℂ) (hz : z ∈ Metric.sphere (c:ℂ) (8*(1/128))) :
      ‖holomorphicMellinDensity k z‖ ≤ mellinStripMajorant k := by
    obtain ⟨hm, hl, hh⟩ := params_of_panel c hlo hhi (Metric.sphere_subset_closedBall hz)
    exact norm_holomorphicMellinDensity_le k hm hl hh
  have hquad := error_25_panel (h := (1/128:ℝ)) (by norm_num) hf hM
  have hleft : c-1/128 = panelEdge i := by
    norm_num [c, mellinPanelCenter, panelEdge]
  have hright : c+1/128 = panelEdge (i+1) := by
    norm_num [c, mellinPanelCenter, panelEdge, Nat.cast_add]
    ring
  rw [hleft, hright] at hquad
  simpa [panelQuadrature, panelError, c, mellinPanelNode, Rat.cast_add, Rat.cast_mul, Rat.cast_div] using hquad

private theorem continuous_real_density (k : ℕ) : Continuous (fun u : ℝ => holomorphicMellinDensity k (u:ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  exact (holomorphicMellinDensity_differentiableAt k (u := (u:ℂ)) (by norm_num)).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

theorem mellinQuadrature_error (k : ℕ) :
    ‖(∫ u in (-32:ℝ)..5, holomorphicMellinDensity k (u:ℂ)) - mellinQuadrature k‖ ≤
      2368*panelError k := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := panelEdge)
    (n := 2368) (fun i _ => (continuous_real_density k).intervalIntegrable (panelEdge i) (panelEdge (i+1)))
  have hlo : panelEdge 0 = -32 := by norm_num [panelEdge]
  have hhi : panelEdge 2368 = 5 := by norm_num [panelEdge]
  rw [hlo, hhi] at hsum
  rw [← hsum, mellinQuadrature, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i ∈ Finset.range 2368, panelError k :=
      Finset.sum_le_sum fun _ hi => panelQuadrature_error k (Finset.mem_range.mp hi)
    _ = _ := by simp

def mellinQuadratureComponent (imaginary : Bool) (k : ℕ) : ℝ :=
  component imaginary (mellinQuadrature k)

private theorem component_of_integral (imaginary : Bool) (k : ℕ) :
    component imaginary (∫ u in (-32:ℝ)..5, holomorphicMellinDensity k (u:ℂ)) =
      finiteCoefficient imaginary k := by
  have h := (continuous_real_density k).intervalIntegrable (μ := volume) (-32) 5
  cases imaginary
  · change Complex.reCLM (∫ u in (-32:ℝ)..5, holomorphicMellinDensity k (u:ℂ)) = _
    rw [← Complex.reCLM.intervalIntegral_comp_comm h, finiteCoefficient]
    refine intervalIntegral.integral_congr fun u _ => ?_
    change component false (holomorphicMellinDensity k (u:ℂ)) = _
    rw [holomorphicMellinDensity_ofReal, finiteCoefficientDensity_eq]
  · change Complex.imCLM (∫ u in (-32:ℝ)..5, holomorphicMellinDensity k (u:ℂ)) = _
    rw [← Complex.imCLM.intervalIntegral_comp_comm h, finiteCoefficient]
    refine intervalIntegral.integral_congr fun u _ => ?_
    change component true (holomorphicMellinDensity k (u:ℂ)) = _
    rw [holomorphicMellinDensity_ofReal, finiteCoefficientDensity_eq]

theorem mellinQuadratureComponent_eq (imaginary : Bool) (k : ℕ) :
    mellinQuadratureComponent imaginary k =
      (1/128)*∑ i ∈ Finset.range 2368, ∑ j : Fin 25,
        (weight j:ℝ) * finiteCoefficientDensity imaginary k (mellinPanelNode i j:ℝ) := by
  have hf (i : ℕ) (j : Fin 25) :
      component imaginary (holomorphicMellinDensity k ((mellinPanelNode i j:ℝ):ℂ)) =
        finiteCoefficientDensity imaginary k (mellinPanelNode i j:ℝ) := by
    rw [holomorphicMellinDensity_ofReal, finiteCoefficientDensity_eq]
  cases imaginary
  · simp only [mellinQuadratureComponent, mellinQuadrature, panelQuadrature, component, Bool.false_eq_true,
      if_false, Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im, zero_div, zero_mul, sub_zero,
      ← Finset.mul_sum] at hf ⊢
    simp only [hf]
  · simp only [mellinQuadratureComponent, mellinQuadrature, panelQuadrature, component, if_true, Complex.im_sum,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.one_re, Complex.one_im, zero_div, zero_mul, add_zero, ← Finset.mul_sum] at hf ⊢
    simp only [hf]

theorem mellinQuadratureComponent_error (imaginary : Bool) (k : ℕ) :
    |finiteCoefficient imaginary k - mellinQuadratureComponent imaginary k| ≤ 2368*panelError k := by
  rw [← component_of_integral, mellinQuadratureComponent]
  have hb := mellinQuadrature_error k
  cases imaginary
  · simp only [component, Bool.false_eq_true, if_false, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans hb
  · simp only [component, if_true, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans hb

private theorem panelError_zero : 2368*panelError 0 ≤ (1:ℝ)/10^12 := by
  norm_num [panelError, mellinStripMajorant]

private theorem panelError_higher {k : ℕ} (hpos : 0 < k) (hk : k < 4) :
    2368*panelError k ≤ (1:ℝ)/10^8 := by
  interval_cases k <;> norm_num [panelError, mellinStripMajorant, Nat.factorial]

theorem firstDisk_correctionGap_lower_of_quadrature
    (hreal : mellinQuadratureComponent false 0 ≤ -11566/10^10)
    (himag : mellinQuadratureComponent true 0 ≤ -2741/10^10)
    (hrest : ∀ k : ℕ, 0 < k → k < 4 →
      |mellinQuadratureComponent false k| ≤ 270/10^8 ∧
      |mellinQuadratureComponent true k| ≤ 404/10^8)
    {s : ℂ} (hs : s ∈ Metric.closedBall firstCenter firstRadius) :
    (11600:ℝ) < ‖correctionGap s‖ := by
  have hr := (abs_le.mp ((mellinQuadratureComponent_error false 0).trans panelError_zero)).2
  have hi := (abs_le.mp ((mellinQuadratureComponent_error true 0).trans panelError_zero)).2
  refine firstDisk_correctionGap_lower_of_finite ?_ ?_ ?_ hs
  · linarith only [hr,hreal]
  · linarith only [hi,himag]
  · intro k hp hk
    have h (b : Bool) : |finiteCoefficient b k| ≤ |mellinQuadratureComponent b k| + (1:ℝ)/10^8 := by
      calc
        _ = |(finiteCoefficient b k - mellinQuadratureComponent b k) + mellinQuadratureComponent b k| := by simp
        _ ≤ |finiteCoefficient b k - mellinQuadratureComponent b k| +
            |mellinQuadratureComponent b k| := abs_add_le _ _
        _ ≤ _ := by
          have he := (mellinQuadratureComponent_error b k).trans (panelError_higher hp hk)
          linarith only [he]
    exact ⟨by linarith only [h false,(hrest k hp hk).1],
      by linarith only [h true,(hrest k hp hk).2]⟩

#print axioms mellinQuadrature_error
#print axioms mellinQuadratureComponent_eq
#print axioms mellinQuadratureComponent_error
#print axioms firstDisk_correctionGap_lower_of_quadrature

end DottieOriented.NativeSpectrum
end
