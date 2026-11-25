import EtaEulerRemainder

/-! The finite Mellin approximation is an explicit Euler-transformed Dirichlet sum. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.EtaMellin

open Complex MeasureTheory Set

def binomialWeight (k j : ℕ) : ℂ :=
  ↑(((-1:ℝ)^j * (k.choose j:ℝ))/2^(k+1))

def etaEulerSum (n : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k+1),
    binomialWeight k j * ((j:ℂ)+1)^(-w)

private def exponentialKernel (j : ℕ) (x : ℝ) : ℂ :=
  ↑(Real.exp (-(((j:ℝ)+1)*x)))

private theorem binomial_row (k : ℕ) (x : ℝ) :
    Real.exp (-x)/2 * (ratio x)^k =
      ∑ j ∈ Finset.range (k+1), (((-1:ℝ)^j*(k.choose j:ℝ))/2^(k+1)) *
        Real.exp (-(((j:ℝ)+1)*x)) := by
  unfold ratio
  rw [div_pow, show 1 - Real.exp (-x) = -Real.exp (-x)+1 by ring, add_pow]
  simp only [one_pow, mul_one, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show -(((j:ℝ)+1)*x) = ((j+1:ℕ):ℝ)*(-x) by push_cast; ring,
    Real.exp_nat_mul, pow_succ (Real.exp (-x)), pow_succ (2:ℝ),
    neg_pow (Real.exp (-x))]
  ring

private theorem partial_expansion (n : ℕ) (x : ℝ) :
    fermiPartial n x = ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k+1),
      binomialWeight k j * exponentialKernel j x := by
  have h : Real.exp (-x)/2 * (∑ k ∈ Finset.range n, (ratio x)^k) =
      ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k+1),
        (((-1:ℝ)^j*(k.choose j:ℝ))/2^(k+1)) * Real.exp (-(((j:ℝ)+1)*x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => binomial_row k x
  rw [fermiPartial, h]
  simp only [ofReal_sum, ofReal_mul, binomialWeight, exponentialKernel]

private theorem exponential_convergent (j : ℕ) {w : ℂ} (hw : 0 < w.re) :
    MellinConvergent (exponentialKernel j) w := by
  have h : MellinConvergent (fun x : ℝ => (Real.exp (-x):ℂ)) w := by
    have he : (fun x : ℝ => (x:ℂ)^(w-1) • (Real.exp (-x):ℂ)) =
        (fun x : ℝ => (Real.exp (-x):ℂ) * (x:ℂ)^(w-1)) := by
      funext x
      exact mul_comm _ _
    rw [MellinConvergent, he]
    exact Complex.GammaIntegral_convergent hw
  exact (MellinConvergent.comp_mul_left (f := fun x : ℝ => (Real.exp (-x):ℂ))
    (s := w) (a := (j:ℝ)+1) (by positivity)).mpr h

private theorem exponential_mellin (j : ℕ) {w : ℂ} (hw : 0 < w.re) :
    mellin (exponentialKernel j) w = Complex.Gamma w * ((j:ℂ)+1)^(-w) := by
  have h : mellin (exponentialKernel j) w =
      ((((j:ℝ)+1:ℝ):ℂ)^(-w)) • mellin (fun x : ℝ => (Real.exp (-x):ℂ)) w :=
    mellin_comp_mul_left (fun x : ℝ => (Real.exp (-x):ℂ)) w (by positivity)
  rw [h, ← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral hw]
  simp only [ofReal_add, ofReal_natCast, ofReal_one, smul_eq_mul, mul_comm]

private theorem mellin_finset {ι : Type*} (t : Finset ι) {f : ι → ℝ → ℂ}
    {w : ℂ} (h : ∀ i ∈ t, MellinConvergent (f i) w) :
    mellin (fun x => ∑ i ∈ t, f i x) w = ∑ i ∈ t, mellin (f i) w := by
  simp only [mellin, Finset.smul_sum]
  exact integral_finset_sum t h

private theorem convergent_finset {ι : Type*} (t : Finset ι) {f : ι → ℝ → ℂ}
    {w : ℂ} (h : ∀ i ∈ t, MellinConvergent (f i) w) :
    MellinConvergent (fun x => ∑ i ∈ t, f i x) w := by
  simp only [MellinConvergent, Finset.smul_sum]
  exact integrable_finset_sum t h

theorem etaPartial_eq_eulerSum (n : ℕ) {w : ℂ} (hw : 0 < w.re) :
    etaPartial n w = etaEulerSum n w := by
  let f (k j : ℕ) (x : ℝ) : ℂ := binomialWeight k j • exponentialKernel j x
  have h (k j : ℕ) : MellinConvergent (f k j) w :=
    (exponential_convergent j hw).const_smul (binomialWeight k j)
  have hRow (k : ℕ) : MellinConvergent (fun x => ∑ j ∈ Finset.range (k+1), f k j x) w :=
    convergent_finset _ (fun j _ => h k j)
  have hTerm (k j : ℕ) :
      mellin (f k j) w = Complex.Gamma w * (binomialWeight k j * ((j:ℂ)+1)^(-w)) := by
    change mellin (fun x => binomialWeight k j • exponentialKernel j x) w = _
    rw [mellin_const_smul, exponential_mellin j hw, smul_eq_mul]
    ring
  have hCol (k : ℕ) : mellin (fun x => ∑ j ∈ Finset.range (k+1), f k j x) w =
      Complex.Gamma w * ∑ j ∈ Finset.range (k+1), binomialWeight k j * ((j:ℂ)+1)^(-w) := by
    rw [mellin_finset _ (fun j _ => h k j), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hTerm k j)
  have hExp : fermiPartial n = fun x => ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k+1), f k j x := by
    funext x
    exact partial_expansion n x
  rw [etaPartial, hExp, mellin_finset _ (fun k _ => hRow k)]
  simp only [hCol, etaEulerSum, ← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ (Complex.Gamma_ne_zero_of_re_pos hw)

theorem eta_eulerSum_error (n : ℕ) {w : ℂ} (hr : 0 < w.re) (hi : 0 < w.im) :
    ‖eta w - etaEulerSum n w‖ ≤ (1/2:ℝ)^n * Real.Gamma w.re / ‖Complex.Gamma w‖ := by
  rw [← etaPartial_eq_eulerSum n hr]
  exact eta_remainder_bound n hr hi

theorem etaEulerSum_entire (n : ℕ) : Differentiable ℂ (etaEulerSum n) := by
  unfold etaEulerSum
  apply Differentiable.sum
  intro k _
  apply Differentiable.sum
  intro j _
  have hn : ((j:ℂ)+1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
  simp only [Complex.cpow_def_of_ne_zero hn]
  fun_prop

#print axioms etaPartial_eq_eulerSum
#print axioms eta_eulerSum_error

end DottieOriented.NativeSpectrum.EtaMellin
end
