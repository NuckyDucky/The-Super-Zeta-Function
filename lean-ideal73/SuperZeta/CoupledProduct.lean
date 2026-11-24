import SuperZeta.Ray
import SuperZeta.CoupledDeterminant

/-! The normalized product of the classified squared roots and its logarithmic
derivative on the positive ray. -/
namespace SuperZeta.Ray
open Complex Set Filter
open scoped Topology
noncomputable section

private theorem factor_slit {z : ℂ} (hz : z ∈ slitPlane) {r : ℝ} (hr : 0<r) :
    1+(r:ℂ)/z ∈ slitPlane := by
  have hn := normSq_pos.mpr (slitPlane_ne_zero hz)
  rcases hz with hx | hy
  · left
    simp [Complex.div_re]
    positivity
  · right
    simp [Complex.div_im, hr.ne', hy, hn.ne']

/-- For any spectral list with summable reciprocal norms and a uniform sector
bound, the canonical product converges and its derivative divided by the
product is the convergent sum of the resolvents. -/
theorem product_on_ray {ι : Type*} {l : ι → ℂ} (data : SpectralData l 1)
    {t : ℝ} (ht : 0<t) :
    let P (r : ℝ) := ∏' j, (1+(r:ℂ)/l j)
    HasProd (fun j => 1+(t:ℂ)/l j) (P t) ∧ P t ≠ 0 ∧
    HasDerivAt P (P t * resolvent l t) t := by
  let f (j : ι) (r : ℝ) := Complex.log (1+(r:ℂ)/l j)
  let g (j : ι) (r : ℝ) := ((r:ℂ)+l j)⁻¹
  have hinv : Summable (fun j => ‖l j‖⁻¹) := by
    simpa [Real.rpow_neg (norm_nonneg _)] using data.powers
  have hcomplex : Summable (fun j => (l j)⁻¹) := Summable.of_norm (by simpa using hinv)
  have hsum (r : ℝ) : Summable (fun j => f j r) := by
    apply Complex.summable_log_one_add_of_summable
    simpa only [div_eq_mul_inv] using hcomplex.mul_left (r:ℂ)
  have hfac (j) (r : ℝ) (hr : 0<r) := factor_slit (data.slit j) hr
  have prod (r : ℝ) (hr : 0<r) := Complex.hasProd_of_hasSum_log
    (fun j => slitPlane_ne_zero (hfac j r hr)) (hsum r).hasSum
  have hder (j) (r : ℝ) (hr : r ∈ Ioi 0) : HasDerivAt (f j) (g j r) r := by
    have hh := (((hasDerivAt_id (r:ℂ)).div_const (l j)).const_add 1).clog (hfac j r hr)
    apply hh.comp_ofReal.congr_deriv
    have hn := slitPlane_ne_zero (data.slit j)
    change 1 / l j / (1 + (r:ℂ)/l j) = ((r:ℂ)+l j)⁻¹
    field_simp [hn]
    ring
  obtain ⟨d,hd,margin⟩ := data.sector
  have hbound (j) (r : ℝ) (hr : r ∈ Ioi 0) : ‖g j r‖ ≤ d⁻¹ * ‖l j‖⁻¹ := by
    have hz := norm_pos_iff.mpr (slitPlane_ne_zero (data.slit j))
    change ‖((r:ℂ)+l j)⁻¹‖ ≤ _
    rw [← mul_inv, norm_inv]
    apply inv_anti₀ (mul_pos hd hz)
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (le_of_lt hr)) hd.le).trans (margin j r (le_of_lt hr))
  have ds := hasDerivAt_tsum_of_isPreconnected (hinv.mul_left d⁻¹) isOpen_Ioi
    isPreconnected_Ioi hder hbound ht (hsum t) ht
  have de := (Complex.hasDerivAt_exp _).scomp t ds
  have ep (r : ℝ) (hr : 0<r) : Complex.exp (∑' j, f j r) = ∏' j, (1+(r:ℂ)/l j) :=
    (prod r hr).tprod_eq.symm
  refine ⟨(prod t ht).multipliable.hasProd, (ep t ht).symm.trans_ne (Complex.exp_ne_zero _), ?_⟩
  apply HasDerivAt.congr_of_eventuallyEq _ (by
    filter_upwards [Ioi_mem_nhds ht] with r hr using (ep r hr).symm)
  simpa only [Function.comp_def, smul_eq_mul, ep t ht, g, resolvent, mul_comm] using de

/-- For the unit-coupling Dottie spectrum the sole product input is an
equality of values on the positive real ray. Differentiation, convergence
and the Mellin reconstruction are consequences. -/
theorem reconstruction_from_ray_product {d : ℝ} (hd : 0<d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ QuartetRadius.level (t n)=2*Real.pi*(n+1))
    (product_eq : ∀ r : ℝ, 0<r → (∏' j, (1+(r:ℂ)/RootBounds.family d t j)) =
      ((Real.cosh (Real.sqrt r)^2 + r : ℝ):ℂ))
    {s : ℂ} (hs : 1/2<s.re) (hu : s.re<1) :
    (∑' j, (RootBounds.family d t j)^(-s)) - Reference.entireCorrection 1 s =
      Spectrum.riemannFactor s * riemannZeta (2*s) := by
  apply indexed_reconstruction hd roots hs hu
  intro r hr
  have hrpos : 0<r := hr
  let P (y : ℝ) := ∏' j, (1+(y:ℂ)/RootBounds.family d t j)
  have hp := product_on_ray (indexed_data (s:=1) hd roots (by norm_num)) hr
  have slit : P r ∈ slitPlane := by
    rw [show P r = _ from product_eq r hr]
    exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
  have hl := (Complex.hasDerivAt_log slit).scomp r hp.2.2
  have heq : (fun y : ℝ => (Real.log (Real.cosh (Real.sqrt y)^2+y):ℂ)) =ᶠ[𝓝 r]
      (Complex.log ∘ P) := by
    filter_upwards [Ioi_mem_nhds hr] with y hy
    have hypos : 0<y := hy
    change _ = Complex.log (∏' j, _)
    rw [product_eq y hy, Complex.ofReal_log (by positivity)]
  apply (hl.congr_of_eventuallyEq heq).congr_deriv
  change (P r * resolvent _ r) * (P r)⁻¹ = _
  field_simp [slitPlane_ne_zero slit]

/-- The same spectral factors converge at every complex argument. Their
product vanishes exactly at the listed points, including arguments off the
positive integration ray. -/
theorem product_zero_iff_index {ι : Type*} {l : ι → ℂ} (data : SpectralData l 1) (w : ℂ) :
    Multipliable (fun j => 1-w/l j) ∧
    ((∏' j, (1-w/l j))=0 ↔ ∃ j, w=l j) := by
  have hinv : Summable (fun j => ‖l j‖⁻¹) := by
    simpa [Real.rpow_neg (norm_nonneg _)] using data.powers
  have hz : Summable (fun j => -w/l j) := by
    simpa only [div_eq_mul_inv] using
      (Summable.of_norm (by simpa using hinv) : Summable (fun j => (l j)⁻¹)).mul_left (-w)
  have hs : Summable (fun j => Complex.log (1-w/l j)) := by
    simpa only [neg_div, ← sub_eq_add_neg] using Complex.summable_log_one_add_of_summable hz
  refine ⟨Complex.multipliable_of_summable_log hs, ?_⟩
  have hf (j) : 1-w/l j=0 ↔ w=l j := by
    have hn := slitPlane_ne_zero (data.slit j)
    rw [sub_eq_zero, eq_comm,div_eq_iff hn,one_mul]
  constructor
  · contrapose!
    intro hall
    have hne (j) : 1-w/l j ≠ 0 := mt (hf j).mp (hall j)
    rw [← Complex.cexp_tsum_eq_tprod hne hs]
    exact Complex.exp_ne_zero _
  · rintro ⟨j,hj⟩
    exact (hasProd_zero_of_exists_eq_zero ⟨j,(hf j).mpr hj⟩).tprod_eq

/-- The determinant and its normalized spectral product have the same zero
set globally, before one invokes a genus-zero factorization theorem. -/
theorem determinant_zero_iff_product_zero {d : ℝ}
    (hd : d ∈ Ioo 0 (Real.pi/2) ∧ d = Real.cos d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ QuartetRadius.level (t n)=2*Real.pi*(n+1)) (w : ℂ) :
    Spectrum.coupledDet w=0 ↔ (∏' j, (1-w/RootBounds.family d t j))=0 := by
  rw [Spectrum.coupledDet_zero_iff_unique_index hd roots,
    (product_zero_iff_index (indexed_data (s:=1) hd.1.1 roots (by norm_num)) w).2]
  refine ⟨ExistsUnique.exists, ?_⟩
  rintro ⟨j,hj⟩
  exact ⟨j,hj,fun k hk => RootBounds.family_injective d roots (hk.symm.trans hj)⟩

/-- Apply a genus-zero factorization principle to the original spectrum.
The principle is an explicit hypothesis. All of its determinant-specific
inputs, including the global growth estimate and the entire zero list, are
supplied by the preceding kernel proofs. -/
theorem reconstruction_of_genus_zero
    (factorization : ∀ (E : ℂ → ℂ) (l : Unit ⊕ (ℕ ⊕ ℕ) → ℂ),
      (∀ w, AnalyticAt ℂ E w) → E 0=1 →
      (∀ w, ‖E w‖ ≤ Real.exp (2*Real.sqrt ‖w‖) + ‖w‖) →
      Function.Injective l → (∀ w, E w=0 ↔ ∃ j, w=l j) →
      (∀ w, E w=0 → deriv E w ≠ 0) → Summable (fun j => ‖l j‖⁻¹) →
      ∀ w, E w = ∏' j, (1-w/l j))
    {d : ℝ} (hd : d ∈ Ioo 0 (Real.pi/2) ∧ d = Real.cos d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ QuartetRadius.level (t n)=2*Real.pi*(n+1))
    {s : ℂ} (hs : 1/2<s.re) (hu : s.re<1) :
    (∑' j, (RootBounds.family d t j)^(-s)) - Reference.entireCorrection 1 s =
      Spectrum.riemannFactor s * riemannZeta (2*s) := by
  let l := RootBounds.family d t
  have hinj := RootBounds.family_injective d roots
  have zeros (w : ℂ) : Spectrum.coupledDet w=0 ↔ ∃ j, w=l j := by
    rw [Spectrum.coupledDet_zero_iff_unique_index hd roots]
    exact ⟨ExistsUnique.exists, fun ⟨j,hj⟩ =>
      ⟨j,hj,fun k hk => hinj (hk.symm.trans hj)⟩⟩
  have hinv : Summable (fun j => ‖l j‖⁻¹) := by
    simpa [l, Real.rpow_neg (norm_nonneg _)] using
      (indexed_data (s:=1) hd.1.1 roots (by norm_num)).powers
  have eqprod := factorization Spectrum.coupledDet l Spectrum.coupledDet_analytic
    Spectrum.coupledDet_zero Spectrum.coupledDet_growth hinj zeros
    (fun _ h => Spectrum.coupledDet_simple h) hinv
  apply reconstruction_from_ray_product hd.1.1 roots _ hs hu
  intro r hr
  simpa [l, neg_div] using (eqprod (-(r:ℂ))).symm.trans (Spectrum.coupledDet_on_ray hr.le)

end
end SuperZeta.Ray
