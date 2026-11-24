import SuperZeta.MellinContinuation
import SuperZeta.Stieltjes
import SuperZeta.ReferenceResolvent
import SuperZeta.RootBounds

/-! Integration by parts for the actual logarithmic determinant ratio on the
positive ray and reconstruction from the corresponding logarithmic derivatives. -/
noncomputable section
namespace SuperZeta.Ray
open Reference Complex MeasureTheory Filter Set
open scoped Topology

def relative (q t : ℝ) : ℂ := logKernel q (Real.sqrt t)
def weight (s : ℂ) (t : ℝ) : ℂ := (t:ℂ)^(-s)

theorem relative_bound {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) :
    ‖relative q t‖ ≤ q*t ∧ ‖relative q t‖ ≤ q := by
  have hb := logKernel_bound hq (Real.sqrt t)
  have hc := Real.cosh_pos (Real.sqrt t)
  have hc1 := Real.one_le_cosh (Real.sqrt t)
  have hs := Real.self_le_sinh_iff.mpr (Real.sqrt_nonneg t)
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg t) hs 2
  have hsc := Real.cosh_sq_sub_sinh_sq (Real.sqrt t)
  have hcs : Real.sqrt t^2 ≤ Real.cosh (Real.sqrt t)^2 := by linarith
  have hden : 1 ≤ Real.cosh (Real.sqrt t)^2 := one_le_pow₀ hc1
  constructor
  · apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hq
    rw [div_pow,Real.sq_sqrt ht]
    exact div_le_self ht hden
  · apply hb.trans
    rw [← mul_one q] at ⊢
    have hh : (Real.sqrt t/Real.cosh (Real.sqrt t))^2 ≤ 1 := by
      rw [div_pow, div_le_one (sq_pos_of_pos hc)]
      exact hcs
    nlinarith only [mul_le_mul_of_nonneg_left hh hq]

theorem boundary {q : ℝ} (hq : 0 ≤ q) {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    Tendsto (weight s * relative q) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (weight s * relative q) atTop (𝓝 0) := by
  constructor
  · apply squeeze_zero_norm' (a:=fun t : ℝ => q*t^(1-s.re))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' := mem_Ioi.mp ht
      rw [Pi.mul_apply, weight,norm_mul, norm_cpow_eq_rpow_re_of_pos ht', neg_re]
      have hp : t^(1-s.re) = t^(-s.re)*t := by
        rw [show 1-s.re = -s.re+1 by ring, Real.rpow_add ht', Real.rpow_one]
      rw [hp]
      calc
        _ ≤ t^(-s.re)*(q*t) := mul_le_mul_of_nonneg_left (relative_bound hq ht'.le).1 (by positivity)
        _ = _ := by ring
    · have h := (Real.continuousAt_rpow_const 0 (1-s.re) (Or.inr (by linarith))).tendsto
      simpa [Real.zero_rpow (by linarith : 1-s.re ≠ 0)] using
        ((h.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))).const_mul q)
  · apply squeeze_zero_norm' (a:=fun t : ℝ => q*t^(-s.re))
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      rw [Pi.mul_apply,weight,norm_mul,norm_cpow_eq_rpow_re_of_pos ht, neg_re, mul_comm q]
      exact mul_le_mul_of_nonneg_left (relative_bound hq ht.le).2 (by positivity)
    · simpa using (tendsto_rpow_neg_atTop hs).const_mul q

set_option maxHeartbeats 900000 in
/-- The integration-by-parts step with both endpoint terms evaluated from
the reciprocal determinant. The derivative may be supplied by a logarithmic
resolvent calculation on the open ray. -/
theorem integration_by_parts {q : ℝ} (hq : 0≤q) {s : ℂ} (hs : 0<s.re) (hs' : s.re<1)
    {v : ℝ → ℂ} (hv : ∀ t ∈ Ioi 0, HasDerivAt (relative q) (v t) t)
    (hi : IntegrableOn (weight s * v) (Ioi 0)) :
    Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ)*(∫ t in Ioi (0:ℝ), weight s t*v t) =
      correction q s := by
  have hsne : -s ≠ 0 := by intro h; have : s = 0 := neg_eq_zero.mp h; simp [this] at hs
  let u' := fun t : ℝ => -s*(t:ℂ)^(-s-1)
  have hu (x : ℝ) (hx : x ∈ Ioi 0) : HasDerivAt (weight s) (u' x) x :=
    hasDerivAt_ofReal_cpow_const (mem_Ioi.mp hx).ne' hsne
  have hm : IntegrableOn (fun t : ℝ => (t:ℂ)^(-s-1)*relative q t) (Ioi 0) := by
    simpa only [MellinConvergent,smul_eq_mul,relative] using correction_converges hq hs'
  have hI : IntegrableOn (u' * relative q) (Ioi 0) := by
    simpa only [IntegrableOn,u',Pi.mul_def,mul_assoc] using hm.const_mul (-s)
  obtain ⟨hb,ht⟩ := boundary hq hs hs'
  rw [integral_Ioi_mul_deriv_eq_deriv_mul hu hv hi hI hb ht]
  unfold correction mellin
  simp only [zero_sub,sub_zero,u',mul_assoc,integral_const_mul,smul_eq_mul]
  change _ = s * Complex.sin (↑Real.pi*s)/↑Real.pi *
    ∫ t in Ioi (0:ℝ), (t:ℂ)^(-s-1)*relative q t
  ring

private theorem integrable_tsum_norm {ι : Type*} [Countable ι] {μ : Measure ℝ}
    {F : ι → ℝ → ℂ} (hi : ∀ j, Integrable (F j) μ)
    (hs : Summable (fun j => ∫ t, ‖F j t‖ ∂μ)) :
    Integrable (fun t => ∑' j, F j t) μ := by
  have hmeas j : AEMeasurable (fun t => ‖F j t‖ₑ) μ := (hi j).1.enorm
  have hle (j : ι) : ∫⁻ t, ‖F j t‖ₑ ∂μ = ‖∫ t, ‖F j t‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral (fun t => ‖F j t‖₊) (hi j).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg (F j t)))]
    simp only [coe_nnnorm]
  have hfin : (∫⁻ t, ∑' j, ‖F j t‖ₑ ∂μ) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    simp_rw [hle]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hs.abs)
  have hsum : ∀ᵐ t ∂μ, Summable (fun j => ‖F j t‖) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) hfin] with t ht
    exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mp ht.ne
  apply (integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hmeas) hfin).mono'
  · apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
      (fun I => I.aestronglyMeasurable_sum fun j _ => (hi j).1)
    apply hsum.mono
    intro t ht
    simpa only [Finset.sum_apply, HasSum, SummationFilter.unconditional_filter] using ht.of_norm.hasSum
  · filter_upwards [hsum] with t ht
    have hh := ENNReal.coe_tsum (f:=fun j => ‖F j t‖₊) (NNReal.summable_coe.mp ht)
    simp only [enorm_eq_nnnorm, ← hh, ENNReal.coe_toReal,NNReal.coe_tsum]
    exact norm_tsum_le_tsum_norm ht

def resolvent {ι : Type*} (l : ι → ℂ) (t : ℝ) : ℂ := ∑' j, ((t:ℂ)+l j)⁻¹

/-- The spectral estimates are independent of the determinant equality. -/
structure SpectralData {ι : Type*} (l : ι → ℂ) (s : ℂ) : Prop where
  slit : ∀ j, l j ∈ slitPlane
  powers : Summable fun j => ‖l j‖^(-s.re)
  sector : ∃ d : ℝ, 0 < d ∧ ∀ j (t : ℝ), 0 ≤ t → d*(t+‖l j‖) ≤ ‖(t:ℂ)+l j‖

theorem spectral_integral {ι : Type*} [Countable ι] {l : ι → ℂ} {s : ℂ}
    (data : SpectralData l s) (hs : 0<s.re) (hu : s.re<1) :
    IntegrableOn (weight s * resolvent l) (Ioi 0) ∧
    (∑' j, (l j)^(-s)) = Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ)*
      ∫ t in Ioi (0:ℝ), weight s t*resolvent l t := by
  obtain ⟨d,hd,hm⟩ := data.sector
  have hi j := (Stieltjes.slit_integral hs hu (data.slit j)).1
  have hL : Summable (fun j => ∫ t in Ioi (0:ℝ), ‖Stieltjes.integrand s (l j) t‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun j => Stieltjes.sector_norm_integral hs hu (data.slit j) hd (hm j)) (data.powers.mul_left _)
  refine ⟨?_, (Stieltjes.countable_slit l data.slit hs hu hd hm data.powers).tsum_eq⟩
  simpa only [IntegrableOn,Stieltjes.integrand, div_eq_mul_inv, tsum_mul_left, weight, resolvent, Pi.mul_def]
    using integrable_tsum_norm hi hL

private def ref (n : ℕ) := (eigenvalue n : ℂ)

private theorem refdata {s : ℂ} (hs : 1/2 < s.re) : SpectralData ref s := by
  have hp (n : ℕ) : 0 < eigenvalue n := by unfold eigenvalue; positivity
  refine ⟨fun n => Complex.ofReal_mem_slitPlane.mpr (hp n), ?_, 1, by norm_num, ?_⟩
  · have h := (reference_hasSum hs).summable.norm.mul_left (1/2:ℝ)
    refine h.congr ?_
    intro n
    simp [ref, Complex.norm_cpow_eq_rpow_re_of_pos (hp n),
      abs_of_pos (hp n)]
  · intro n t ht
    simp only [ref, Complex.norm_of_nonneg (hp n).le, one_mul, ← Complex.ofReal_add]
    rw [Complex.norm_of_nonneg (add_nonneg ht (hp n).le)]

/-- All reference data and both integration endpoints are discharged. The
coupled spectral list enters through its sector, summability, and its
logarithmic derivative on the open real ray. -/
theorem reconstruction {ι : Type*} [Countable ι] {l : ι → ℂ} {q : ℝ} (hq : 0≤q)
    {s : ℂ} (hs : 1/2<s.re) (hu : s.re<1) (data : SpectralData l s)
    (coupled : ∀ t ∈ Ioi 0, HasDerivAt
      (fun y : ℝ => (Real.log ((Real.cosh (Real.sqrt y))^2+q*y):ℂ)) (resolvent l t) t) :
    (∑' j, (l j)^(-s)) - Reference.entireCorrection q s =
      Spectrum.riemannFactor s * riemannZeta (2*s) := by
  have hs0 : 0<s.re := by linarith
  obtain ⟨hl,hel⟩ := spectral_integral data hs0 hu
  obtain ⟨hr,her⟩ := spectral_integral (refdata hs) hs0 hu
  let v := fun t : ℝ => resolvent l t - 2*resolvent ref t
  have hv (t : ℝ) (ht : t ∈ Ioi 0) : HasDerivAt (relative q) (v t) t := by
    have h := (coupled t ht).sub (reference_resolvent ht).ofReal_comp
    have hrw : ((∑' n : ℕ, (2:ℝ)/(t+eigenvalue n):ℝ):ℂ) = 2*resolvent ref t := by
      simp [resolvent,ref,Complex.ofReal_tsum,div_eq_mul_inv,tsum_mul_left]
    rw [hrw] at h
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (mem_Ioi.mp ht)] with y hy
    have hlog := log_determinant_split hq (mem_Ioi.mp hy).le
    simp only [Real.log_pow,Nat.cast_ofNat] at *
    change relative q y = _
    simp only [relative, Pi.sub_apply]
    linear_combination -hlog
  have hfun : (fun t : ℝ => weight s t*v t) =
      fun t => weight s t*resolvent l t - 2*(weight s t*resolvent ref t) := by
    funext t
    dsimp [v]
    ring
  change Integrable (fun t => weight s t * resolvent l t) (volume.restrict (Ioi 0)) at hl
  change Integrable (fun t => weight s t * resolvent ref t) (volume.restrict (Ioi 0)) at hr
  have hi : IntegrableOn (weight s * v) (Ioi 0) := by
    change Integrable (fun t => weight s t*v t) _
    rw [hfun]
    exact hl.sub (hr.const_mul (2:ℂ))
  have ib := integration_by_parts hq hs0 hu hv hi
  rw [hfun, integral_sub hl (hr.const_mul (2:ℂ)), integral_const_mul] at ib
  have hsum := (reference_hasSum hs).tsum_eq
  rw [tsum_mul_left] at hsum
  change 2*(∑' n, (ref n)^(-s)) = _ at hsum
  rw [her] at hsum
  rw [hel, entireCorrection_eq hq hu, ← hsum]
  linear_combination ib

/-- A lower bound on the cosine of the half-angle supplies the exact
uniform-sector inequality used by the Stieltjes transform. -/
theorem margin_of_angle {z : ℂ} {d t : ℝ} (hd : 0≤d) (hd' : d≤1) (ht : 0≤t)
    (hang : (2*d^2-1)*‖z‖ ≤ z.re) : d*(t+‖z‖) ≤ ‖(t:ℂ)+z‖ := by
  have he : ‖(t:ℂ)+z‖^2 = t^2+2*t*z.re+‖z‖^2 := by
    simp [Complex.sq_norm,Complex.normSq_apply]
    ring
  have hd2 : 0≤1-d^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hd') (by linarith : 0≤1+d)]
  have hsq := mul_nonneg hd2 (sq_nonneg (t-‖z‖))
  have hh := mul_le_mul_of_nonneg_left hang ht
  have hn : (d*(t+‖z‖))^2 ≤ ‖(t:ℂ)+z‖^2 := by nlinarith only [he,hsq,hh]
  exact le_of_sq_le_sq hn (norm_nonneg _)

open scoped ComplexConjugate

private lemma join {α β : Type*} (f : α ⊕ β → ℝ)
    (h : Summable (f ∘ Sum.inl)) (k : Summable (f ∘ Sum.inr)) : Summable f :=
  (HasSum.sum (f:=f) h.hasSum k.hasSum).summable

/-- The indexed unit-coupling roots satisfy the sector and summability
estimates throughout the half-plane of absolute convergence. -/
theorem indexed_data {d : ℝ} (hd : 0<d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ QuartetRadius.level (t n)=2*Real.pi*(n+1))
    {s : ℂ} (hs : 1/2<s.re) : SpectralData (RootBounds.family d t) s := by
  have pos (n : ℕ) := RootBounds.squared_off_cut (Nat.succ_pos n)
    (roots n).1 (by simpa using (roots n).2)
  have mar (n : ℕ) := RootBounds.resolvent_margin (Nat.succ_pos n)
    (roots n).1 (by simpa using (roots n).2)
  have hpos : 0<d^2 := by positivity
  constructor
  · rintro (_ | n | n)
    · exact Complex.ofReal_mem_slitPlane.mpr hpos
    · exact pos n
    · rcases pos n with h | h
      · left; exact h
      · right
        change (conj (RootBounds.u (t n)^2)).im ≠ 0
        simpa only [Complex.conj_im, neg_ne_zero] using h
  · have h := RootBounds.norm_series (fun n => (roots n).2) hs
    refine join _ (hasSum_fintype _).summable ?_
    refine join _ h ?_
    change Summable (fun n => ‖conj (RootBounds.u (t n)^2)‖^(-s.re))
    simpa only [Complex.norm_conj] using h
  · refine ⟨1/2, by norm_num, ?_⟩
    rintro (_ | n | n) r hr
    · change 1/2*(r+‖((d^2:ℝ):ℂ)‖) ≤ ‖(r:ℂ)+((d^2:ℝ):ℂ)‖
      rw [Complex.norm_of_nonneg hpos.le, ← ofReal_add, Complex.norm_of_nonneg (by positivity)]
      linarith
    · exact mar n r hr
    · change 1/2*(r+‖conj (RootBounds.u (t n)^2)‖) ≤ ‖(r:ℂ)+conj (RootBounds.u (t n)^2)‖
      rw [← Complex.conj_ofReal r, ←map_add, Complex.norm_conj, Complex.norm_conj]
      exact mar n r hr

/-- At the original q=1 coupling the verified quartet estimates discharge
both the angular and convergence hypotheses. The remaining spectral input
identifies the logarithmic derivative of the coupled determinant. -/
theorem indexed_reconstruction {d : ℝ} (hd : 0<d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ QuartetRadius.level (t n)=2*Real.pi*(n+1))
    {s : ℂ} (hs : 1/2<s.re) (hu : s.re<1)
    (coupled : ∀ r ∈ Ioi 0, HasDerivAt
      (fun y : ℝ => (Real.log ((Real.cosh (Real.sqrt y))^2+y):ℂ))
      (resolvent (RootBounds.family d t) r) r) :
    (∑' j, (RootBounds.family d t j)^(-s)) - Reference.entireCorrection 1 s =
      Spectrum.riemannFactor s * riemannZeta (2*s) := by
  exact reconstruction (by norm_num : (0:ℝ)≤1) hs hu (indexed_data hd roots hs)
    (by simpa only [one_mul] using coupled)

end SuperZeta.Ray
