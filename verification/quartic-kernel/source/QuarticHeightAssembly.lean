import QuarticStageCertificate
import QuarticMellinContinuation
import SuperZeta.GaussianSpectralTransfer
import SuperZeta.Recovery

namespace SuperZeta.QuarticHeightAssembly

open Complex Filter Set QuarticStageAxes
open scoped Topology
noncomputable section

def spectralMatch (s : ℂ) : Prop :=
  UnitSpectrum.continuation s = Reference.entireCorrection 1 s

/-- Transport a height set through the actual corrected spectrum, including its
    inverse. The height doubles in one direction and halves in the other. -/
theorem spectral_matches_at_heights (I : Set ℝ) :
    Set.BijOn (fun s : ℂ => 2 * s)
      {s | (0 < s.re ∧ s.re < 1 / 2) ∧ 2 * s.im ∈ I ∧ spectralMatch s}
      {w | (0 < w.re ∧ w.re < 1) ∧ w.im ∈ I ∧ riemannZeta w = 0} := by
  have re (s : ℂ) : (2 * s).re = 2 * s.re := by simp [Complex.mul_re]
  have im (s : ℂ) : (2 * s).im = 2 * s.im := by simp [Complex.mul_im]
  have forward : Set.MapsTo (fun s : ℂ => 2 * s)
      {s | (0 < s.re ∧ s.re < 1 / 2) ∧ 2 * s.im ∈ I ∧ spectralMatch s}
      {w | (0 < w.re ∧ w.re < 1) ∧ w.im ∈ I ∧ riemannZeta w = 0} := by
    rintro s ⟨⟨h₀,h₁⟩,ht,hS⟩
    exact ⟨⟨by rw [re]; linarith, by rw [re]; linarith⟩, (im s).symm ▸ ht,
      (UnitSpectrum.equality_iff_riemann_zero h₀ h₁).2.mp hS⟩
  refine ⟨forward, ?_, ?_⟩
  · intro s _ z _ he
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) he
  · rintro w ⟨⟨h₀,h₁⟩,ht,hz⟩
    let s := w / 2
    have he : 2 * s = w := by dsimp [s]; ring
    have hs₀ : 0 < s.re := by have h := congrArg Complex.re he; rw [re] at h; linarith
    have hs₁ : s.re < 1 / 2 := by have h := congrArg Complex.re he; rw [re] at h; linarith
    have ht' : 2 * s.im ∈ I := by rw [← im, he]; exact ht
    have hz' : riemannZeta (2 * s) = 0 := he.symm ▸ hz
    exact ⟨s, ⟨⟨hs₀,hs₁⟩,ht', (UnitSpectrum.equality_iff_riemann_zero hs₀ hs₁).2.mpr hz'⟩, he⟩

/-- The finite super-zeta recovery certificate controls height as well as
    horizontal displacement. The norm estimate and approximation error are the
    actual inputs checked on a recovery cell. -/
theorem height_error_of_recovery {s root value approximation : ℂ} {κ η : ℝ}
    (hκ : 0 < κ) (hlower : κ * ‖s - root‖ ≤ ‖value‖)
    (herror : ‖value - approximation‖ ≤ η) :
    |s.im - root.im| ≤ (η + ‖approximation‖) / κ := by
  simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (s - root)).trans
    (Recovery.residual_distance hκ hlower herror)

/-- Use the full spectral zero correspondence before applying the cumulative
    checkpoint result to the census of ordinary zeros. -/
theorem spectral_matches_on_line_of_cofinal_counts
    (T : ℕ → ℝ) (zeros : ℕ → Finset {w : ℂ // (0 < w.re ∧ w.re < 1) ∧ riemannZeta w = 0})
    (cofinal : ∀ t : ℝ, ∃ n, t ≤ T n)
    (complete : ∀ (w : {w : ℂ // (0 < w.re ∧ w.re < 1) ∧ riemannZeta w = 0}) n,
      |w.val.im| ≤ T n → w ∈ zeros n)
    (counts : ∀ n, (zeros n).card =
      ((zeros n).filter (fun w => w.val.re = 1 / 2)).card)
    {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2) (hs : spectralMatch s) :
    s.re = 1 / 4 := by
  have hw : (0 < (2 * s).re ∧ (2 * s).re < 1) ∧ riemannZeta (2 * s) = 0 := by
    rw [show (2 * s).re = 2 * s.re by simp [Complex.mul_re]]
    exact ⟨⟨by linarith, by linarith⟩,
      (UnitSpectrum.equality_iff_riemann_zero h₀ h₁).2.mp hs⟩
  have h := Recovery.on_line_of_cofinal_counts (fun w => |w.val.im|)
    (fun w => w.val.re = 1 / 2) T zeros cofinal complete counts ⟨2 * s, hw⟩
  change (2 * s).re = 1 / 2 at h
  simp [Complex.mul_re] at h
  linarith

/-- This transport uses the analytic field factorization and the actual spectral
    product at a single input of unrestricted height. -/
theorem field_zero_cases {field G : ℂ → ℂ}
    (d : GaussianSpectralTransfer.FactorizationData field G)
    {w : ℂ} (h₀ : 0 < w.re) (h₁ : w.re < 1) :
    field w = 0 ↔ spectralMatch (w / 2) ∨ GaussianSpectralTransfer.beta w = 0 ∨ G w = 0 := by
  have hS := GaussianSpectralTransfer.spectral_product d
    (s := w / 2) (by rw [Complex.div_ofNat_re]; linarith)
  rw [show 2 * (w / 2) = w by ring] at hS
  have hfactor := Spectrum.riemannFactor_ne_zero
    (s := w / 2) (by rw [Complex.div_ofNat_re]; linarith)
  have hm := mul_eq_zero (a := Spectrum.riemannFactor (w / 2)) (b := field w)
  simp only [hfactor, false_or] at hm
  rw [← hm, ← hS, mul_eq_zero, mul_eq_zero, or_assoc, sub_eq_zero, spectralMatch]

/-- Apply the two rational-factor zero-location statements at the same input. -/
theorem off_line_field_zero_iff {field G : ℂ → ℂ}
    (d : GaussianSpectralTransfer.FactorizationData field G)
    (hR : ∀ w : ℂ, 0 < w.re → w.re < 1 → riemannZeta w = 0 → w.re = 1 / 2)
    (hB : ∀ w : ℂ, 0 < w.re → w.re < 1 → GaussianSpectralTransfer.beta w = 0 → w.re = 1 / 2)
    {w : ℂ} (h₀ : 0 < w.re) (h₁ : w.re < 1) (hoff : w.re ≠ 1 / 2) :
    field w = 0 ↔ G w = 0 := by
  refine (field_zero_cases d h₀ h₁).trans ⟨?_, fun h => Or.inr (Or.inr h)⟩
  rintro (hs | hb | hg)
  · have h := (UnitSpectrum.equality_iff_riemann_zero (s := w / 2)
      (by rw [Complex.div_ofNat_re]; linarith) (by rw [Complex.div_ofNat_re]; linarith)).2.mp hs
    rw [show 2 * (w / 2) = w by ring] at h
    exact (hoff (hR w h₀ h₁ h)).elim
  · exact (hoff (hB w h₀ h₁ hb)).elim
  · exact hg

set_option maxRecDepth 20000 in
private theorem theta_center_ne : QuarticKernel.theta (1 / QuarticKernel.scale) ≠ 0 := by
  have hcell := List.all_eq_true.mp QuarticKernel.actual_cells_pass 0
    (List.mem_range.mpr (by decide))
  have hx : (0 : ℝ) ∈ Icc (QuarticGrid.node 0 : ℝ) (QuarticGrid.node (0+1) : ℝ) := by
    norm_num [QuarticGrid.node]
  have hk := (QuarticKernel.checkCell_sound (by decide) hcell QuarticKernel.actual_bin_count
    QuarticKernel.actual_checked_shells.2.1 QuarticKernel.actual_checked_shells.2.2
    QuarticKernel.actual_checked_shells.1 hx).1
  have hdata : QuarticGrid.data[0]?.getD (0,0) = (2101203285,2236894332) := by decide
  have hfloor : 0 < (QuarticGrid.lowerK 0 : ℝ) := by
    rw [QuarticGrid.lowerK, hdata]
    norm_num
  have hpos := hfloor.trans_le hk
  simpa [QuarticKernel.kernel] using hpos.ne'

/-- The completed quartic is tied to the Hecke continuation by a right-half-plane
    series equality. The Mellin and analytic-continuation results then carry the
    identification to every positive real part and every height. -/
theorem completion_eq {G : ℂ → ℂ}
    (hG : Differentiable ℂ G)
    (hseries : ∀ w : ℂ, 2 < w.re → G w = QuarticKernel.normSeries w)
    {w : ℂ} (hw : 0 < w.re) :
    QuarticSignedOrders.full w = (QuarticKernel.scale : ℂ) ^ w * Complex.Gamma w * G w := by
  let U : Set ℂ := {z | 0 < z.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected
  have hl : AnalyticOnNhd ℂ QuarticSignedOrders.full U := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    exact (QuarticKernel.mellin_differentiable_from_center theta_center_ne hz).differentiableWithinAt
  have hr : AnalyticOnNhd ℂ
      (fun z => (QuarticKernel.scale : ℂ) ^ z * Complex.Gamma z * G z) U := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    have hpow : DifferentiableAt ℂ (fun z : ℂ => (QuarticKernel.scale : ℂ) ^ z) z :=
      differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr QuarticKernel.scale_pos.ne'))
    have hg : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z (by
      intro n he
      have hh : 0 < z.re := hz
      rw [he] at hh
      simp at hh
      exact (not_lt_of_ge (Nat.cast_nonneg (α := ℝ) n)) hh)
    exact ((hpow.mul hg).mul (hG z)).differentiableWithinAt
  apply hl.eqOn_of_preconnected_of_eventuallyEq hr hconn (z₀ := 3) (by norm_num [U]) _ hw
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (3 : ℂ) ∈ {z : ℂ | 2 < z.re} by norm_num)] with z hz
  rw [hseries z hz]
  exact QuarticKernel.rightMellin hz

theorem completion_zero_iff {G : ℂ → ℂ}
    (hG : Differentiable ℂ G)
    (hseries : ∀ w : ℂ, 2 < w.re → G w = QuarticKernel.normSeries w)
    {w : ℂ} (hw : 0 < w.re) : QuarticSignedOrders.full w = 0 ↔ G w = 0 := by
  rw [completion_eq hG hseries hw]
  have hpow : (QuarticKernel.scale : ℂ) ^ w ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr QuarticKernel.scale_pos.ne'))
  simp [hpow, Complex.Gamma_ne_zero_of_re_pos hw]

/-- Once the fixed arithmetic factor is identified, an off-line field zero in
    the central strip must have height outside the verified rectangle. -/
theorem off_line_field_zero_height {field G : ℂ → ℂ}
    (d : GaussianSpectralTransfer.FactorizationData field G) (hG : Differentiable ℂ G)
    (hseries : ∀ w : ℂ, 2 < w.re → G w = QuarticKernel.normSeries w)
    (hR : ∀ w : ℂ, 0 < w.re → w.re < 1 → riemannZeta w = 0 → w.re = 1 / 2)
    (hB : ∀ w : ℂ, 0 < w.re → w.re < 1 → GaussianSpectralTransfer.beta w = 0 → w.re = 1 / 2)
    {w : ℂ} (hwidth : |w.re - 1/2| ≤ 1/20) (hoff : w.re ≠ 1/2) (hz : field w = 0) :
    27 / 100 < |w.im| := by
  obtain ⟨hl,hr⟩ := abs_le.mp hwidth
  have h₀ : 0 < w.re := by linarith
  have h₁ : w.re < 1 := by linarith
  have he := (off_line_field_zero_iff d hR hB h₀ h₁ hoff).mp hz
  by_contra! ht
  have hw : GaussianSideSign.point (w.re - 1/2) w.im = w := by
    apply Complex.ext
    · change (1/2 : ℝ) + (w.re - 1/2) = w.re
      ring
    · rfl
  have hc : QuarticKernel.completedQuartic (GaussianSideSign.point (w.re - 1/2) w.im) = 0 := by
    rw [hw]
    exact (completion_zero_iff hG hseries h₀).mpr he
  exact hoff (hw ▸ QuarticKernel.verified_quartic_zero_on_line hwidth ht hc)

/-- At an original super-zeta address, the two axes together test field
    vanishing off the line. The address can be inverted to recover the
    original field input and therefore its original height. -/
theorem off_line_field_zero_at_address {field G : ℂ → ℂ}
    (l : Launch) (d : GaussianSpectralTransfer.FactorizationData field G)
    (hG : Differentiable ℂ G)
    (hseries : ∀ w : ℂ, 2 < w.re → G w = QuarticKernel.normSeries w)
    (hR : ∀ w : ℂ, 0 < w.re → w.re < 1 → riemannZeta w = 0 → w.re = 1 / 2)
    (hB : ∀ w : ℂ, 0 < w.re → w.re < 1 → GaussianSpectralTransfer.beta w = 0 → w.re = 1 / 2)
    (x : QuarticTurn.Input) (hoff : x.val.re ≠ 1 / 2) :
    let q := QuarticOrderedTurns.J * QuarticOrderedTurns.reading (QuarticTurn.chart x)
    (QuarticTurn.chart.symm (QuarticTurn.chart x)).val.im = x.val.im ∧
      (field x.val = 0 ↔ q.imJ ^ 2 + q.imK ^ 2 = 0) := by
  obtain ⟨⟨hl,hu⟩,_⟩ := x.property
  change 15 / 64 ≤ (x.val/2).re at hl
  change (x.val/2).re ≤ 17 / 64 at hu
  simp only [Complex.div_ofNat_re] at hl hu
  have h₀ : 0 < x.val.re := by linarith
  have h₁ : x.val.re < 1 := by linarith
  dsimp only
  rw [QuarticTurn.same_input, axis_length_at_address l x, Complex.normSq_eq_zero,
    completion_zero_iff hG hseries h₀, off_line_field_zero_iff d hR hB h₀ h₁ hoff]
  exact ⟨rfl,Iff.rfl⟩

/-- Both Gaussian measurements can be compared at a freely chosen reference
    height. The theorem retains the actual point's height and the original
    spectral addresses. -/
theorem reflected_gaussian_disk_at_height (l : Launch) {T : ℝ} (hT : 203 ≤ T)
    {w : ℂ} (hw : w ∈ Metric.closedBall (GaussianDiskCount.rightCenter T) (31 / 2048)) :
    |w.im - (T - 1 / 512)| ≤ 31 / 2048 ∧
    (RingReversibility.mirror w).im = w.im ∧
    ‖RingReversibility.phi w‖ < ‖RingReversibility.phi (RingReversibility.mirror w)‖ ∧
    stageValue l (RingReversibility.mirror w) = star (stageValue l w) := by
  have hgeom : ‖w - GaussianDiskCount.rightCenter T‖ ≤ 31 / 2048 := hw
  have ht := (Complex.abs_im_le_norm _).trans hgeom
  simp only [Complex.sub_im, GaussianDiskCount.rightCenter] at ht
  refine ⟨ht, ?_, (QuarterReflectedReadings.disk_spectral_order hT hw).2, reflected_stage l w⟩
  simp [RingReversibility.mirror]

/-- The missing implication for localization into the fixed Dottie annuli can
    be supplied on the right half-strip. Reflection then handles the left
    at the same height. -/
theorem fixed_rings_of_right_localization
    (rightLoc : ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 →
      ReflectedGaussianReading.completed w = 0 → w ∈ GaussianRingMidpoint.rightRing)
    {w : ℂ} (h₀ : 0 < w.re) (h₁ : w.re < 1) (hoff : w.re ≠ 1 / 2)
    (hz : ReflectedGaussianReading.completed w = 0) :
    w ∈ GaussianRingMidpoint.rightRing ∨
      RingReversibility.mirror w ∈ GaussianRingMidpoint.rightRing := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · apply Or.inr
    apply rightLoc
    · simp [RingReversibility.mirror]; linarith
    · simp [RingReversibility.mirror]; linarith
    · rw [ReflectedGaussianReading.completed_mirror, hz]
      simp
  · exact Or.inl (rightLoc w hright h₁ hz)

/-- Assemble the proposed fixed-ring route for the field. The two geographic
    inputs are separated in the type: localization of strip zeros and
    survival of an axis in the right annulus. -/
theorem field_strip_rh_of_ring_localization {field G : ℂ → ℂ}
    (l : Launch) (d : GaussianSpectralTransfer.FactorizationData field G)
    (hG : Differentiable ℂ G)
    (hseries : ∀ w : ℂ, 2 < w.re → G w = QuarticKernel.normSeries w)
    (hR : ∀ w : ℂ, 0 < w.re → w.re < 1 → riemannZeta w = 0 → w.re = 1 / 2)
    (hB : ∀ w : ℂ, 0 < w.re → w.re < 1 → GaussianSpectralTransfer.beta w = 0 → w.re = 1 / 2)
    (locate : ∀ w : ℂ, 0 < w.re → w.re < 1 → w.re ≠ 1 / 2 → G w = 0 →
      w ∈ GaussianRingMidpoint.rightRing ∨
        RingReversibility.mirror w ∈ GaussianRingMidpoint.rightRing)
    (survives : ∀ w ∈ GaussianRingMidpoint.rightRing,
      (stageValue l w).re ≠ 0 ∨ (stageValue l w).im ≠ 0) :
    ∀ w : ℂ, 0 < w.re → w.re < 1 → field w = 0 → w.re = 1 / 2 := by
  intro w h₀ h₁ hz
  by_contra hoff
  have hg := (off_line_field_zero_iff d hR hB h₀ h₁ hoff).mp hz
  have hf := (completion_zero_iff hG hseries h₀).mpr hg
  have hclear (x : QuarticTurn.Input) (h : ReflectedGaussianReading.completed x.val ≠ 0)
      (hx : x.val = w) : False := by
    obtain ⟨⟨hl, hu⟩, _⟩ := x.property
    change 15 / 64 ≤ (x.val / 2).re at hl
    change (x.val / 2).re ≤ 17 / 64 at hu
    simp only [Complex.div_ofNat_re] at hl hu
    have hwidth : |x.val.re - 1 / 2| ≤ 1 / 20 := abs_le.mpr ⟨by linarith, by linarith⟩
    apply h
    rw [← QuarticSignedOrders.full_eq_completed x.val hwidth, hx]
    exact hf
  rcases locate w h₀ h₁ hoff hg with hr | hl
  · exact hclear (RingReversibility.inputOfRing hr)
      (excludes_right_and_mirror l survives hr).1 rfl
  · have hmirror : RingReversibility.mirror (RingReversibility.mirror w) = w := by
      simp [RingReversibility.mirror]
    exact hclear (ReflectedGaussianReading.reflectedInput (RingReversibility.inputOfRing hl))
      (excludes_right_and_mirror l survives hl).2 hmirror

end
end SuperZeta.QuarticHeightAssembly
