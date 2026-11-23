import QuarticHeightAssembly

namespace SuperZeta.QuarticCrossAnalysis
noncomputable section
open Complex QuarticOrderedTurns QuarticStageAxes QuarticHeightAssembly

def I : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def ij (q : Quaternion ℝ) := I * q * J
def ji (q : Quaternion ℝ) := J * q * I

theorem ij_difference (a b : ℂ) :
    ij (pack a b) - ji (pack a b) = pack ⟨2*b.im, 0⟩ ⟨0, 2*a.re⟩ := by
  apply Quaternion.ext <;>
    simp [ij, ji, I, J, pack, Quaternion.mul_re, Quaternion.mul_imI,
      Quaternion.mul_imJ, Quaternion.mul_imK] <;> ring

theorem ij_ne_ji_iff (a b : ℂ) :
    ij (pack a b) ≠ ji (pack a b) ↔ b.im ≠ 0 ∨ a.re ≠ 0 := by
  rw [← sub_ne_zero, ij_difference]
  constructor
  · intro h
    by_cases hb : b.im = 0
    · exact Or.inr (fun ha => h (by apply Quaternion.ext <;> simp [pack, hb, ha] <;> rfl))
    · exact Or.inl hb
  · rintro (hb | ha) he
    · have h := congrArg (fun q : Quaternion ℝ => q.re) he
      change 2 * b.im = 0 at h
      exact hb (by linarith)
    · have h := congrArg (fun q : Quaternion ℝ => q.imK) he
      change 2 * a.re = 0 at h
      exact ha (by linarith)

theorem ij_at_address (l : Launch) (x : QuarticTurn.Input) :
    ij (reading (QuarticTurn.chart x)) - ji (reading (QuarticTurn.chart x)) =
      pack ⟨2 * (HiddenQuarticQuaternion.total x.val).im, 0⟩
        ⟨0, 2 * (stageValue l x.val).re⟩ := by
  rw [stage_eq_completed, reading, QuarticTurn.same_reading]
  exact ij_difference _ _

/-- At a point on the outer measuring circle at an arbitrary reference
    height, recover the original input, the ordinary zeta zero test, both
    ordered products, and the two Hamilton coordinates at its reflection. -/
theorem outer_circle_cross_analysis (l : Launch) {T : ℝ} (hT : 203 ≤ T)
    {w : ℂ} (hw : w ∈ Metric.sphere (GaussianDiskCount.rightCenter T) (31 / 2048)) :
    ∃ x : QuarticTurn.Input, x.val = w ∧
      |w.im - (T - 1 / 512)| ≤ 31 / 2048 ∧
      let qm := reading (QuarticTurn.chart (ReflectedGaussianReading.reflectedInput x))
      let q := reading (QuarticTurn.chart x)
      (QuarticTurn.chart.symm (QuarticTurn.chart x)).val = w ∧
      (spectralMatch (w / 2) ↔ riemannZeta w = 0) ∧
      ij q - ji q = pack ⟨2 * (HiddenQuarticQuaternion.total w).im, 0⟩
        ⟨0, 2 * (stageValue l w).re⟩ ∧
      jk q - kj q = pack (2 * Complex.I * star (stageValue l w)) 0 ∧
      (J * qm).imJ = (J * q).imJ ∧ (J * qm).imK = -(J * q).imK := by
  have hd := Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le
  obtain ⟨hl, hr, ht⟩ := QuarterReflectedReadings.right_disk_coordinates hT hd
  let x : QuarticTurn.Input := ⟨w, by
    change (15 / 64 ≤ (w/2).re ∧ (w/2).re ≤ 17 / 64) ∧ 101 ≤ (w/2).im
    simp only [Complex.div_ofNat_re, Complex.div_ofNat_im]
    exact ⟨⟨by linarith, by linarith⟩, ht⟩⟩
  exact ⟨x, rfl, (reflected_gaussian_disk_at_height l hT hd).1,
    congrArg Subtype.val (QuarticTurn.same_input x),
    (both_tests_at_address l x).1, ij_at_address l x,
    (both_tests_at_address l x).2, axes_at_mirror_addresses l x⟩

end
end SuperZeta.QuarticCrossAnalysis
