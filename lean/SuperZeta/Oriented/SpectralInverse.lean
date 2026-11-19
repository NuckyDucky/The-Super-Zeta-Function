import SuperZeta.Oriented.OrderedStages
import SuperZeta.Oriented.TraceRecovery
import SuperZeta.Oriented.TwistedGrowth
import SuperZeta.Oriented.GrowthCount
import SuperZeta.Oriented.GrowthProduct
import SuperZeta.Oriented.ProductTrace
import SuperZeta.Oriented.BranchInverse

/-! Integration: take the zero set of the actual twisted entire determinant
as the index type. Simplicity, reciprocal summability and the full canonical
product are derived before either probe is used to recover a cap orbit. -/
noncomputable section
namespace DottieOriented.SpectralInverse
open DottieOriented TraceRecovery Complex Filter Set
open scoped Topology ComplexConjugate

abbrev Roots (φ : ℝ) := {v : ℂ // signedDet 1 φ v = 0}

/-- Each element of this index type is a zero, and every zero occurs once.
At a regular phase all zeros are simple. -/
theorem full_twisted_spectrum {φ : ℝ} (hc : Real.cos φ ≠ 0) :
    (∀ j : Roots φ, deriv (signedDet 1 φ) j.val ≠ 0) ∧
    (Summable fun j : Roots φ => ‖j.val‖⁻¹) ∧
    (∀ v : ℂ, signedDet 1 φ v = ∏' j : Roots φ, (1-v/j.val)) := by
  have entire : Differentiable ℂ (signedDet 1 φ) := fun v => (signedDet_analytic 1 φ v).differentiableAt
  obtain ⟨K,hK,hgrowth⟩ := signedDet_growth hc
  have hs := RootCount.summable_reciprocal (signedDet 1 φ) (fun j : Roots φ => j.val)
    entire (signedDet_at_zero hc) Subtype.val_injective (fun j => j.property) hK (fun v _ => hgrowth v)
  have simple (j : Roots φ) := signedDet_simple hc j.property
  refine ⟨simple, hs, ?_⟩
  apply SuperZeta.Factorization.eq_tprod_of_sqrt_growth _ _ entire (signedDet_at_zero hc)
    ⟨K,hK,fun v _ => hgrowth v⟩ Subtype.val_injective _ simple hs
  exact fun v => ⟨fun h => ⟨⟨v,h⟩,rfl⟩,fun ⟨j,e⟩ => e ▸ j.property⟩

def rootSum (φ : ℝ) : ℂ := ∑' j : Roots φ, j.val⁻¹

/-- The complete, absolutely convergent sum equals the derivative measurement. -/
theorem rootSum_is_trace {φ : ℝ} (hc : Real.cos φ ≠ 0) :
    rootSum φ = (firstTrace 1 φ : ℂ) := by
  obtain ⟨_,hs,prod⟩ := full_twisted_spectrum hc
  have identity := reciprocal_sum_of_local_product (fun j : Roots φ => j.val)
    (by simpa using hs) (Eventually.of_forall prod)
  change (∑' j : Roots φ, j.val⁻¹) = _
  rw [identity,firstTrace,(signedDet_hasDerivAt_zero 1 φ).deriv]
  simp only [Complex.ofReal_re, Complex.ofReal_neg]

def rootProbes (θ : ℝ) : ℝ × ℝ :=
  ((rootSum (-(θ + Real.pi/6))).re, (rootSum (-(θ - Real.pi/6))).re)

theorem rootProbes_eq_traces {θ : ℝ}
    (hp : Real.cos (θ + Real.pi/6) ≠ 0) (hm : Real.cos (θ - Real.pi/6) ≠ 0) :
    rootProbes θ = traceProbes (Real.pi/6) θ := by
  simp only [rootProbes,rootSum_is_trace (φ:=-(θ + Real.pi/6)) (by simpa only [Real.cos_neg] using hp),
    rootSum_is_trace (φ:=-(θ - Real.pi/6)) (by simpa only [Real.cos_neg] using hm),Complex.ofReal_re,
    traceProbes,nativeTrace]

def markFromProbes (M : ℝ × ℝ) : ℂ :=
  ((sineReading M.1 - sineReading M.2 : ℝ) : ℂ) +
    (((sineReading M.1 + sineReading M.2) / Real.sqrt 3 : ℝ) : ℂ) * I

theorem rootProbes_recover_mark {θ : ℝ}
    (hp : Real.cos (θ + Real.pi/6) ≠ 0) (hm : Real.cos (θ - Real.pi/6) ≠ 0) :
    markFromProbes (rootProbes θ) = exp ((θ : ℂ)*I) := by
  rw [rootProbes_eq_traces hp hm]
  have hpq := recover_pi_div_six hp hm
  have hx := congrArg Prod.fst hpq
  have hy := congrArg Prod.snd hpq
  dsimp only [Prod.fst, Prod.snd] at hx hy
  rw [markFromProbes, hx, hy, exp_mul_I, ofReal_cos, ofReal_sin]

def capAngle (y : ℝ) := nativeAngle y (capRoot y)

/-- At a regular pair of probes the difference in their ordering reads the
sign of the missing horizontal coordinate. -/
theorem rootProbes_order {θ : ℝ}
    (hp : Real.cos (θ + Real.pi/6) ≠ 0) (hm : Real.cos (θ - Real.pi/6) ≠ 0) :
    (rootProbes θ).2 < (rootProbes θ).1 ↔ 0 < Real.cos θ := by
  have pos {x : ℝ} (h : Real.cos x ≠ 0) : 0 < 1-Real.sin x := by
    have hsq := Real.sin_sq_add_cos_sq x
    have hn := sq_pos_of_ne_zero h
    nlinarith [Real.sin_le_one x, sq_nonneg (Real.sin x-1)]
  rw [rootProbes_eq_traces hp hm]
  change nativeTrace (θ-Real.pi/6) < nativeTrace (θ+Real.pi/6) ↔ _
  rw [nativeTrace_eq hm, nativeTrace_eq hp, div_lt_div_iff₀ (pos hm) (pos hp),
    Real.sin_add, Real.sin_sub, Real.sin_pi_div_six]
  constructor <;> intro h <;> linarith

theorem rootProbes_at_pivot : rootProbes (-(Real.pi/2)) = (8-4*Real.sqrt 3, 8-4*Real.sqrt 3) := by
  obtain ⟨hp,hm⟩ := probeGuards_pi_div_six (θ:=-(Real.pi/2)) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])
  exact (rootProbes_eq_traces hp hm).trans traceProbes_pi_div_six_at_pivot

theorem rootProbes_cap_angle (y : ℝ)
    (hp : Real.cos (capAngle y + Real.pi/6) ≠ 0)
    (hm : Real.cos (capAngle y - Real.pi/6) ≠ 0) :
    (markFromProbes (rootProbes (capAngle y))).arg = capAngle y := by
  rw [rootProbes_recover_mark hp hm, exp_mul_I]
  exact arg_cos_add_sin_mul_I (arg_mem_Ioc _)

/-- Equal measured root sums on a calibrated branch identify the physical
parameter and the full 640-stage history of its cap-rooted pair. -/
theorem equal_packets_recover_ordered_lifts {a b y k : ℝ}
    (hc : ContinuousOn capAngle (Icc a b)) (hs : ∀ x ∈ Ioo a b, 0 < deriv capAngle x)
    (hy : y ∈ Icc a b) (hk : k ∈ Icc a b)
    (gy : Real.cos (capAngle y + Real.pi/6) ≠ 0 ∧ Real.cos (capAngle y - Real.pi/6) ≠ 0)
    (gk : Real.cos (capAngle k + Real.pi/6) ≠ 0 ∧ Real.cos (capAngle k - Real.pi/6) ≠ 0)
    (readings : rootProbes (capAngle k) = rootProbes (capAngle y)) :
    k = y ∧ orbitLifts (I*(k:ℂ)) (capRoot k, conj (capRoot k)) 640 =
        orbitLifts (I*(y:ℂ)) (capRoot y, conj (capRoot y)) 640 := by
  have angles := congrArg (fun p => (markFromProbes p).arg) readings
  change (markFromProbes (rootProbes (capAngle k))).arg =
    (markFromProbes (rootProbes (capAngle y))).arg at angles
  rw [rootProbes_cap_angle k gk.1 gk.2, rootProbes_cap_angle y gy.1 gy.2] at angles
  have mono := strictMonoOn_of_deriv_pos (convex_Icc a b) hc (by simpa only [interior_Icc] using hs)
  have same := mono.injOn hk hy angles
  exact ⟨same, same ▸ rfl⟩

/-- A clockwise shift using the root data and a new measurement on the turned
orbit. The two external analytic conditions are continuity and positivity of
the slope of the actual cap angle on the selected parameter interval. -/
theorem return_from_fresh_root_sums {a b y : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn capAngle (Icc a b)) (hs : ∀ x ∈ Ioo a b, 0 < deriv capAngle x)
    (hy : y ∈ Icc a b)
    (h0 : Real.cos (capAngle y + Real.pi/6) ≠ 0)
    (h1 : Real.cos (capAngle y - Real.pi/6) ≠ 0)
    (range : capAngle y - Real.pi/6 ∈ Icc (capAngle a) (capAngle b))
    (sector : capAngle y - Real.pi/6 ∈ Ioo (-2*Real.pi/3) (-Real.pi/3)) :
    ∃ z ∈ Icc a b,
      capAngle z = (markFromProbes (rootProbes (capAngle y))).arg - Real.pi/6 ∧
      ∀ k ∈ Icc a b, (capAngle k = (markFromProbes (rootProbes (capAngle z))).arg + Real.pi/6 ↔ k = y) := by
  obtain ⟨z,⟨⟨hz,ht⟩,back⟩,_⟩ :=
    Branch.return_angle_round_trip hab capAngle hc hs hy range
  have hsect := ht.symm ▸ sector
  obtain ⟨hp,hm⟩ := probeGuards_pi_div_six hsect.1 hsect.2
  refine ⟨z,hz, by rwa [rootProbes_cap_angle y h0 h1], ?_⟩
  intro k hk
  rw [rootProbes_cap_angle z hp hm]
  exact ⟨back k hk,fun he => by rw [he,ht]; ring⟩

end DottieOriented.SpectralInverse
