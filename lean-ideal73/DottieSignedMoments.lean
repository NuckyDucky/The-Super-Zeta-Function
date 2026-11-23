import DottieReferenceMoment
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The factorial-divided signed moments in the archived circle replay and
a bound on their truncated Taylor reconstruction. -/

open Complex Finset

namespace QuarticModel

noncomputable section

open SuperZeta.StirlingCorrection
open private referenceTerm from DottieReferenceMoment

private def signedTerm (a : ℕ → ℤ) (s : ℂ) (n : ℕ) : ℂ :=
  (a (n+1) : ℂ) * ((n+1 : ℕ) : ℂ)^(-s)

def signedDirichletPolynomial (a : ℕ → ℤ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ range N, signedTerm a s n

def signedMoment (a : ℕ → ℤ) (N : ℕ) (s : ℂ) (k : ℕ) : ℂ :=
  ∑ n ∈ range N, signedTerm a s n * ((-(Real.log (n+1)) : ℝ) : ℂ)^k / (k.factorial : ℂ)

def signedMomentMass (a : ℕ → ℤ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, |(a (n+1) : ℝ)| / Real.sqrt (n+1)

private theorem exp_tail_factorial (z : ℂ) (K : ℕ) :
    ‖Complex.exp z - ∑ k ∈ range K, z^k / (k.factorial : ℂ)‖ ≤
      ‖z‖^K / (K.factorial : ℝ) * Real.exp ‖z‖ := by
  refine (Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z K).trans ?_
  let y := ‖z‖
  let f (k : ℕ) := y^k / (k.factorial : ℝ)
  have hs : HasSum f (Real.exp y) := by
    unfold f
    rw [Real.exp_eq_exp_ℝ, ← NormedSpace.expSeries_apply_eq_div' (𝕂 := ℝ) y]
    exact NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) y
  have ht := (summable_nat_add_iff K).mpr hs.summable
  have hsplit := hs.summable.sum_add_tsum_nat_add K
  rw [hs.tsum_eq] at hsplit
  have hsum : Real.exp y - ∑ k ∈ range K, f k = ∑' k, f (k+K) := by linarith
  change Real.exp y - ∑ k ∈ range K, f k ≤ f K * Real.exp y
  rw [hsum, ← (hs.mul_left (f K)).tsum_eq]
  apply ht.tsum_le_tsum _ (hs.mul_left (f K)).summable
  intro k
  have hfac : k.factorial * K.factorial ≤ (k+K).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  calc
    f (k+K) ≤ y^(k+K) / ((k.factorial * K.factorial : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg z) _) (by positivity) (by exact_mod_cast hfac)
    _ = f K * f k := by
      simp only [f, pow_add, Nat.cast_mul, div_mul_div_comm]
      ring

private theorem signedTerm_shift (a : ℕ → ℤ) (s d : ℂ) (n : ℕ) :
    signedTerm a (s+d) n = signedTerm a s n * Complex.exp (d * ((-(Real.log (n+1)) : ℝ) : ℂ)) := by
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have he : ((n+1 : ℕ) : ℂ)^(-d) = Complex.exp (d * ((-(Real.log (n+1)) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hn, ← Complex.natCast_log, Complex.ofReal_neg]
    congr 1
    push_cast
    ring
  simp only [signedTerm, neg_add, Complex.cpow_add _ _ hn, he, mul_assoc]

private theorem signedTerm_norm {a : ℕ → ℤ} {s : ℂ} (hs : s.re = 1/2) (n : ℕ) :
    ‖signedTerm a s n‖ = |(a (n+1) : ℝ)| / Real.sqrt (n+1) := by
  rw [signedTerm, norm_mul, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs,
    ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Complex.neg_re, hs, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  push_cast
  rfl

/-- With the archived factorial normalization, the Taylor error is bounded
by the absolute coefficient mass times `exp q * q^K/K!`, where
`q = ‖d‖ log N`. -/
theorem signed_dirichlet_taylor_bound {a : ℕ → ℤ} {N : ℕ}
    {s : ℂ} (hs : s.re = 1/2) (d : ℂ) (K : ℕ) :
    let q := ‖d‖ * Real.log N
    ‖signedDirichletPolynomial a N (s+d) - ∑ k ∈ range K, signedMoment a N s k * d^k‖ ≤
      signedMomentMass a N * (q^K / (K.factorial : ℝ) * Real.exp q) := by
  let q := ‖d‖ * Real.log N
  let y (n : ℕ) := d * ((-(Real.log (n+1)) : ℝ) : ℂ)
  have hshift : signedDirichletPolynomial a N (s+d) =
      ∑ n ∈ range N, signedTerm a s n * Complex.exp (y n) := by
    exact sum_congr rfl (fun n _ => signedTerm_shift a s d n)
  have htaylor : (∑ k ∈ range K, signedMoment a N s k * d^k) =
      ∑ n ∈ range N, signedTerm a s n * ∑ k ∈ range K, (y n)^k / (k.factorial : ℂ) := by
    simp only [signedMoment, sum_mul, mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro k _
    dsimp only [y]
    rw [mul_pow]
    ring
  change ‖_‖ ≤ signedMomentMass a N * (q^K / (K.factorial : ℝ) * Real.exp q)
  rw [hshift, htaylor, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (norm_sum_le _ _).trans ?_
  rw [signedMomentMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  have hnN : (n+1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hn)
  have hlog : 0 ≤ Real.log (n+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hy : ‖y n‖ ≤ q := by
    change ‖d * ((-(Real.log (n+1)) : ℝ) : ℂ)‖ ≤ q
    rw [norm_mul, Complex.ofReal_neg, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hnN) (norm_nonneg _)
  rw [norm_mul, signedTerm_norm hs]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (exp_tail_factorial (y n) K).trans ?_
  gcongr

/-- Recover the exact archived normalization from the unscaled Dirichlet
polynomial used to record the moments. -/
theorem dottieReferencePolynomial_eq_scaled_dirichlet :
    dottieReferencePolynomial = (archivedThetaScale : ℂ)^dottieReferencePoint *
      signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint := by
  rw [dottieReferencePolynomial, Finset.sum_range_succ', signedDirichletPolynomial,
    Finset.mul_sum, show referenceTerm 0 = 0 from if_pos rfl, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  have hn : n+1 ≠ 0 := Nat.succ_ne_zero n
  rw [referenceTerm, if_neg hn, signedTerm, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg archivedThetaScale_pos.le (Nat.cast_nonneg (α := ℝ) (n+1)),
    Complex.ofReal_natCast, Complex.cpow_neg]
  ring

/-- For the original reference at `s₀ − i/512`, the 17 deposited moments
have a Taylor error at most `10⁻³⁸` times the absolute mass. -/
theorem dottie_reference_taylor_bound :
    let s₀ : ℂ := 1/2 + (dottieHeight : ℂ)*I
    let d : ℂ := -(1/512 : ℂ)*I
    ‖signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint -
      ∑ k ∈ range 17, signedMoment archivedLatticeCoeff 276824064 s₀ k * d^k‖ ≤
      signedMomentMass archivedLatticeCoeff 276824064 / 10^38 := by
  let s₀ : ℂ := 1/2 + (dottieHeight : ℂ)*I
  let d : ℂ := -(1/512 : ℂ)*I
  have hs : s₀.re = 1/2 := by norm_num [s₀, Complex.mul_re]
  have hpoint : s₀+d = dottieReferencePoint := by
    unfold s₀ d dottieReferencePoint
    push_cast
    ring
  have hd : ‖d‖ = 1/512 := by norm_num [d, norm_mul, norm_div, Complex.norm_ofNat]
  have hlog : Real.log 276824064 < 20 := by
    have hpow : (2.7 : ℝ)^20 ≤ Real.exp 20 := by
      rw [show (20:ℝ) = (20:ℕ) * (1:ℝ) by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
    exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr ((by norm_num : (276824064:ℝ) < 2.7^20).trans_le hpow)
  let q := ‖d‖*Real.log 276824064
  have hq : q ≤ 1/25 := by dsimp [q]; rw [hd]; linarith
  have hq₀ : 0 ≤ q := mul_nonneg (norm_nonneg _) (Real.log_nonneg (by norm_num))
  have he : Real.exp q ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2)]
    exact Real.exp_le_exp.mpr (hq.trans (by linarith [Real.log_two_gt_d9]))
  have herror : q^17 / ((17 : ℕ).factorial : ℝ) * Real.exp q ≤ 1 / 10^38 := by
    calc
      _ ≤ (1/25 : ℝ)^17 / ((17 : ℕ).factorial : ℝ) * 2 := by gcongr
      _ ≤ _ := by norm_num [Nat.factorial]
  have hm : 0 ≤ signedMomentMass archivedLatticeCoeff 276824064 := by
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have h := signed_dirichlet_taylor_bound (a := archivedLatticeCoeff) (N := 276824064) hs d 17
  change ‖_‖ ≤ signedMomentMass archivedLatticeCoeff 276824064 *
    (q^17 / ((17:ℕ).factorial : ℝ) * Real.exp q) at h
  rw [hpoint] at h
  exact h.trans (by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left herror hm)

private theorem abs_cast_jacobi_le_one (x : ℤ) (b : ℕ) : |(jacobiSym x b : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy x b with h | h | h <;> rw [h] <;> norm_num

private theorem abs_archived_sign_le_one (z : GaussianInt) : |(archivedGaussianSign z : ℝ)| ≤ 1 := by
  simp only [archivedGaussianSign, Int.cast_mul, abs_mul]
  calc
    _ ≤ (1 : ℝ) * 1 * 1 := by gcongr <;> apply abs_cast_jacobi_le_one
    _ = _ := by norm_num

/-- Each archived row has signed weight of magnitude at most one. At norm
`n` the row enumeration has at most `√n` terms. -/
theorem archivedMomentMass_le_cutoff (N : ℕ) :
    signedMomentMass archivedLatticeCoeff N ≤ N := by
  have hcoeff (n : ℕ) : |(archivedLatticeCoeff n : ℝ)| ≤ Real.sqrt n := by
    rw [archivedLatticeCoeff, Int.cast_sum, ← Real.norm_eq_abs]
    refine (norm_sum_le _ _).trans ?_
    calc
      (∑ j ∈ range n.sqrt, ‖(archivedLatticeRow n j : ℝ)‖) ≤
          ∑ _j ∈ range n.sqrt, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [archivedLatticeRow, Int.cast_ite, Int.cast_zero, Real.norm_eq_abs]
        split
        · exact abs_archived_sign_le_one _
        · norm_num
      _ = (n.sqrt : ℝ) := by simp
      _ ≤ Real.sqrt n := (Real.le_sqrt (by positivity) (by positivity)).mpr
        (by exact_mod_cast Nat.sqrt_le' n)
  unfold signedMomentMass
  calc
    _ ≤ ∑ _n ∈ range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      exact (div_le_one (by positivity)).mpr (by exact_mod_cast hcoeff (n+1))
    _ = _ := by simp

/-- Absolute error at the reference point, using only the row count and
the exact published cutoff. -/
theorem dottie_reference_taylor_absolute_error :
    let s₀ : ℂ := 1/2 + (dottieHeight : ℂ)*I
    let d : ℂ := -(1/512 : ℂ)*I
    ‖signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint -
      ∑ k ∈ range 17, signedMoment archivedLatticeCoeff 276824064 s₀ k * d^k‖ < 3 / 10^30 := by
  dsimp only
  refine dottie_reference_taylor_bound.trans_lt ?_
  exact (div_le_div_of_nonneg_right (archivedMomentMass_le_cutoff _) (by norm_num)).trans_lt (by norm_num)

#print axioms signed_dirichlet_taylor_bound
#print axioms dottieReferencePolynomial_eq_scaled_dirichlet
#print axioms dottie_reference_taylor_bound
#print axioms archivedMomentMass_le_cutoff
#print axioms dottie_reference_taylor_absolute_error

end
end QuarticModel
