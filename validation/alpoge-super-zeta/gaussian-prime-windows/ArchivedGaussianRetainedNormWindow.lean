import GaussianQuarticD4
import GaussianD4MinorExponents
import GaussianSqrtTriangleWindow

/-! The retained norm ratio for the actual quartic's closure, with
the arithmetic Frobenius and unramified input stated at each prime. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open ArithmeticFunction ArtinPrimitiveRootsConjecture FieldTarget Finset NumberField
open UniqueFactorizationMonoid

noncomputable section

/-- The signed degree-one trace. The two quadratic base roots are
fixed exactly when the first marked root stays in its antipodal pair. -/
def closurePrimeTrace (g : GaussianClosureGroup) : ℤ :=
  2 * ((if g = 1 then 1 else 0) - (if g = gaussianCentralElement then 1 else 0))

theorem closurePrimeTrace_eq_fixed_root_difference (g : GaussianClosureGroup) :
    closurePrimeTrace g =
      ((Finset.univ.filter (fun j : ZMod 4 => d4Action g j = j)).card : ℤ) -
        (if (d4Action g 0).val % 2 = 0 then 2 else 0) := by
  revert g
  decide +kernel

def retainedPrimes (x : ℝ) : Finset ℕ := by
  classical
  exact (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => gaussianSqrtTriangleScale x ≤ (p : ℝ) ∧ p.Prime)

private theorem retained_isPrime {x : ℝ} {p : ℕ} (hp : p ∈ retainedPrimes x) : p.Prime := by
  simpa only [retainedPrimes, mem_filter, mem_range] using
    (show p.Prime from (mem_filter.mp hp).2.2)

private def principalPrime (p : ℕ) : Ideal (𝓞 L) := Ideal.span ({(p : 𝓞 L)} : Set (𝓞 L))

/-- The distinct prime ideal factors of the rational principal ideal. -/
def closurePrimeFiber (p : ℕ) : Finset (Ideal (𝓞 L)) := by
  classical
  exact (normalizedFactors (principalPrime p)).toFinset

private def minorIdeal (x : ℝ) (label : GaussianClosureGroup) : Ideal (𝓞 L) :=
  sqrtFrobeniusMinorIdeal x (integerAction label).toRingHom

private def exponent (x : ℝ) (p : ℕ) : ℕ :=
  frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p

/-- The named arithmetic inputs for evaluating the retained part of
the determinant ideal in the degree-eight normal closure. -/
structure RetainedPrimeData (x : ℝ) (frob : ℕ → GaussianClosureGroup) : Prop where
  unramified : ∀ p ∈ retainedPrimes x, ∀ P ∈ closurePrimeFiber p, (p : 𝓞 L) ∉ P ^ 2
  localExponents : ∀ p ∈ retainedPrimes x, ∀ P ∈ closurePrimeFiber p, ∀ label,
    label = 1 ∨ label = gaussianCentralElement →
      (normalizedFactors (minorIdeal x label)).count P =
        if frob p = label then exponent x p else 0
  traceWeight : ∀ p ∈ retainedPrimes x,
    archivedGaussianPrimeWeight p = (closurePrimeTrace (frob p) : ℝ)

private theorem closurePrimeFiber_product {p : ℕ} (hp : p.Prime)
    (hUnr : ∀ P ∈ closurePrimeFiber p, (p : 𝓞 L) ∉ P ^ 2) :
    (∏ P ∈ closurePrimeFiber p, P) = principalPrime p := by
  classical
  have hP₀ : principalPrime p ≠ ⊥ := by
    simpa only [principalPrime, ne_eq, Ideal.span_singleton_eq_bot] using
      (Nat.cast_ne_zero.mpr hp.ne_zero : (p : 𝓞 L) ≠ 0)
  have hDistinct : (normalizedFactors (principalPrime p)).Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro P
    by_cases hP : P ∈ normalizedFactors (principalPrime p)
    · have hF : P ∈ closurePrimeFiber p := Multiset.mem_toFinset.mpr hP
      let : P.IsPrime := Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)
      have hLe : principalPrime p ≤ P := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP)
      have hNo : ¬ principalPrime p ≤ P ^ (1 + 1) := fun h =>
        hUnr P hF ((P ^ 2).span_singleton_le_iff_mem.mp h)
      exact le_of_eq (Ideal.count_normalizedFactors_eq (by simpa only [pow_one] using hLe) hNo)
    · rw [Multiset.count_eq_zero.mpr hP]
      decide
  change (closurePrimeFiber p).prod id = _
  rw [← Finset.prod_val, closurePrimeFiber, Multiset.toFinset_val, hDistinct.dedup,
    Ideal.prod_normalizedFactors_eq_self hP₀]

/-- Keep the prime power factors over the retained rational prime window. -/
def retainedMinorPart (x : ℝ) (label : GaussianClosureGroup) : Ideal (𝓞 L) := by
  classical
  exact ∏ p ∈ retainedPrimes x, ∏ P ∈ closurePrimeFiber p,
    P ^ (normalizedFactors (minorIdeal x label)).count P

theorem retainedMinorNorm_factorization {x : ℝ} {frob : ℕ → GaussianClosureGroup}
    (data : RetainedPrimeData x frob) (label : GaussianClosureGroup)
    (hLabel : label = 1 ∨ label = gaussianCentralElement) :
    (retainedMinorPart x label).absNorm =
      ∏ p ∈ retainedPrimes x, p ^ (8 * if frob p = label then exponent x p else 0) := by
  classical
  unfold retainedMinorPart
  rw [map_prod]
  apply prod_congr rfl
  intro p hp
  let e := if frob p = label then exponent x p else 0
  have hE : (∏ P ∈ closurePrimeFiber p, P ^ (normalizedFactors (minorIdeal x label)).count P) =
      (∏ P ∈ closurePrimeFiber p, P) ^ e := by
    rw [← Finset.prod_pow]
    exact prod_congr rfl (fun P hP => congrArg (fun t : ℕ => P ^ t)
      (data.localExponents p hp P hP label hLabel))
  rw [hE, map_pow, closurePrimeFiber_product (retained_isPrime hp) (data.unramified p hp),
    principalPrime, Ideal.absNorm_span_natCast, RingOfIntegers.rank, degree_eight, ← pow_mul]

private theorem log_retainedMinorNorm {x : ℝ} {frob : ℕ → GaussianClosureGroup}
    (data : RetainedPrimeData x frob) (label : GaussianClosureGroup)
    (hLabel : label = 1 ∨ label = gaussianCentralElement) :
    Real.log ((retainedMinorPart x label).absNorm : ℝ) =
      ∑ p ∈ retainedPrimes x, 8 * ((if frob p = label then exponent x p else 0 : ℕ) : ℝ) *
        Real.log (p : ℝ) := by
  classical
  rw [retainedMinorNorm_factorization data label hLabel, Nat.cast_prod, Real.log_prod]
  · apply sum_congr rfl
    intro p hp
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  · exact fun p hp => Nat.cast_ne_zero.mpr (pow_ne_zero _ (retained_isPrime hp).ne_zero)

private def omittedPrimeCenter (x : ℝ) : ℝ :=
  archivedGaussianPrimeCenter -
    ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => (p : ℝ) < gaussianSqrtTriangleScale x),
      archivedGaussianSignedPrimeWeight p / (p : ℝ)

/-- The retained logarithmic norm difference in the same normalization
and with the same small-prime centering as the quartic criterion. -/
def archivedGaussianRetainedNormWindow (x : ℝ) : ℝ :=
  gaussianSqrtTriangleScale x / (2 * x ^ 2) *
    (Real.log ((retainedMinorPart x gaussianCentralElement).absNorm : ℝ) -
      Real.log ((retainedMinorPart x 1).absNorm : ℝ)) -
    x / 3 * omittedPrimeCenter x

theorem archivedGaussianRetainedNormWindow_eq {x : ℝ} {frob : ℕ → GaussianClosureGroup}
    (data : RetainedPrimeData x frob) :
    archivedGaussianRetainedNormWindow x = archivedGaussianSqrtTriangleWindow x := by
  classical
  let k := gaussianSqrtTriangleScale x
  let f (p : ℕ) := archivedGaussianSignedPrimeWeight p *
    ((2 * k / x ^ 2) * (exponent x p : ℝ))
  have hSum : (∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => k ≤ (p : ℝ)), f p) =
      ∑ p ∈ retainedPrimes x, f p := by
    symm
    refine sum_subset (fun p hp => ?_) (fun p hp hnr => ?_)
    · simp only [retainedPrimes, mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    · have hh := mem_filter.mp hp
      have hn : ¬ p.Prime := fun hp' => hnr (mem_filter.mpr ⟨hh.1, hh.2, hp'⟩)
      simp [f, archivedGaussianSignedPrimeWeight, hn]
  unfold archivedGaussianRetainedNormWindow archivedGaussianSqrtTriangleWindow
  rw [archivedGaussianTriangleAtScale_eq_recentered]
  change k / (2 * x ^ 2) *
    (Real.log ((retainedMinorPart x gaussianCentralElement).absNorm : ℝ) -
      Real.log ((retainedMinorPart x 1).absNorm : ℝ)) -
    x / 3 * omittedPrimeCenter x = (∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => k ≤ (p : ℝ)),
      f p) - x / 3 * omittedPrimeCenter x
  rw [hSum, log_retainedMinorNorm data _ (Or.inr rfl), log_retainedMinorNorm data _ (Or.inl rfl),
    ← sum_sub_distrib, mul_sum]
  apply congrArg (fun y : ℝ => y - x / 3 * omittedPrimeCenter x)
  refine sum_congr rfl fun p hp => ?_
  have hp' := retained_isPrime hp
  simp only [f, archivedGaussianSignedPrimeWeight, vonMangoldt_apply_prime hp', if_pos hp',
    data.traceWeight p hp, closurePrimeTrace, Int.cast_mul, Int.cast_sub, Int.cast_ofNat]
  split_ifs <;> simp <;> ring

theorem archivedGaussianRetainedNormWindow_bound_iff {X₀ : ℝ}
    (hData : ∀ x ≥ X₀, ∃ frob, RetainedPrimeData x frob) :
    GaussianCutoffWindowBound archivedGaussianRetainedNormWindow ↔
      GaussianCutoffWindowBound archivedGaussianSqrtTriangleWindow := by
  apply gaussianCutoffWindowBound_iff_of_error (X₀ := X₀)
  intro θ _ _
  refine ⟨0, le_rfl, fun x hx => ?_⟩
  obtain ⟨_, h⟩ := hData x hx
  rw [archivedGaussianRetainedNormWindow_eq h, sub_self, abs_zero, zero_mul]

theorem quartic_rh_of_archived_gaussian_retained_norm_windows
    (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    {X₀ : ℝ} (hData : ∀ x ≥ X₀, ∃ frob, RetainedPrimeData x frob)
    (hcut : GaussianCutoffWindowBound archivedGaussianRetainedNormWindow) :
    DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_sqrt_triangle_windows hD hpos
    ((archivedGaussianRetainedNormWindow_bound_iff hData).mp hcut)

#print axioms closurePrimeTrace_eq_fixed_root_difference
#print axioms retainedMinorNorm_factorization
#print axioms archivedGaussianRetainedNormWindow_eq
#print axioms archivedGaussianRetainedNormWindow_bound_iff
#print axioms quartic_rh_of_archived_gaussian_retained_norm_windows

end
end GaussianQuarticClosure
end AlpogeSuperZeta
