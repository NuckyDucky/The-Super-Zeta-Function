import DedekindCyclotomicLocalEuler
import DedekindEulerByRationalPrime
import DedekindMixedThetaSignedRings
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Ideal NumberField Set

noncomputable section

local instance (m : ℕ) [NeZero m] : Fintype (DirichletCharacter ℂ m) := Fintype.ofFinite _

private def cyclotomicPrimeEmbedding (m : ℕ) : {p // p ∈ Nat.primeFactors m} ↪ Nat.Primes :=
  ⟨fun p ↦ ⟨p.val, (Nat.mem_primeFactors.mp p.property).1⟩,
    fun _ _ h ↦ Subtype.ext (congrArg (fun p : Nat.Primes ↦ p.val) h)⟩

private def cyclotomicBadPrimes (m : ℕ) : Finset Nat.Primes :=
  (Nat.primeFactors m).attach.map (cyclotomicPrimeEmbedding m)

private theorem mem_cyclotomicBadPrimes (m : ℕ) [NeZero m] (p : Nat.Primes) :
    p ∈ cyclotomicBadPrimes m ↔ p.val ∣ m := by
  classical
  unfold cyclotomicBadPrimes
  constructor
  · intro h
    obtain ⟨q, _, hq⟩ := Finset.mem_map.mp h
    have he : q.val = p.val := congrArg (fun r : Nat.Primes ↦ r.val) hq
    exact he ▸ (Nat.mem_primeFactors.mp q.property).2.1
  · intro h
    let q : {n // n ∈ Nat.primeFactors m} :=
      ⟨p.val, Nat.mem_primeFactors.mpr ⟨p.property, h, NeZero.ne m⟩⟩
    exact Finset.mem_map.mpr ⟨q, Finset.mem_attach _ _, Subtype.ext rfl⟩

private def cyclotomicPrimeEulerDenominator (m : ℕ) [NeZero m] (p : Nat.Primes) (w : ℂ) : ℂ :=
  ∏ P ∈ IsDedekindDomain.primesOverFinset (span {(p.val : ℤ)}) (𝓞 (CyclotomicField m ℚ)),
    (1 - ((p.val : ℂ) ^ (-w)) ^ P.inertiaDeg ℤ)

/-- The factors omitted by the modulus-`m` Dirichlet characters are exactly
the actual Euler denominators of the cyclotomic field above primes dividing `m`. -/
def cyclotomicFiniteEulerDenominator (m : ℕ) [NeZero m] (w : ℂ) : ℂ :=
  ∏ p ∈ cyclotomicBadPrimes m, cyclotomicPrimeEulerDenominator m p w

private theorem cyclotomicPrimeEulerDenominator_ne_zero (m : ℕ) [NeZero m]
    (p : Nat.Primes) {w : ℂ} (hw : 0 < w.re) :
    cyclotomicPrimeEulerDenominator m p w ≠ 0 := by
  let K := CyclotomicField m ℚ
  let Q : Ideal ℤ := span {(p.val : ℤ)}
  let _ : Fact p.val.Prime := ⟨p.property⟩
  let _ : Q.IsMaximal := Int.ideal_span_isMaximal_of_prime p.val
  have hQ : Q ≠ ⊥ := by simp [Q, p.property.ne_zero]
  have hp : (1 : ℝ) < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
  have hbase : ‖(p.val : ℂ) ^ (-w)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hw)
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro P hP
  have h := (IsDedekindDomain.mem_primesOverFinset_iff hQ (𝓞 K)).mp hP
  let _ : P.IsPrime := h.1
  let _ : P.LiesOver Q := h.2
  have hpos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have hlt : ‖((p.val : ℂ) ^ (-w)) ^ P.inertiaDeg ℤ‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hbase (Nat.ne_of_gt hpos)
  refine sub_ne_zero.mpr fun he ↦ ?_
  rw [← he, norm_one] at hlt
  exact (lt_irrefl _) hlt

theorem cyclotomicFiniteEulerDenominator_ne_zero (m : ℕ) [NeZero m] {w : ℂ} (hw : 0 < w.re) :
    cyclotomicFiniteEulerDenominator m w ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p _ ↦ cyclotomicPrimeEulerDenominator_ne_zero m p hw

private theorem cyclotomicFiniteEulerDenominator_differentiable (m : ℕ) [NeZero m] :
    Differentiable ℂ (cyclotomicFiniteEulerDenominator m) := by
  unfold cyclotomicFiniteEulerDenominator cyclotomicPrimeEulerDenominator
  refine Differentiable.fun_finsetProd fun p _ ↦ Differentiable.fun_finsetProd fun P _ ↦ ?_
  have hp : (p.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hbase : Differentiable ℂ (fun w : ℂ ↦ (p.val : ℂ) ^ (-w)) :=
    differentiable_id.neg.const_cpow (Or.inl hp)
  exact (differentiable_const (1 : ℂ)).sub (hbase.pow _)

private theorem cyclotomic_dedekind_euler_eq_corrected_dirichlet_product (m : ℕ) [NeZero m]
    (w : ℂ) (hw : 1 < w.re) :
    NumberField.dedekindZeta (CyclotomicField m ℚ) w =
      (∏ χ : DirichletCharacter ℂ m, χ.LFunction w) * (cyclotomicFiniteEulerDenominator m w)⁻¹ := by
  classical
  let K := CyclotomicField m ℚ
  let chars (p : Nat.Primes) : ℂ :=
    ∏ χ : DirichletCharacter ℂ m, (1 - χ (p.val : ZMod m) * (p.val : ℂ) ^ (-w))⁻¹
  let badFactor (p : Nat.Primes) : ℂ :=
    if p ∈ cyclotomicBadPrimes m then (cyclotomicPrimeEulerDenominator m p w)⁻¹ else 1
  have hc : HasProd chars (∏ χ : DirichletCharacter ℂ m, χ.LFunction w) := by
    apply hasProd_prod
    intro χ _
    simpa only [χ.LFunction_eq_LSeries hw] using χ.LSeries_eulerProduct_hasProd hw
  have hb : HasProd badFactor (cyclotomicFiniteEulerDenominator m w)⁻¹ := by
    have he : (∏ p ∈ cyclotomicBadPrimes m, badFactor p) =
        (cyclotomicFiniteEulerDenominator m w)⁻¹ := by
      rw [cyclotomicFiniteEulerDenominator, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun p hp ↦ by simp [badFactor, hp]
    rw [← he]
    exact hasProd_prod_of_ne_finset_one (fun p hp ↦ by simp [badFactor, hp])
  have hlocal (p : Nat.Primes) :
      (cyclotomicPrimeEulerDenominator m p w)⁻¹ = chars p * badFactor p := by
    by_cases h : p ∈ cyclotomicBadPrimes m
    · have hnu : ¬ IsUnit (p.val : ZMod m) := by
        rw [ZMod.isUnit_iff_coprime]
        exact fun hp ↦ (p.property.coprime_iff_not_dvd.mp hp) ((mem_cyclotomicBadPrimes m p).mp h)
      have hzero (χ : DirichletCharacter ℂ m) : χ (p.val : ZMod m) = 0 := χ.map_nonunit hnu
      simp [chars, badFactor, h, hzero]
    · have hp : ¬ p.val ∣ m := fun hp ↦ h ((mem_cyclotomicBadPrimes m p).mpr hp)
      let _ : Fact p.val.Prime := ⟨p.property⟩
      rw [show badFactor p = 1 by simp [badFactor, h], mul_one]
      unfold cyclotomicPrimeEulerDenominator chars
      rw [cyclotomic_localEuler_denominator_of_not_dvd m p.val hp, Finset.prod_inv_distrib]
  calc
    _ = ∏' p : Nat.Primes, (cyclotomicPrimeEulerDenominator m p w)⁻¹ := by
      simpa only [K, cyclotomicPrimeEulerDenominator, Finset.prod_inv_distrib] using
        dedekindZeta_eq_eulerProduct_rationalPrimes K w hw
    _ = _ := (tprod_congr hlocal).trans (hc.mul hb).tprod_eq

/-- Clearing the finite Euler factors gives the same-point continuation
identity on the whole plane away from the pole. -/
theorem cyclotomic_continuation_eq_dirichlet_product (m : ℕ) [NeZero m]
    {Z : ℂ → ℂ} (hZ : IsDedekindZeta (CyclotomicField m ℚ) Z) {w : ℂ} (hw : w ≠ 1) :
    cyclotomicFiniteEulerDenominator m w * Z w = ∏ χ : DirichletCharacter ℂ m, χ.LFunction w := by
  let P : ℂ → ℂ := fun s ↦ ∏ χ : DirichletCharacter ℂ m, χ.LFunction s
  have hP : DifferentiableOn ℂ P ({1}ᶜ : Set ℂ) := by
    refine DifferentiableOn.fun_finsetProd fun χ _ s hs ↦ ?_
    exact (χ.differentiableAt_LFunction s (Or.inl (show s ≠ 1 from hs))).differentiableWithinAt
  have hB := (cyclotomicFiniteEulerDenominator_differentiable m).differentiableOn.mul hZ.1
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have htwo : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have hr : (cyclotomicFiniteEulerDenominator m * Z) =ᶠ[nhds (2 : ℂ)] P := by
    have hu : (Complex.re ⁻¹' Ioi (1 : ℝ)) ∈ nhds (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : ℂ).re)
    refine Filter.eventually_of_mem hu fun s hs ↦ ?_
    change cyclotomicFiniteEulerDenominator m s * Z s = P s
    change 1 < s.re at hs
    rw [hZ.2 s hs, cyclotomic_dedekind_euler_eq_corrected_dirichlet_product m s hs]
    change cyclotomicFiniteEulerDenominator m s *
      (P s * (cyclotomicFiniteEulerDenominator m s)⁻¹) = P s
    rw [mul_left_comm, mul_inv_cancel₀ (cyclotomicFiniteEulerDenominator_ne_zero m (by linarith)), mul_one]
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hB.analyticOnNhd isOpen_compl_singleton) (hP.analyticOnNhd isOpen_compl_singleton) hconn htwo hr hw

/-- Cyclotomic Dedekind RH is precisely the strip-zero statement for the
Dirichlet characters of that modulus. -/
theorem cyclotomic_dedekindZetaRH_iff_dirichlet (m : ℕ) [NeZero m] :
    DedekindZetaRH (CyclotomicField m ℚ) ↔
      ∀ χ : DirichletCharacter ℂ m, StripZerosOnLine χ.LFunction := by
  classical
  rw [dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind (CyclotomicField m ℚ))]
  constructor
  · intro h χ w hlo hhi hz
    have hw : w ≠ 1 := by rintro rfl; norm_num at hhi
    have hp : (∏ χ' : DirichletCharacter ℂ m, χ'.LFunction w) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ χ) hz
    have he := cyclotomic_continuation_eq_dirichlet_product m
      (mixedThetaContinuation_isDedekind (CyclotomicField m ℚ)) hw
    rw [hp] at he
    exact h w hlo hhi ((mul_eq_zero.mp he).resolve_left (cyclotomicFiniteEulerDenominator_ne_zero m hlo))
  · intro h w hlo hhi hz
    have hw : w ≠ 1 := by rintro rfl; norm_num at hhi
    have he := cyclotomic_continuation_eq_dirichlet_product m
      (mixedThetaContinuation_isDedekind (CyclotomicField m ℚ)) hw
    rw [hz, mul_zero] at he
    obtain ⟨χ, _, hχ⟩ := Finset.prod_eq_zero_iff.mp he.symm
    exact h χ w hlo hhi hχ

#check @cyclotomic_continuation_eq_dirichlet_product
#check @cyclotomic_dedekindZetaRH_iff_dirichlet
#print axioms cyclotomicFiniteEulerDenominator_ne_zero
#print axioms cyclotomic_continuation_eq_dirichlet_product
#print axioms cyclotomic_dedekindZetaRH_iff_dirichlet

end

end FieldTarget
