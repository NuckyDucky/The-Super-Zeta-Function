import GaussianCommonDivisorLift

/-! Multiplying the index of a quadratic coefficient multiplies it by
the real coordinate of a geometric sum. Modulo a square of a prime,
this factor is the index multiplier times a power of the real coordinate. -/

namespace AlpogeSuperZeta

open QuarticModel QuadraticAlgebra Finset

local notation "R₀" => QuadraticAlgebra GaussianInt gaussianDiscriminant (0 : GaussianInt)

private def quadraticPowerFactor (z : R₀) (n : ℕ) : GaussianInt :=
  (∑ i ∈ range n, z ^ i * (star z) ^ (n - 1 - i)).re

private theorem quadratic_im_pow_eq_mul_factor (z : R₀) (n : ℕ) :
    (z ^ n).im = z.im * quadraticPowerFactor z n := by
  have h :
      (∑ i ∈ range n, z ^ i * (star z) ^ (n - 1 - i)) * (z - star z) =
        z ^ n - star (z ^ n) := by
    rw [star_pow]
    exact geom_sum₂_mul z (star z) n
  have hi := congrArg QuadraticAlgebra.im h
  simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_sub,
    QuadraticAlgebra.im_star, QuadraticAlgebra.re_star, zero_mul, add_zero, sub_self, mul_zero] at hi
  unfold quadraticPowerFactor
  apply mul_left_cancel₀ (by decide : (2 : GaussianInt) ≠ 0)
  linear_combination -hi

private theorem pow_re_of_im_sq_zero {A : Type*} [CommRing A] {d : A}
    (z : QuadraticAlgebra A d 0) (hz : z.im ^ 2 = 0) (n : ℕ) :
    (z ^ n).re = z.re ^ n ∧ z.im ∣ (z ^ n).im := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨b, hb⟩ := ih.2
    have hzero : (z ^ n).im * z.im = 0 := by
      calc
        _ = z.im ^ 2 * b := by rw [hb]; ring
        _ = 0 := by rw [hz, zero_mul]
    constructor
    · rw [pow_succ z, QuadraticAlgebra.re_mul, ih.1, mul_assoc d, hzero, mul_zero, add_zero,
        pow_succ]
    · refine ⟨(z ^ n).re + b * z.re, ?_⟩
      rw [pow_succ, QuadraticAlgebra.im_mul, hb]
      ring

private theorem quadratic_factor_mod_prime_sq (I : Ideal GaussianInt) (z : R₀)
    (hz : z.im ∈ I) (n : ℕ) :
    quadraticPowerFactor z n - (n : GaussianInt) * z.re ^ (n - 1) ∈ I ^ 2 := by
  let E := GaussianInt ⧸ (I ^ 2)
  let f := Ideal.Quotient.mk (I ^ 2)
  let g := mapGaussianQuadratic f
  let v := g z
  have hv : v.im ^ 2 = 0 := by
    change f z.im ^ 2 = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_two, pow_two]
    exact Ideal.mul_mem_mul hz hz
  have hvs : (star v).im ^ 2 = 0 := by rw [QuadraticAlgebra.im_star, neg_sq, hv]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_mul, map_natCast, map_pow, sub_eq_zero]
  change (g (∑ i ∈ range n, z ^ i * (star z) ^ (n - 1 - i))).re =
    (n : E) * v.re ^ (n - 1)
  rw [map_sum]
  change QuadraticAlgebra.reₗ _ _ (∑ i ∈ range n, g (z ^ i * (star z) ^ (n - 1 - i))) = _
  rw [map_sum]
  simp only [QuadraticAlgebra.reₗ_apply, map_mul, map_pow]
  have hs : g (star z) = star v := mapGaussianQuadratic_star f z
  rw [hs]
  have hterm (i : ℕ) (hi : i ∈ range n) :
      (v ^ i * (star v) ^ (n - 1 - i)).re = v.re ^ (n - 1) := by
    have ha := pow_re_of_im_sq_zero v hv i
    have hb := pow_re_of_im_sq_zero (star v) hvs (n - 1 - i)
    obtain ⟨a, ha'⟩ := ha.2
    obtain ⟨b, hb'⟩ := hb.2
    have hzero : (v ^ i).im * ((star v) ^ (n - 1 - i)).im = 0 := by
      calc
        _ = v.im ^ 2 * (-a * b) := by rw [ha', hb', QuadraticAlgebra.im_star]; ring
        _ = 0 := by rw [hv, zero_mul]
    rw [QuadraticAlgebra.re_mul, ha.1, hb.1, QuadraticAlgebra.re_star, zero_mul, add_zero,
      mul_assoc, hzero, mul_zero, add_zero, ← pow_add,
      Nat.add_sub_cancel' (by have := Finset.mem_range.mp hi; omega)]
  rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]

private theorem gaussianPowerCoefficient_mul_index (h : GaussianInt) (m n : ℕ) :
    gaussianPowerCoefficient h (m * n) =
      gaussianPowerCoefficient h m *
        quadraticPowerFactor ((⟨h, 1⟩ : R₀) ^ m) n := by
  unfold gaussianPowerCoefficient
  rw [pow_mul, quadratic_im_pow_eq_mul_factor]

private theorem mul_mem_prime_pow_exact {I : Ideal GaussianInt} [I.IsPrime] (hI : I ≠ ⊥)
    {a b : GaussianInt} {j k : ℕ}
    (ha : a ∈ I ^ j) (ha' : a ∉ I ^ (j + 1))
    (hb : b ∈ I ^ k) (hb' : b ∉ I ^ (k + 1)) :
    a * b ∈ I ^ (j + k) ∧ a * b ∉ I ^ (j + k + 1) := by
  obtain ⟨π, rfl⟩ : Submodule.IsPrincipal I := inferInstance
  have hp : π ≠ 0 := fun h => hI (Ideal.span_singleton_eq_bot.mpr h)
  have hprime : Prime π := (Ideal.span_singleton_prime hp).mp inferInstance
  simp only [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha ha' hb hb' ⊢
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  have hc' : ¬π ∣ c := fun h => ha' (by rw [hc, pow_succ]; exact mul_dvd_mul_left _ h)
  have hd' : ¬π ∣ d := fun h => hb' (by rw [hd, pow_succ]; exact mul_dvd_mul_left _ h)
  rw [show a * b = π ^ (j + k) * (c * d) by rw [hc, hd, pow_add]; ring]
  refine ⟨dvd_mul_right _ _, ?_⟩
  rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hp)]
  exact fun h => (hprime.dvd_or_dvd h).elim hc' hd'

private theorem quadraticPowerFactor_mem_of_cast_mem (I : Ideal GaussianInt) (z : R₀)
    (hz : z.im ∈ I) {n : ℕ} (hn : (n : GaussianInt) ∈ I) :
    quadraticPowerFactor z n ∈ I := by
  have hd := Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0) (quadratic_factor_mod_prime_sq I z hz n)
  have hmain := I.mul_mem_right (z.re ^ (n - 1)) hn
  simpa only [sub_add_cancel] using I.add_mem hd hmain

private theorem quadraticPowerFactor_exact_one {I : Ideal GaussianInt} [I.IsPrime]
    (hI : I ≠ ⊥) (z : R₀) (hz : z.im ∈ I) (hreal : z.re ∉ I)
    {n : ℕ} (hn : (n : GaussianInt) ∈ I) (hn' : (n : GaussianInt) ∉ I ^ 2) :
    quadraticPowerFactor z n ∈ I ∧ quadraticPowerFactor z n ∉ I ^ 2 := by
  refine ⟨quadraticPowerFactor_mem_of_cast_mem I z hz hn, ?_⟩
  have hpow : z.re ^ (n - 1) ∉ I := fun h => hreal ((inferInstance : I.IsPrime).mem_of_pow_mem _ h)
  have hmain : (n : GaussianInt) * z.re ^ (n - 1) ∉ I ^ 2 := by
    simpa using (mul_mem_prime_pow_exact hI (j := 1) (k := 0)
      (by simpa using hn) (by simpa using hn') (by simp)
      (by simpa using hpow)).2
  intro h
  apply hmain
  simpa only [sub_sub_cancel] using (I ^ 2).sub_mem h (quadratic_factor_mod_prime_sq I z hz n)

theorem gaussianPowerCoefficient_mul_prime_pow_lower (I : Ideal GaussianInt)
    {p m : ℕ} {h : GaussianInt}
    (hp : (p : GaussianInt) ∈ I) (hm : gaussianPowerCoefficient h m ∈ I) (j : ℕ) :
    gaussianPowerCoefficient h (m * p ^ j) ∈ I ^ (j + 1) := by
  induction j with
  | zero => simpa using hm
  | succ j ih =>
    have him : gaussianPowerCoefficient h (m * p ^ j) ∈ I :=
      Ideal.pow_le_self (by omega) ih
    have hfactor := quadraticPowerFactor_mem_of_cast_mem I
      ((⟨h, 1⟩ : R₀) ^ (m * p ^ j)) him hp
    rw [pow_succ p, ← Nat.mul_assoc, gaussianPowerCoefficient_mul_index, pow_succ I (j + 1)]
    exact Ideal.mul_mem_mul ih hfactor

private theorem gaussianPowerCoefficient_mul_prime_pow_exact {I : Ideal GaussianInt}
    [I.IsPrime] (hI : I ≠ ⊥) {p m : ℕ} {h : GaussianInt}
    (hp : (p : GaussianInt) ∈ I) (hp' : (p : GaussianInt) ∉ I ^ 2)
    (hm : gaussianPowerCoefficient h m ∈ I) (hm' : gaussianPowerCoefficient h m ∉ I ^ 2)
    (hreal : ∀ n, gaussianPowerCoefficient h n ∈ I → ((⟨h, 1⟩ : R₀) ^ n).re ∉ I)
    (j : ℕ) :
    gaussianPowerCoefficient h (m * p ^ j) ∈ I ^ (j + 1) ∧
      gaussianPowerCoefficient h (m * p ^ j) ∉ I ^ (j + 2) := by
  induction j with
  | zero => simpa using And.intro hm hm'
  | succ j ih =>
    have him : gaussianPowerCoefficient h (m * p ^ j) ∈ I :=
      Ideal.pow_le_self (by omega) ih.1
    have hfactor := quadraticPowerFactor_exact_one hI ((⟨h, 1⟩ : R₀) ^ (m * p ^ j))
      him (hreal _ him) hp hp'
    rw [pow_succ p, ← Nat.mul_assoc, gaussianPowerCoefficient_mul_index]
    exact mul_mem_prime_pow_exact hI ih.1 ih.2 (by simpa using hfactor.1) hfactor.2

private theorem gaussian_natCast_prime_not_mem_sq {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (I : ↥(gaussianPrimesAbove p)) : (p : GaussianInt) ∉ I.val ^ 2 := by
  have hbranch (r : ZMod p) (hr : r ^ 2 = -1) :
      (p : GaussianInt) ∉ (gaussianPrimeAt r hr) ^ 2 := by
    let J := gaussianPrimeAt r hr
    have hn : (-r) ^ 2 = -1 := by simpa only [neg_sq] using hr
    let J' := gaussianPrimeAt (-r) hn
    have hsplit := split_gaussian_primes hp r hr hn
    have hJ : J ∈ gaussianPrimesAbove p := by simp [J, hsplit]
    have hJ' : J' ∈ gaussianPrimesAbove p := by simp [J', hsplit]
    intro he
    have hm : J * J' ≤ J ^ 2 := by
      change gaussianPrimeAt r hr * gaussianPrimeAt (-r) hn ≤ _
      rw [gaussianPrimeAt_product hp r hr]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr he
    rw [pow_two] at hm
    have hJ0 : J ≠ 0 := gaussianPrimesAbove_ne_bot hJ
    have hle : J' ≤ J := Ideal.dvd_iff_le.mp ((mul_dvd_mul_iff_left hJ0).mp
      (Ideal.dvd_iff_le.mpr hm))
    exact gaussianPrimeAt_distinct hp r hr
      ((gaussianPrimesAbove_isMaximal hJ').eq_of_le (gaussianPrimesAbove_isMaximal hJ).ne_top hle).symm
  have hodd := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
  by_cases hs : p % 4 = 1
  · obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
    have hr' : r ^ 2 = -1 := by rw [pow_two, ← hr]
    have hn : (-r) ^ 2 = -1 := by simpa only [neg_sq] using hr'
    have hcases (J : Ideal GaussianInt) (hJ : J ∈ gaussianPrimesAbove p) :
        J = gaussianPrimeAt r hr' ∨ J = gaussianPrimeAt (-r) hn := by
      simpa only [split_gaussian_primes hp r hr' hn, Finset.mem_insert, Finset.mem_singleton] using hJ
    have hi := hcases I.val I.property
    rcases hi with hi | hi
    · rw [hi]; exact hbranch r hr'
    · rw [hi]; exact hbranch (-r) hn
  · have h3 : p % 4 = 3 := by omega
    have hprime := GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p h3
    rw [eq_inert_gaussian_prime h3 I.property, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have hh : (p : GaussianInt) * p ∣ (p : GaussianInt) * 1 := by
      simpa only [pow_two, mul_one] using h
    exact hprime.not_isUnit (isUnit_iff_dvd_one.mpr ((mul_dvd_mul_iff_left hprime.ne_zero).mp hh))

attribute [local instance] Ideal.Quotient.field

/-- At the negative sign, write the index as m times p to the power j
with m prime to p. If the norm plus one divides m, then the common
divisor belongs to the (j+1)-st power of the prime and no higher power. -/
theorem gaussianCommonDivisor_exact_prime_power {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hD : p.Coprime 26509772707289)
    (I : ↥(gaussianPrimesAbove p)) (hneg : archivedIdealCharacter I.val = -1)
    {m : ℕ} (hm : 0 < m) (hnorm : I.val.absNorm + 1 ∣ m) (hmp : ¬p ∣ m) (j : ℕ) :
    gaussianCommonDivisorIdeal (m * p ^ j) ≤ I.val ^ (j + 1) ∧
      ¬gaussianCommonDivisorIdeal (m * p ^ j) ≤ I.val ^ (j + 2) := by
  classical
  have hI := gaussianPrimesAbove_ne_bot I.property
  have : I.val.IsMaximal := gaussianPrimesAbove_isMaximal I.property
  let E := GaussianInt ⧸ I.val
  have : Finite E := gaussian_finiteQuotient _ hI
  let : Fintype E := Fintype.ofFinite E
  let f := Ideal.Quotient.mk I.val
  have ht : (2 : E) ≠ 0 := by
    intro he
    apply gaussian_two_not_mem_odd_prime hp I
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using he)
  have hc : ringChar E ≠ 2 := fun he =>
    ht (by have h := ringChar.spec E 2; rw [he] at h; exact h.mpr dvd_rfl)
  have hcard : Fintype.card E = I.val.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have he : Even m := by
    apply even_iff_two_dvd.mpr
    apply dvd_trans _ hnorm
    have ho := FiniteField.odd_card_of_char_ne_two (F := E) hc
    rw [← hcard]
    omega
  have hdiv : gaussianCommonDivisorIdeal m ≤ I.val :=
    (gaussianCommonDivisor_le_prime_iff hp hD I hm).mpr ⟨hneg, hnorm⟩
  have hbase (h : GaussianInt) : gaussianPowerCoefficient h m ∈ I.val :=
    hdiv (Ideal.subset_span (Set.mem_range_self h))
  have hp' : (p : GaussianInt) ∈ I.val := (gaussian_natCast_mem_prime_iff I p).mpr dvd_rfl
  have hlower : gaussianCommonDivisorIdeal (m * p ^ j) ≤ I.val ^ (j + 1) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact gaussianPowerCoefficient_mul_prime_pow_lower I.val hp' (hbase x) j
  refine ⟨hlower, ?_⟩
  have hstrict : ¬gaussianCommonDivisorIdeal m ≤ I.val ^ 2 :=
    gaussianCommonDivisor_not_le_prime_sq_of_even hI hm he
      (fun h => hmp ((gaussian_natCast_mem_prime_iff I m).mp h))
      (gaussian_discriminant_not_mem_good_prime hD I)
  obtain ⟨x, hx⟩ : ∃ x, gaussianPowerCoefficient x m ∉ I.val ^ 2 := by
    by_contra! h
    exact hstrict (Ideal.span_le.mpr (Set.range_subset_iff.mpr h))
  have hreal (n : ℕ) (hi : gaussianPowerCoefficient x n ∈ I.val) :
      ((⟨x, 1⟩ : R₀) ^ n).re ∉ I.val := by
    have hχ : quadraticChar E (f gaussianDiscriminant) = -1 := by
      have heq : quarticDiscriminantSign p I = quadraticChar E (f gaussianDiscriminant) := by
        simp only [quarticDiscriminantSign, if_neg ht]
        rfl
      exact heq.symm.trans ((quarticDiscriminantSign_eq_archivedIdealCharacter p I).trans hneg)
    have hns := quadraticChar_neg_one_iff_not_isSquare.mp hχ
    have : Fact (∀ v : E, v ^ 2 ≠ f gaussianDiscriminant + 0 * v) :=
      ⟨fun v h => hns ⟨v, by simpa [pow_two] using h.symm⟩⟩
    let g := mapGaussianQuadratic f
    intro hre
    have hzero : g ((⟨x, 1⟩ : R₀) ^ n) = 0 := QuadraticAlgebra.ext
      (Ideal.Quotient.eq_zero_iff_mem.mpr hre) (Ideal.Quotient.eq_zero_iff_mem.mpr hi)
    rw [map_pow] at hzero
    have hne : g (⟨x, 1⟩ : R₀) ≠ 0 := by
      intro h
      have heq := congrArg QuadraticAlgebra.im h
      change f 1 = 0 at heq
      exact one_ne_zero ((map_one f).symm.trans heq)
    exact (pow_ne_zero n hne) hzero
  have hlast := (gaussianPowerCoefficient_mul_prime_pow_exact hI hp'
    (gaussian_natCast_prime_not_mem_sq hp I) (hbase x) hx hreal j).2
  intro h
  exact hlast (h (Ideal.subset_span (Set.mem_range_self x)))

private theorem rational_prime_dvd_gaussian_absNorm {p : ℕ} [Fact p.Prime]
    (I : ↥(gaussianPrimesAbove p)) : p ∣ I.val.absNorm := by
  have : I.val.IsMaximal := gaussianPrimesAbove_isMaximal I.property
  let E := GaussianInt ⧸ I.val
  have : Finite E := gaussian_finiteQuotient _ (gaussianPrimesAbove_ne_bot I.property)
  let : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = I.val.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  apply (gaussian_natCast_mem_prime_iff I _).mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_natCast, ← hcard]
  exact Nat.cast_card_eq_zero E

/-- Exact containment in every positive power of every good Gaussian
prime. This is the valuation formula of the common divisor. -/
theorem gaussianCommonDivisor_le_prime_pow_iff {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hD : p.Coprime 26509772707289)
    (I : ↥(gaussianPrimesAbove p)) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    gaussianCommonDivisorIdeal n ≤ I.val ^ k ↔
      archivedIdealCharacter I.val = -1 ∧ (I.val.absNorm + 1) * p ^ (k - 1) ∣ n := by
  constructor
  · intro h
    obtain ⟨hneg, hdiv⟩ := (gaussianCommonDivisor_le_prime_iff hp hD I hn).mp
      (h.trans (Ideal.pow_le_self hk.ne'))
    let a := n.factorization p
    let m := n / p ^ a
    have hshape : p ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hm : 0 < m := Nat.ordCompl_pos p hn.ne'
    have hmp : ¬ p ∣ m := Nat.not_dvd_ordCompl Fact.out hn.ne'
    have hcop : Nat.Coprime (I.val.absNorm + 1) p := by
      apply Nat.Coprime.symm
      apply (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
      intro h'
      have h1 := Nat.dvd_sub h' (rational_prime_dvd_gaussian_absNorm I)
      have hp1 : p ∣ 1 := by simpa using h1
      exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hp1)
    have hdivm : I.val.absNorm + 1 ∣ m := (hcop.pow_right a).dvd_of_dvd_mul_left
      (hshape.symm ▸ hdiv)
    have hstrict := (gaussianCommonDivisor_exact_prime_power hp hD I hneg hm hdivm hmp a).2
    have hlen : k - 1 ≤ a := by
      by_contra! he
      apply hstrict
      have hc : gaussianCommonDivisorIdeal n ≤ I.val ^ (a + 2) :=
        h.trans (Ideal.pow_le_pow_right (by omega : a + 2 ≤ k))
      rwa [Nat.mul_comm m, hshape]
    refine ⟨hneg, ?_⟩
    rw [← hshape, Nat.mul_comm (p ^ a)]
    exact Nat.mul_dvd_mul hdivm (pow_dvd_pow p hlen)
  · rintro ⟨hneg, b, hb⟩
    let m := (I.val.absNorm + 1) * b
    have he : n = m * p ^ (k - 1) := by rw [hb]; dsimp [m]; ac_rfl
    have hm : 0 < m := by
      by_contra! h
      rw [he, Nat.le_zero.mp h, zero_mul] at hn
      exact (lt_irrefl 0) hn
    have hbase := (gaussianCommonDivisor_le_prime_iff hp hD I hm).mpr
      ⟨hneg, dvd_mul_right _ _⟩
    have hpmem := (gaussian_natCast_mem_prime_iff I p).mpr dvd_rfl
    rw [he]
    apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change gaussianPowerCoefficient x (m * p ^ (k - 1)) ∈ I.val ^ k
    have hcoef := gaussianPowerCoefficient_mul_prime_pow_lower I.val hpmem
      (hbase (Ideal.subset_span (Set.mem_range_self x))) (k - 1)
    simpa only [Nat.sub_add_cancel hk] using hcoef

#print axioms quadratic_factor_mod_prime_sq
#print axioms gaussianPowerCoefficient_mul_index
#print axioms gaussianPowerCoefficient_mul_prime_pow_lower
#print axioms gaussianCommonDivisor_exact_prime_power
#print axioms gaussianCommonDivisor_le_prime_pow_iff

end AlpogeSuperZeta
