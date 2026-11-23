import IdealPrimePowerExponents

/-! Specialize the prime-power exponent equivalence to a ring of integers. -/

namespace FieldCoefficientTransfer

open NumberField

variable (K : Type*) [Field K] [NumberField K]

noncomputable abbrev primesAbove (p : ℕ) : Finset (Ideal (𝓞 K)) :=
  IdealPrimePower.primesAbove (𝓞 K) p

abbrev PrimeAbove (p : ℕ) := ↥(primesAbove K p)

theorem primeAbove_inertiaDeg_pos {p : ℕ} (P : PrimeAbove K p) : 0 < P.val.inertiaDeg ℤ :=
  IdealPrimePower.primeAbove_inertiaDeg_pos (𝓞 K) P

noncomputable abbrev exponentDegree {p : ℕ} (f : PrimeAbove K p → ℕ) : ℕ :=
  IdealPrimePower.exponentDegree (𝓞 K) f

noncomputable abbrev primePowerIdealsEquivExponents (p : ℕ) [Fact p.Prime] (n : ℕ) :
    {I : Ideal (𝓞 K) // I.absNorm = p^n} ≃
      {f : PrimeAbove K p → ℕ // exponentDegree K f = n} :=
  IdealPrimePower.primePowerIdealsEquivExponents (𝓞 K) p n

#print axioms primePowerIdealsEquivExponents

end FieldCoefficientTransfer
