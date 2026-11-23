import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Coprime.Lemmas

namespace IdealNormCoprime

noncomputable section

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]

abbrev fiber (R : Type*) [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] (n : ℕ) :=
  {I : Ideal R // I.absNorm = n}

private abbrev principal (R : Type*) [CommRing R] (m : ℕ) : Ideal R :=
  Ideal.span {(m : R)}

omit [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] in
private theorem spans_coprime {m n : ℕ} (h : m.Coprime n) :
    principal R m ⊔ principal R n = ⊤ :=
  Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_span_singleton_iff _ _).mpr h.cast)

omit [Module.Finite ℤ R] in
private theorem split_mul {m n : ℕ} (h : m.Coprime n) (I : fiber R (m*n)) :
    (I.val ⊔ principal R m) * (I.val ⊔ principal R n) = I.val := by
  have hab : principal R m * principal R n ≤ I.val := by
    simpa only [principal, Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, ← I.property]
      using I.val.span_singleton_absNorm_le
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right hab)
  · calc
      I.val = I.val * (principal R m ⊔ principal R n) := by rw [spans_coprime h, Ideal.mul_top]
      _ = I.val * principal R m ⊔ I.val * principal R n := Ideal.mul_sup _ _ _
      _ ≤ (I.val ⊔ principal R m) * (I.val ⊔ principal R n) := by
        apply sup_le
        · rw [mul_comm]
          exact Ideal.mul_mono le_sup_right le_sup_left
        · exact Ideal.mul_mono le_sup_left le_sup_right

private theorem split_norm {m n : ℕ} (h : m.Coprime n) (I : fiber R (m*n)) :
    (I.val ⊔ principal R m).absNorm = m ∧ (I.val ⊔ principal R n).absNorm = n := by
  let u := (I.val ⊔ principal R m).absNorm
  let v := (I.val ⊔ principal R n).absNorm
  have huv : u * v = m * n := by
    change Ideal.absNorm _ * Ideal.absNorm _ = _
    rw [← map_mul, split_mul h I, I.property]
  have du : u ∣ m ^ Module.finrank ℤ R := by
    rw [← Ideal.absNorm_span_natCast (S := R)]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have dv : v ∣ n ^ Module.finrank ℤ R := by
    rw [← Ideal.absNorm_span_natCast (S := R)]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hun : u.Coprime n := (h.pow_left _).coprime_dvd_left du
  have hvm : v.Coprime m := (h.symm.pow_left _).coprime_dvd_left dv
  refine ⟨Nat.dvd_antisymm (hun.dvd_of_dvd_mul_right ?_) (hvm.symm.dvd_of_dvd_mul_right ?_),
    Nat.dvd_antisymm (hvm.dvd_of_dvd_mul_left ?_) (hun.symm.dvd_of_dvd_mul_left ?_)⟩
  · rw [← huv]; exact dvd_mul_right _ _
  · rw [huv]; exact dvd_mul_right _ _
  · rw [← huv]; exact dvd_mul_left _ _
  · rw [huv]; exact dvd_mul_left _ _

omit [Module.Finite ℤ R] in
private theorem recover {m n : ℕ} (h : m.Coprime n) (A : fiber R m) (B : fiber R n) :
    A.val * B.val ⊔ principal R m = A.val := by
  have ha : principal R m ≤ A.val := by
    simpa only [A.property] using A.val.span_singleton_absNorm_le
  have hb : principal R n ≤ B.val := by
    simpa only [B.property] using B.val.span_singleton_absNorm_le
  have ht : B.val ⊔ principal R m = ⊤ := top_unique <|
    (spans_coprime (R := R) h.symm).symm.le.trans (sup_le_sup_right hb _)
  rw [Ideal.mul_sup_eq_of_coprime_right ht, sup_eq_left.mpr ha]

def splitEquiv {m n : ℕ} (h : m.Coprime n) : fiber R m × fiber R n ≃ fiber R (m*n) where
  toFun u := ⟨u.1.val * u.2.val, by rw [map_mul, u.1.property, u.2.property]⟩
  invFun I := (⟨_, (split_norm h I).1⟩, ⟨_, (split_norm h I).2⟩)
  left_inv := by
    rintro ⟨A,B⟩
    apply Prod.ext <;> apply Subtype.ext
    · exact recover h A B
    · simpa only [mul_comm] using recover h.symm B A
  right_inv I := Subtype.ext (split_mul h I)

#print axioms splitEquiv

end
end IdealNormCoprime
