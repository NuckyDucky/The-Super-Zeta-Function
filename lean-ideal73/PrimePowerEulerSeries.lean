import PrimePowerExponents
import FieldCoefficientTransfer
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! The ordinary ideal coefficient at every rational prime power is the
corresponding coefficient of the local geometric Euler series. -/

namespace FieldCoefficientTransfer

open ArithmeticFunction NumberField PowerSeries
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def geometricAtDegree (d : ℕ) : PowerSeries ℂ :=
  PowerSeries.subst (PowerSeries.X ^ d : PowerSeries ℂ) (PowerSeries.mk (1 : ℕ → ℂ))

theorem coeff_geometricAtDegree {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    coeff n (geometricAtDegree d) = if d ∣ n then 1 else 0 := by
  rw [geometricAtDegree, coeff_subst_X_pow hd, coeff_mk, Pi.one_apply, map_one]

theorem geometricAtDegree_mul_denominator {d : ℕ} (hd : d ≠ 0) :
    geometricAtDegree d * (1 - PowerSeries.X^d) = 1 := by
  have ha : PowerSeries.HasSubst (PowerSeries.X^d : PowerSeries ℂ) := .X_pow hd
  have h := congrArg (PowerSeries.substAlgHom ha) (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simpa only [map_mul, map_sub, map_one, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom, geometricAtDegree] using h

noncomputable def fieldLocalEulerSeries (p : ℕ) : PowerSeries ℂ :=
  ∏ P : PrimeAbove K p, geometricAtDegree (P.val.inertiaDeg ℤ)

theorem fieldLocalEulerSeries_mul_denominator (p : ℕ) :
    fieldLocalEulerSeries K p *
      (∏ P : PrimeAbove K p, (1 - PowerSeries.X^(P.val.inertiaDeg ℤ))) = 1 := by
  rw [fieldLocalEulerSeries, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun P _ =>
    geometricAtDegree_mul_denominator (primeAbove_inertiaDeg_pos K P).ne'

private noncomputable def allowedExponents (p n : ℕ) : Finset (PrimeAbove K p →₀ ℕ) :=
  (Finset.univ.finsuppAntidiag n).filter fun e =>
    ∀ P : PrimeAbove K p, P.val.inertiaDeg ℤ ∣ e P

private noncomputable def degreeEquivAllowedExponents (p n : ℕ) :
    {f : PrimeAbove K p → ℕ // exponentDegree K f = n} ≃ ↥(allowedExponents K p n) where
  toFun f := by
    let e : PrimeAbove K p →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun P => P.val.inertiaDeg ℤ * f.val P)
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_finsuppAntidiag.mpr ⟨?_, Finset.subset_univ _⟩, ?_⟩⟩
    · exact f.property
    · intro P
      exact dvd_mul_right _ _
  invFun e := by
    have h := Finset.mem_filter.mp e.property
    refine ⟨fun P => e.val P / P.val.inertiaDeg ℤ, ?_⟩
    unfold exponentDegree
    calc
      _ = ∑ P : PrimeAbove K p, e.val P := Finset.sum_congr rfl fun P _ => Nat.mul_div_cancel' (h.2 P)
      _ = n := (Finset.mem_finsuppAntidiag.mp h.1).1
  left_inv f := by
    apply Subtype.ext
    funext P
    change (P.val.inertiaDeg ℤ * f.val P) / P.val.inertiaDeg ℤ = f.val P
    exact Nat.mul_div_cancel_left (f.val P) (primeAbove_inertiaDeg_pos K P)
  right_inv e := by
    apply Subtype.ext
    ext P
    change P.val.inertiaDeg ℤ * (e.val P / P.val.inertiaDeg ℤ) = e.val P
    exact Nat.mul_div_cancel' ((Finset.mem_filter.mp e.property).2 P)

private theorem coeff_fieldLocalEulerSeries_card (p n : ℕ) :
    coeff n (fieldLocalEulerSeries K p) = (↑(allowedExponents K p n).card : ℂ) := by
  unfold fieldLocalEulerSeries
  rw [PowerSeries.coeff_prod]
  simp_rw [coeff_geometricAtDegree (primeAbove_inertiaDeg_pos K _).ne']
  have hprod (e : PrimeAbove K p →₀ ℕ) :
      (∏ P : PrimeAbove K p, if P.val.inertiaDeg ℤ ∣ e P then (1 : ℂ) else 0) =
        if ∀ P : PrimeAbove K p, P.val.inertiaDeg ℤ ∣ e P then 1 else 0 := by
    split_ifs with h
    · simp [h]
    · obtain ⟨P,hP⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ P) (if_neg hP)
  simp_rw [hprod]
  rw [← Finset.sum_filter]
  simp [allowedExponents]

/-- The prime-power coefficients in the field-transfer theorem come from
the actual Euler factors, with one geometric series per prime ideal. -/
theorem idealCounts_primePower_eq_localEuler (p : ℕ) [Fact p.Prime] (n : ℕ) :
    idealCounts K (p^n) = coeff n (fieldLocalEulerSeries K p) := by
  rw [coeff_fieldLocalEulerSeries_card]
  have hcard := Nat.card_congr ((primePowerIdealsEquivExponents K p n).trans
    (degreeEquivAllowedExponents K p n))
  have hfin : Nat.card ↥(allowedExponents K p n) = (allowedExponents K p n).card :=
    Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
  rw [hfin] at hcard
  simp [idealCounts, toArithmeticFunction, (Fact.out : p.Prime).ne_zero, hcard]

#print axioms idealCounts_primePower_eq_localEuler
#print axioms fieldLocalEulerSeries_mul_denominator

end FieldCoefficientTransfer
