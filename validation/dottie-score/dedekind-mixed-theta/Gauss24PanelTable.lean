import RationalPanelQuadrature

namespace FieldTarget

open Finset

def gauss24Denominator : ℤ := 10 ^ 30

/-- Rational approximations to the Gauss–Legendre offsets and weights. The
checked moments below certify this specific rational table directly. -/
def gauss24Table : List (ℤ × ℤ) := [
(995187219997021360179997409701, 12341229799987199546805667070),
  (974728555971309498198391993008, 28531388628933663181307815952),
  (938274552002732758523649001709, 44277438817419806168602748211),
  (886415527004401034213154341982, 59298584915436780746367758500),
  (820001985973902921953949872670, 73346481411080305734033615253),
  (740124191578554364243828103100, 86190161531953275917185202984),
  (648093651936975569252495786911, 97618652104113888269880664464),
  (545421471388839535658375617218, 107444270115965634782577342447),
  (433793507626045138487084231913, 115505668053725601353344483907),
  (315042679696163374386793291320, 121670472927803391204463153476),
  (191118867473616309158639820757, 125837456346828296121375382511),
  (64056892862605626085043082625, 127938195346752156974056165225),
  (-64056892862605626085043082625, 127938195346752156974056165225),
  (-191118867473616309158639820757, 125837456346828296121375382511),
  (-315042679696163374386793291320, 121670472927803391204463153476),
  (-433793507626045138487084231913, 115505668053725601353344483907),
  (-545421471388839535658375617218, 107444270115965634782577342447),
  (-648093651936975569252495786911, 97618652104113888269880664464),
  (-740124191578554364243828103100, 86190161531953275917185202984),
  (-820001985973902921953949872670, 73346481411080305734033615253),
  (-886415527004401034213154341982, 59298584915436780746367758500),
  (-938274552002732758523649001709, 44277438817419806168602748211),
  (-974728555971309498198391993008, 28531388628933663181307815952),
  (-995187219997021360179997409701, 12341229799987199546805667070)
]

def gauss24Pair (i : Fin 24) : ℤ × ℤ := gauss24Table.getD i.val (0, 0)

def gauss24Node (i : Fin 24) : ℚ := (gauss24Pair i).1 / (gauss24Denominator : ℚ)

def gauss24Weight (i : Fin 24) : ℚ := (gauss24Pair i).2 / (gauss24Denominator : ℚ)

private theorem den_pos : 0 < gauss24Denominator := by decide +kernel

private theorem nodes_ok : ∀ i : Fin 24, |(gauss24Pair i).1| ≤ gauss24Denominator := by
  decide +kernel

private theorem weights_nonnegative : ∀ i : Fin 24, 0 ≤ (gauss24Pair i).2 := by
  decide +kernel

private theorem weights_sum : (∑ i : Fin 24, (gauss24Pair i).2) ≤ 3 * gauss24Denominator := by
  decide +kernel

/-- Clear the common denominator before checking each moment. -/
private def gauss24MomentNumerator (k : ℕ) : ℤ :=
  (1 - (-1 : ℤ) ^ (k + 1)) * gauss24Denominator ^ (k + 1) -
  ((k : ℤ) + 1) * ∑ i : Fin 24, (gauss24Pair i).2 * (gauss24Pair i).1 ^ k

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem moments_checked : ∀ k : Fin 48,
    |gauss24MomentNumerator k.val| * 10 ^ 28 ≤
      ((k.val : ℤ) + 1) * gauss24Denominator ^ (k.val + 1) := by
  decide +kernel

theorem gauss24_node_abs_le (i : Fin 24) : |(gauss24Node i : ℝ)| ≤ 1 := by
  have hd : (0 : ℝ) < (gauss24Denominator : ℝ) := by exact_mod_cast den_pos
  unfold gauss24Node
  push_cast
  rw [abs_div, abs_of_pos hd]
  apply (div_le_one hd).mpr
  exact_mod_cast nodes_ok i

theorem gauss24_weight_nonneg (i : Fin 24) : 0 ≤ (gauss24Weight i : ℝ) := by
  unfold gauss24Weight
  push_cast
  exact div_nonneg (by exact_mod_cast weights_nonnegative i) (by exact_mod_cast den_pos.le)

theorem gauss24_weight_abs_sum_le : (∑ i : Fin 24, |(gauss24Weight i : ℝ)|) ≤ 3 := by
  have hd : (0 : ℝ) < (gauss24Denominator : ℝ) := by exact_mod_cast den_pos
  simp_rw [abs_of_nonneg (gauss24_weight_nonneg _)]
  unfold gauss24Weight
  push_cast
  rw [← Finset.sum_div]
  exact (div_le_iff₀ hd).mpr (by exact_mod_cast weights_sum)

theorem gauss24_moment_error {k : ℕ} (hk : k < 48) :
    |(panelMoment k : ℝ) - ∑ i : Fin 24, (gauss24Weight i : ℝ) * (gauss24Node i : ℝ) ^ k| ≤
      1 / 10 ^ 28 := by
  have hd : (0 : ℝ) < (gauss24Denominator : ℝ) := by exact_mod_cast den_pos
  have hk' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hx : |(gauss24MomentNumerator k : ℝ)| * 10 ^ 28 ≤
      ((k : ℝ) + 1) * (gauss24Denominator : ℝ) ^ (k + 1) := by
    exact_mod_cast moments_checked ⟨k, hk⟩
  have hpositive : 0 < ((k : ℝ) + 1) * (gauss24Denominator : ℝ) ^ (k + 1) := by positivity
  have hre :
      (panelMoment k : ℝ) - ∑ i : Fin 24, (gauss24Weight i : ℝ) * (gauss24Node i : ℝ) ^ k =
        (gauss24MomentNumerator k : ℝ) / (((k : ℝ) + 1) * (gauss24Denominator : ℝ) ^ (k + 1)) := by
    unfold panelMoment gauss24MomentNumerator gauss24Weight gauss24Node
    push_cast
    simp_rw [div_pow, div_mul_div_comm, ← pow_succ']
    rw [← Finset.sum_div]
    field_simp [hd.ne', hk'.ne', pow_succ]
  rw [hre, abs_div, abs_of_pos hpositive]
  apply (div_le_div_iff₀ hpositive (by positivity : (0 : ℝ) < 10 ^ 28)).mpr
  simpa only [one_mul] using hx

#print axioms gauss24_node_abs_le
#print axioms gauss24_weight_abs_sum_le
#print axioms gauss24_moment_error

end FieldTarget
