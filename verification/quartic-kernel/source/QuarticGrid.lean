import QuarticGridData
import QuarticSlope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
namespace QuarticGrid

set_option maxRecDepth 12000

def lowerK (j : ℕ) : ℚ := (data[j]?.getD (0,0)).1 / 1000000
def upperK (j : ℕ) : ℚ := (data[j]?.getD (0,0)).2 / 1000000
def node (j : ℕ) : ℚ := j / 64

def sincLower (j : ℕ) : ℚ :=
  let y := (27/100 : ℚ) * node (j+1)
  if y ≤ 4 then 1 - y^2/6 + y^4/120 - y^6/5040 + y^8/362880 - y^10/39916800
  else -1/4

def lowerMass (j : ℕ) : ℚ := 2 * lowerK j * (node j)^2
def upperMass (j : ℕ) : ℚ := 2 * upperK j * (node (j+1))^2

def lowerLine (j : ℕ) : ℚ :=
  (if 0 ≤ sincLower j then lowerMass j else upperMass j) * sincLower j

def sincDen : ℤ := 39916800 * 6400^10

def sincInt (j : ℕ) : ℤ :=
  let a : ℤ := 27 * ((j : ℤ)+1)
  if a ≤ 25600 then
    sincDen - 6652800*a^2*6400^8 + 332640*a^4*6400^6 - 7920*a^6*6400^4
      + 110*a^8*6400^2 - a^10
  else -9979200 * 6400^10

private def rowUpper (j : ℕ) (cell : ℕ × ℕ) : ℤ := 2 * cell.2 * ((j:ℤ)+1)^2
private def rowLower (j : ℕ) (cell : ℕ × ℕ) : ℤ := 2 * cell.1 * (j:ℤ)^2
private def rowLine (j : ℕ) (cell : ℕ × ℕ) : ℤ :=
  (if 0 ≤ sincInt j then rowLower j cell else rowUpper j cell) * sincInt j

def rawUpper (j : ℕ) : ℤ := rowUpper j (data[j]?.getD (0,0))
def rawLower (j : ℕ) : ℤ := rowLower j (data[j]?.getD (0,0))
def rawLine (j : ℕ) : ℤ := rowLine j (data[j]?.getD (0,0))

private theorem sinc_rat (j : ℕ) : sincLower j = (sincInt j : ℚ) / (sincDen : ℚ) := by
  have h : (27/100 : ℚ) * node (j+1) ≤ 4 ↔ (27 : ℤ)*((j:ℤ)+1) ≤ 25600 := by
    have hh : ((27 : ℤ)*((j:ℤ)+1) : ℚ) ≤ (25600:ℚ) ↔
        (27 : ℤ)*((j:ℤ)+1) ≤ 25600 := by norm_cast
    rw [← hh]
    simp only [node, Nat.cast_add, Nat.cast_one, Int.cast_mul, Int.cast_add,
      Int.cast_natCast, Int.cast_one, Int.cast_ofNat]
    constructor <;> intro h₁ <;> linarith
  by_cases hj : (27 : ℤ)*((j:ℤ)+1) ≤ 25600
  · rw [sincLower, if_pos (h.mpr hj), sincInt, if_pos hj]
    simp only [node, sincDen, Nat.cast_add, Nat.cast_one, Int.cast_mul, Int.cast_add,
      Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one, Int.cast_ofNat]
    ring
  · rw [sincLower, if_neg (mt h.mp hj), sincInt, if_neg hj]
    norm_num [sincDen]

private theorem upper_rat (j : ℕ) : upperMass j = (rawUpper j : ℚ)/(1000000*64^2) := by
  simp only [upperMass, upperK, node, rawUpper, rowUpper, Nat.cast_add, Nat.cast_one,
    Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_ofNat]
  ring

private theorem lower_rat (j : ℕ) : lowerMass j = (rawLower j : ℚ)/(1000000*64^2) := by
  simp only [lowerMass, lowerK, node, rawLower, rowLower, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast, Int.cast_ofNat]
  ring

private theorem line_rat (j : ℕ) : lowerLine j / 64 =
    (rawLine j : ℚ)/(1000000*64^3*(sincDen : ℚ)) := by
  have hh : 0 < (sincDen : ℚ) := by norm_num [sincDen]
  have hs : 0 ≤ sincLower j ↔ 0 ≤ sincInt j := by
    rw [sinc_rat, le_div_iff₀ hh, zero_mul]
    norm_cast
  by_cases hj : 0 ≤ sincInt j
  · rw [lowerLine, if_pos (hs.mpr hj), lower_rat, sinc_rat]
    simp only [rawLine, rowLine, if_pos hj, rawLower]
    rw [div_mul_div_comm, div_div, Int.cast_mul]
    congr 1
    ring
  · rw [lowerLine, if_neg (mt hs.mp hj), upper_rat, sinc_rat]
    simp only [rawLine, rowLine, if_neg hj, rawUpper]
    rw [div_mul_div_comm, div_div, Int.cast_mul]
    congr 1
    ring

private def sumRows (f : ℕ → ℕ × ℕ → ℤ) : ℕ → List (ℕ × ℕ) → ℤ
  | _, [] => 0
  | i, row :: rows => f i row + sumRows f (i+1) rows

private theorem sumRows_eq (f : ℕ → ℕ × ℕ → ℤ) (i : ℕ) (rows : List (ℕ × ℕ)) :
    sumRows f i rows = ∑ j ∈ Finset.range rows.length, f (i+j) (rows[j]?.getD (0,0)) := by
  induction rows generalizing i with
  | nil => simp [sumRows]
  | cons row rows ih =>
    simp only [sumRows, List.length_cons, Finset.sum_range_succ', List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Nat.add_zero]
    rw [ih, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show i+1+j=i+(j+1) by omega]

private theorem sumRows_append (f : ℕ → ℕ × ℕ → ℤ) (i : ℕ)
    (a b : List (ℕ × ℕ)) :
    sumRows f i (a ++ b) = sumRows f i a + sumRows f (i+a.length) b := by
  induction a generalizing i with
  | nil => simp [sumRows]
  | cons row rows ih =>
    simp only [List.cons_append, sumRows, ih, List.length_cons, add_assoc]
    rw [Nat.add_comm 1 rows.length]

private theorem dataRows_length : dataRows.length = 1152 := by
  simp only [dataRows, List.length_append]
  change 48+48+48+48+48+48+48+48+48+48+48+48+48+48+48+48+48+48+48+48+48+48+48+48=1152
  rfl

private theorem sumRows_data (f : ℕ → ℕ × ℕ → ℤ) :
    sumRows f 0 data.toList = ∑ j ∈ Finset.range 1152, f j (data[j]?.getD (0,0)) := by
  rw [sumRows_eq, show data.toList.length = 1152 from dataRows_length]
  simp only [Nat.zero_add, Array.getElem?_toList]

private theorem length_block00 : block00.length = 48 := rfl
private theorem upper_block00 : sumRows rowUpper 0 block00 =
    174227786768168 := by decide
private theorem line_block00 : sumRows rowLine 0 block00 =
    706061281272435990726801322767888092964437840873693399420832 := by decide

private theorem length_block01 : block01.length = 48 := rfl
private theorem upper_block01 : sumRows rowUpper 48 block01 =
    1271402919821512 := by decide
private theorem line_block01 : sumRows rowLine 48 block01 =
    5267531037926844475440143833087677743217687205645594146317280 := by decide

private theorem length_block02 : block02.length = 48 := rfl
private theorem upper_block02 : sumRows rowUpper 96 block02 =
    3775246343187094 := by decide
private theorem line_block02 : sumRows rowLine 96 block02 =
    15384301332625761218325646297779253871306348007343942789212048 := by decide

private theorem length_block03 : block03.length = 48 := rfl
private theorem upper_block03 : sumRows rowUpper 144 block03 =
    8165397661255912 := by decide
private theorem line_block03 : sumRows rowLine 144 block03 =
    32009026450266450973038459570101421067468888106837674696303968 := by decide

private theorem length_block04 : block04.length = 48 := rfl
private theorem upper_block04 : sumRows rowUpper 192 block04 =
    14022951990886648 := by decide
private theorem line_block04 : sumRows rowLine 192 block04 =
    51892124554978160402428219909453392912220878607093853438953824 := by decide

private theorem length_block05 : block05.length = 48 := rfl
private theorem upper_block05 : sumRows rowUpper 240 block05 =
    20005943249891182 := by decide
private theorem line_block05 : sumRows rowLine 240 block05 =
    68732216356737911501000499928598696665285500514108359054967296 := by decide

private theorem length_block06 : block06.length = 48 := rfl
private theorem upper_block06 : sumRows rowUpper 288 block06 =
    25013327650296782 := by decide
private theorem line_block06 : sumRows rowLine 288 block06 =
    78402634569609439647883528549254488462055424405407540641787864 := by decide

private theorem length_block07 : block07.length = 48 := rfl
private theorem upper_block07 : sumRows rowUpper 336 block07 =
    29459968841019782 := by decide
private theorem line_block07 : sumRows rowLine 336 block07 =
    82726363712755660779486812058593109304830834199714477896548592 := by decide

private theorem length_block08 : block08.length = 48 := rfl
private theorem upper_block08 : sumRows rowUpper 384 block08 =
    35852438442753378 := by decide
private theorem line_block08 : sumRows rowLine 384 block08 =
    88152579566998305981847817078020581886462314491477914301417904 := by decide

private theorem length_block09 : block09.length = 48 := rfl
private theorem upper_block09 : sumRows rowUpper 432 block09 =
    44788757580423660 := by decide
private theorem line_block09 : sumRows rowLine 432 block09 =
    93590138544916578899173959413044757944503764512864642746086904 := by decide

private theorem length_block10 : block10.length = 48 := rfl
private theorem upper_block10 : sumRows rowUpper 480 block10 =
    54287134046863990 := by decide
private theorem line_block10 : sumRows rowLine 480 block10 =
    92890712491123678709157650334514004966861787326666164848672696 := by decide

private theorem length_block11 : block11.length = 48 := rfl
private theorem upper_block11 : sumRows rowUpper 528 block11 =
    60937034449496980 := by decide
private theorem line_block11 : sumRows rowLine 528 block11 =
    81359450551490108821449419707143594762082756126542283239729408 := by decide

private theorem length_block12 : block12.length = 48 := rfl
private theorem upper_block12 : sumRows rowUpper 576 block12 =
    63860868329395688 := by decide
private theorem line_block12 : sumRows rowLine 576 block12 =
    61984798219266818796568076166451504494040435219208950251510528 := by decide

private theorem length_block13 : block13.length = 48 := rfl
private theorem upper_block13 : sumRows rowUpper 624 block13 =
    66270513306983342 := by decide
private theorem line_block13 : sumRows rowLine 624 block13 =
    41293940693581149298914532757739075468773557013789628150006216 := by decide

private theorem length_block14 : block14.length = 48 := rfl
private theorem upper_block14 : sumRows rowUpper 672 block14 =
    75949655885487690 := by decide
private theorem line_block14 : sumRows rowLine 672 block14 =
    22489000768305112199120276464659563046805428227878770699102816 := by decide

private theorem length_block15 : block15.length = 48 := rfl
private theorem upper_block15 : sumRows rowUpper 720 block15 =
    91625473410117958 := by decide
private theorem line_block15 : sumRows rowLine 720 block15 =
    -375745992173929261022331014871129964723193877017628165958488 := by decide

private theorem length_block16 : block16.length = 48 := rfl
private theorem upper_block16 : sumRows rowUpper 768 block16 =
    104853428764915512 := by decide
private theorem line_block16 : sumRows rowLine 768 block16 =
    -29061943526173829250039746770168976228161790556079409521729656 := by decide

private theorem length_block17 : block17.length = 48 := rfl
private theorem upper_block17 : sumRows rowUpper 816 block17 =
    101867005045293506 := by decide
private theorem line_block17 : sumRows rowLine 816 block17 =
    -51820919863009902440632578914057626697560648837305059366977674 := by decide

private theorem length_block18 : block18.length = 48 := rfl
private theorem upper_block18 : sumRows rowUpper 864 block18 =
    76225967433955436 := by decide
private theorem line_block18 : sumRows rowLine 864 block18 =
    -53164239447469990047746788138063045729386329697498568533019692 := by decide

private theorem length_block19 : block19.length = 48 := rfl
private theorem upper_block19 : sumRows rowUpper 912 block19 =
    42126117414960966 := by decide
private theorem line_block19 : sumRows rowLine 912 block19 =
    -37372518993196013373676334966078488130795117398730845664162592 := by decide

private theorem length_block20 : block20.length = 48 := rfl
private theorem upper_block20 : sumRows rowUpper 960 block20 =
    13002109335007912 := by decide
private theorem line_block20 : sumRows rowLine 960 block20 =
    -14959231401748285977338628346980901847040000000000000000000000 := by decide

private theorem length_block21 : block21.length = 48 := rfl
private theorem upper_block21 : sumRows rowUpper 1008 block21 =
    1157618648899818 := by decide
private theorem line_block21 : sumRows rowLine 1008 block21 =
    -1331867376106866401472441029107447234560000000000000000000000 := by decide

private theorem length_block22 : block22.length = 48 := rfl
private theorem upper_block22 : sumRows rowUpper 1056 block22 =
    8368996010940 := by decide
private theorem line_block22 : sumRows rowLine 1056 block22 =
    -9628725978397843353190679513451724800000000000000000000000 := by decide

private theorem length_block23 : block23.length = 48 := rfl
private theorem upper_block23 : sumRows rowUpper 1104 block23 =
    419039482 := by decide
private theorem line_block23 : sumRows rowLine 1104 block23 =
    -482114741246553373833715714621440000000000000000000000 := by decide

private theorem upper_total :
    sumRows rowUpper 0 data.toList = 934700957952733338 := by
  change sumRows rowUpper 0 dataRows = _
  simp only [dataRows, sumRows_append, List.length_append, length_block00, length_block01, length_block02, length_block03, length_block04, length_block05,
    length_block06, length_block07, length_block08, length_block09, length_block10, length_block11,
    length_block12, length_block13, length_block14, length_block15, length_block16, length_block17,
    length_block18, length_block19, length_block20, length_block21, length_block22, length_block23]
  norm_num only
  norm_num [upper_block00, upper_block01, upper_block02, upper_block03, upper_block04, upper_block05,
      upper_block06, upper_block07, upper_block08, upper_block09, upper_block10, upper_block11,
      upper_block12, upper_block13, upper_block14, upper_block15, upper_block16, upper_block17,
      upper_block18, upper_block19, upper_block20, upper_block21, upper_block22, upper_block23]

private theorem curvature_integer :
    1000 * (∑ j ∈ Finset.range 1152, rawUpper j) < 3565601189 * (1000000 * 64^3 : ℤ) := by
  simp only [rawUpper, ← sumRows_data rowUpper, upper_total]
  decide

private theorem line_total :
    sumRows rowLine 0 data.toList = 628784784323882461852726429698652228510412961438821979048190074 := by
  change sumRows rowLine 0 dataRows = _
  simp only [dataRows, sumRows_append, List.length_append, length_block00, length_block01, length_block02, length_block03, length_block04, length_block05,
    length_block06, length_block07, length_block08, length_block09, length_block10, length_block11,
    length_block12, length_block13, length_block14, length_block15, length_block16, length_block17,
    length_block18, length_block19, length_block20, length_block21, length_block22, length_block23]
  norm_num only
  norm_num [line_block00, line_block01, line_block02, line_block03, line_block04, line_block05,
      line_block06, line_block07, line_block08, line_block09, line_block10, line_block11,
      line_block12, line_block13, line_block14, line_block15, line_block16, line_block17,
      line_block18, line_block19, line_block20, line_block21, line_block22, line_block23]

private theorem slope_integer :
    521202 * (1000000 * 64^3 * sincDen) < ∑ j ∈ Finset.range 1152, rawLine j := by
  simp only [rawLine, ← sumRows_data rowLine, line_total]
  decide

theorem checked_curvature_sum :
    (∑ j ∈ Finset.range 1152, upperMass j / 64) < (3565601189 : ℚ)/1000 := by
  simp only [upper_rat, div_div, ← Finset.sum_div, ← Int.cast_sum]
  have h := (show (1000:ℚ) * ((∑ j ∈ Finset.range 1152, rawUpper j):ℤ) <
      3565601189 * (1000000 * 64^3 : ℚ) by exact_mod_cast curvature_integer)
  apply (div_lt_div_iff₀ (by norm_num) (by norm_num)).2
  linarith

theorem checked_slope_sum :
    (521202 : ℚ) < ∑ j ∈ Finset.range 1152, lowerLine j / 64 := by
  simp only [line_rat, ← Finset.sum_div, ← Int.cast_sum]
  apply (lt_div_iff₀ (by norm_num [sincDen])).2
  exact_mod_cast slope_integer

/-- Pointwise input still required for the rounded table. -/
def Encloses (K : ℝ → ℝ) : Prop :=
  ∀ j < 1152, ∀ x ∈ Icc (node j : ℝ) (node (j+1) : ℝ),
    (lowerK j : ℝ) ≤ K x ∧ K x ≤ (upperK j : ℝ)

private theorem node_eq (j : ℕ) : (node j : ℝ) = j/64 := by simp [node]

private theorem covers (x : ℝ) (hx : x ∈ Icc (0:ℝ) 18) :
    ∃ j < 1152, x ∈ Icc (node j : ℝ) (node (j+1) : ℝ) := by
  by_cases h : x = 18
  · refine ⟨1151, by decide, ?_⟩
    rw [h, node_eq, node_eq]
    norm_num
  · let j := ⌊64*x⌋₊
    have hj : (j:ℝ) ≤ 64*x := Nat.floor_le (by linarith [hx.1])
    have hj' : 64*x < (j:ℝ)+1 := Nat.lt_floor_add_one _
    refine ⟨j, ?_, ?_⟩
    · have hx' : x < 18 := lt_of_le_of_ne hx.2 h
      exact_mod_cast (show (j:ℝ)<1152 by linarith)
    · rw [node_eq, node_eq, Nat.cast_add, Nat.cast_one]
      exact ⟨by linarith, by linarith⟩

private theorem lowerK_nonneg (j : ℕ) : (0 : ℝ) ≤ (lowerK j : ℝ) := by
  unfold lowerK
  push_cast
  positivity

private theorem upperK_nonneg (j : ℕ) : (0 : ℝ) ≤ (upperK j : ℝ) := by
  unfold upperK
  push_cast
  positivity

theorem nonneg_of_grid {K : ℝ → ℝ} (h : Encloses K) : ∀ x ∈ Icc (0 : ℝ) 18, 0 ≤ K x := by
  intro x hx
  obtain ⟨j,hj,hjx⟩ := covers x hx
  exact (lowerK_nonneg j).trans (h j hj x hjx).1

private theorem mass_bounds {K : ℝ → ℝ} (h : Encloses K)
    {j : ℕ} (hj : j < 1152) {x : ℝ} (hx : x ∈ Icc (node j : ℝ) (node (j+1) : ℝ)) :
    (lowerMass j : ℝ) ≤ 2*K x*x^2 ∧ 2*K x*x^2 ≤ (upperMass j : ℝ) := by
  have hK := h j hj x hx
  have ho : (0 : ℝ) ≤ (node j : ℝ) := by rw [node_eq]; positivity
  have hx0 : 0 ≤ x := ho.trans hx.1
  have hK0 := (lowerK_nonneg j).trans hK.1
  have hU := upperK_nonneg j
  simp only [lowerMass, upperMass, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  constructor
  · exact mul_le_mul (mul_le_mul_of_nonneg_left hK.1 (by norm_num))
      (pow_le_pow_left₀ ho hx.1 2) (sq_nonneg _) (mul_nonneg (by norm_num) hK0)
  · exact mul_le_mul (mul_le_mul_of_nonneg_left hK.2 (by norm_num))
      (pow_le_pow_left₀ hx0 hx.2 2) (sq_nonneg _) (mul_nonneg (by norm_num) hU)

private theorem sinc_bound {t x : ℝ} (ht : |t| ≤ 27/100) (hx0 : 0 ≤ x)
    {j : ℕ} (hx : x ≤ (node (j+1):ℝ)) :
    (sincLower j : ℝ) ≤ GaussianSideIntegral.sinc (t*x) := by
  let y : ℚ := (27/100 : ℚ) * node (j+1)
  have hy : |t*x| ≤ (y:ℝ) := by
    rw [abs_mul, abs_of_nonneg hx0]
    dsimp only [y]
    push_cast
    exact mul_le_mul ht hx hx0 (by norm_num)
  have h := QuarticSlope.uniform_sinc_lower (t*x) (y:ℝ) hy
  change ((if y ≤ 4 then 1-y^2/6+y^4/120-y^6/5040+y^8/362880-y^10/39916800 else -1/4 : ℚ):ℝ) ≤ _
  by_cases hy4 : y ≤ 4
  · rw [if_pos hy4]
    rw [if_pos (by exact_mod_cast hy4)] at h
    simpa [QuarticSlope.lowerPoly] using h
  · rw [if_neg hy4]
    rw [if_neg (by exact_mod_cast hy4)] at h
    rw [show ((-1/4:ℚ):ℝ) = (-1/4:ℝ) by norm_num]
    simpa only [neg_div] using h

private theorem line_bound {K : ℝ → ℝ} (h : Encloses K)
    {t x : ℝ} (ht : |t| ≤ 27/100) {j : ℕ} (hj : j < 1152)
    (hx : x ∈ Icc (node j : ℝ) (node (j+1) : ℝ)) :
    (lowerLine j : ℝ) ≤ 2*K x*x^2*GaussianSideIntegral.sinc (t*x) := by
  have hx0 : 0 ≤ x := (show 0 ≤ (node j : ℝ) by rw [node_eq]; positivity).trans hx.1
  have hm := mass_bounds h hj hx
  have hp : 0 ≤ 2*K x*x^2 := by have := (lowerK_nonneg j).trans (h j hj x hx).1; positivity
  have hs := sinc_bound ht hx0 hx.2
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hs hp)
  unfold lowerLine
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_right hm.1 (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_right hm.2 (by exact_mod_cast (le_of_not_ge hc))

private theorem integral_on_grid {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 18)) :
    ∑ j ∈ Finset.range 1152, ∫ x in (node j : ℝ)..(node (j+1) : ℝ), f x = ∫ x in Icc (0:ℝ) 18, f x := by
  have hint (j : ℕ) (hj : j < 1152) : IntervalIntegrable f volume (node j : ℝ) (node (j+1) : ℝ) := by
    rw [node_eq, node_eq]
    apply IntervalIntegrable.mono_set (a := (0:ℝ)) (b := 18)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 (hf.mono_set Ioc_subset_Icc_self))
    have hj' : ((j+1:ℕ):ℝ) ≤ 1152 := by exact_mod_cast (show j+1 ≤ 1152 by omega)
    push_cast at hj' ⊢
    have hab : (j:ℝ)/64 ≤ ((j:ℝ)+1)/64 := by linarith
    rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (0:ℝ) ≤ 18)]
    exact Icc_subset_Icc (by positivity) (by linarith)
  rw [intervalIntegral.sum_integral_adjacent_intervals hint, node_eq, node_eq]
  norm_num [intervalIntegral.integral_of_le, integral_Icc_eq_integral_Ioc]

private theorem cell_width (j : ℕ) : (node (j+1):ℝ) - (node j:ℝ) = 1/64 := by
  rw [node_eq, node_eq, Nat.cast_add, Nat.cast_one]
  ring

theorem curvature_of_grid {K : ℝ → ℝ} (h : Encloses K)
    (hi : IntegrableOn (fun x => 2*K x*x^2) (Icc (0:ℝ) 18)) :
    (∫ x in Icc (0 : ℝ) 18, 2*K x*x^2) ≤ 3565602 - (1 : ℝ)/10^10 := by
  rw [← integral_on_grid hi]
  have hc : (∑ j ∈ Finset.range 1152, (upperMass j:ℝ)/64) ≤ 3565602 - (1:ℝ)/10^10 := by
    have hh : (∑ j ∈ Finset.range 1152, (upperMass j:ℝ)/64) < 3565601189/1000 := by
      have hh' := (Rat.cast_lt (K := ℝ)).mpr checked_curvature_sum
      simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hh'
    linarith
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) hc
  have hab : (node j : ℝ) ≤ (node (j+1):ℝ) := by rw [node_eq,node_eq]; push_cast; linarith
  have hf : IntervalIntegrable (fun x => 2*K x*x^2) volume (node j:ℝ) (node (j+1):ℝ) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    refine hi.mono_set ((Ioc_subset_Icc_self).trans (Icc_subset_Icc ?_ ?_))
    · rw [node_eq]; positivity
    · rw [node_eq]; push_cast
      have hjn := Finset.mem_range.mp hj
      have hj' : ((j+1:ℕ):ℝ) ≤ 1152 := by exact_mod_cast (show j+1 ≤ 1152 by omega)
      push_cast at hj'
      linarith
  have hd := intervalIntegral.integral_mono_on hab hf (intervalIntegrable_const (c := (upperMass j:ℝ)))
    (fun x hx => (mass_bounds h (Finset.mem_range.mp hj) hx).2)
  rw [intervalIntegral.integral_const, cell_width, smul_eq_mul] at hd
  simpa [div_eq_mul_inv, mul_comm] using hd

theorem slope_of_grid {K : ℝ → ℝ} (h : Encloses K)
    {t : ℝ} (ht : |t| ≤ 27/100)
    (hi : IntegrableOn (fun x => 2*K x*x^2*GaussianSideIntegral.sinc (t*x)) (Icc (0:ℝ) 18)) :
    519994 + (1 : ℝ)/10^10 < ∫ x in Icc (0:ℝ) 18, 2*K x*x^2*GaussianSideIntegral.sinc (t*x) := by
  rw [← integral_on_grid hi]
  have hc : 519994 + (1:ℝ)/10^10 < ∑ j ∈ Finset.range 1152, (lowerLine j:ℝ)/64 := by
    have hh : (521202:ℝ) < ∑ j ∈ Finset.range 1152, (lowerLine j:ℝ)/64 := by
      exact_mod_cast checked_slope_sum
    linarith
  refine lt_of_lt_of_le hc (Finset.sum_le_sum fun j hj => ?_)
  have hab : (node j : ℝ) ≤ (node (j+1):ℝ) := by rw [node_eq,node_eq]; push_cast; linarith
  have hf : IntervalIntegrable (fun x => 2*K x*x^2*GaussianSideIntegral.sinc (t*x)) volume
      (node j:ℝ) (node (j+1):ℝ) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    refine hi.mono_set ((Ioc_subset_Icc_self).trans (Icc_subset_Icc ?_ ?_))
    · rw [node_eq]; positivity
    · rw [node_eq]; push_cast
      have hjn := Finset.mem_range.mp hj
      have hj' : ((j+1:ℕ):ℝ) ≤ 1152 := by exact_mod_cast (show j+1 ≤ 1152 by omega)
      push_cast at hj'
      linarith
  have hd := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := (lowerLine j:ℝ))) hf
    (fun x hx => line_bound h ht (Finset.mem_range.mp hj) hx)
  rw [intervalIntegral.integral_const, cell_width, smul_eq_mul] at hd
  simpa [div_eq_mul_inv, mul_comm] using hd

#print axioms checked_curvature_sum
#print axioms checked_slope_sum
#print axioms nonneg_of_grid
#print axioms curvature_of_grid
#print axioms slope_of_grid

end QuarticGrid
