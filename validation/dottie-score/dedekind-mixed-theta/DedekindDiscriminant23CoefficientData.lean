import DedekindDiscriminant23AmplitudeData

/-! Validate the 72 active coefficients once and reuse them on every rectangle.
The other parity is identically zero. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

private def activeParity (k : ℕ) : Bool :=
  k % 2 == 1

private def activeCoefficientBox (k : ℕ) : Box :=
  discriminant23ReadingCoefficientBox
    (discriminant23StoredReadingAmplitudeBox (activeParity k)) (activeParity k) k

private def coefficientBoxes : Array Box := #[
  ⟨538997652033613969539352, 538997652035683914707444⟩,
  ⟨1101413509226066567132306, 1101413509231058167727799⟩,
  ⟨3304240527678199701404736, 3304240527693174503176810⟩,
  ⟨6218949860932756220080201, 6218949860966484234128693⟩,
  ⟨9328424791399134330226830, 9328424791449726351109024⟩,
  ⟨16356259339833797588843070, 16356259339937712304132312⟩,
  ⟨16356259339833797589627576, 16356259339937712303536504⟩,
  ⟨26944105478758683424615177, 26944105478954988633881832⟩,
  ⟨20208079109069012571922673, 20208079109216241472851763⟩,
  ⟨31481541278530955861204807, 31481541278789402931132789⟩,
  ⟨18888924767118573526812864, 18888924767273641751368153⟩,
  ⟨27974870037435661024754802, 27974870037690825666541506⟩,
  ⟨13987435018717830533189736, 13987435018845412818421467⟩,
  ⟨19778734405034785054479940, 19778734405232974241908218⟩,
  ⟨8476600459300622198130730, 8476600459385560366866172⟩,
  ⟨11485396693522034493037227, 11485396693647311365762957⟩,
  ⟨4307023760070762972702928, 4307023760117741735681079⟩,
  ⟨5609120260230721258513186, 5609120260296818424597964⟩,
  ⟨1869706753410240455119069, 1869706753432272783361527⟩,
  ⟨2346540781514758318950478, 2346540781544443711958888⟩,
  ⟨703962234454427522991751, 703962234463333094568929⟩,
  ⟨853366236306758722720519, 853366236318286979643445⟩,
  ⟨232736246265479669025471, 232736246268623709608508⟩,
  ⟨273056664359301275598005, 273056664363222434985437⟩,
  ⟨68264166089825328221190, 68264166090805602230371⟩,
  ⟨77651854576624727246336, 77651854577805404767338⟩,
  ⟨17919658748451864408130, 17919658748724321177305⟩,
  ⟨19794193089246833446887, 19794193089564396351469⟩,
  ⟨4241612804838608861676, 4241612804906655165981⟩,
  ⟨4556053991806683654793, 4556053991883571202018⟩,
  ⟨911210798361337317483, 911210798376713824470⟩,
  ⟨952921884012970695099, 952921884029839945831⟩,
  ⟨178672853252432184099, 178672853255594862335⟩,
  ⟨182114487703186999782, 182114487706560306239⟩,
  ⟨32137850771150695327, 32137850771745901752⟩,
  ⟨31956386737322534763, 31956386737940445038⟩,
  ⟨5326064456220434069, 5326064456323399166⟩,
  ⟨5170752771280268086, 5170752771384409948⟩,
  ⟨816434648096886876, 816434648113326147⟩,
  ⟨774415948925738164, 774415948941950637⟩,
  ⟨116162392338861116, 116162392341292350⟩,
  ⟨107714342967466970, 107714342969806441⟩,
  ⟨15387763281066697, 15387763281400976⟩,
  ⟨13955405204408285, 13955405204722321⟩,
  ⟨1903009800601036, 1903009800644062⟩,
  ⟨1688609027598336, 1688609027637830⟩,
  ⟨220253351425773, 220253351431144⟩,
  ⟨191274425830556, 191274425835396⟩,
  ⟨23909303228716, 23909303229539⟩,
  ⟨20325487701343, 20325487702101⟩,
  ⟨2439058524061, 2439058524374⟩,
  ⟨2030032798517, 2030032798829⟩,
  ⟨234234553573, 234234553834⟩,
  ⟨190890821634, 190890821894⟩,
  ⟨21210091188, 21210091445⟩,
  ⟨16926268147, 16926268403⟩,
  ⟨1813528630, 1813528886⟩,
  ⟨1417258370, 1417258626⟩,
  ⟨146612832, 146613088⟩,
  ⟨112206599, 112206855⟩,
  ⟨11220561, 11220817⟩,
  ⟨8409994, 8410250⟩,
  ⟨813771, 814027⟩,
  ⟨597330, 597586⟩,
  ⟨55907, 56163⟩,
  ⟨40163, 40419⟩,
  ⟨3557, 3813⟩,
  ⟨2472, 2728⟩,
  ⟨120, 376⟩,
  ⟨53, 309⟩,
  ⟨-91, 165⟩,
  ⟨-93, 163⟩
]

private def storedActiveCoefficient (k : ℕ) : Box :=
  coefficientBoxes[k]?.getD (constant 0)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock0 : ∀ j : Fin 4,
    activeCoefficientBox (0 + j.val) = storedActiveCoefficient (0 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock1 : ∀ j : Fin 4,
    activeCoefficientBox (4 + j.val) = storedActiveCoefficient (4 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock2 : ∀ j : Fin 4,
    activeCoefficientBox (8 + j.val) = storedActiveCoefficient (8 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock3 : ∀ j : Fin 4,
    activeCoefficientBox (12 + j.val) = storedActiveCoefficient (12 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock4 : ∀ j : Fin 4,
    activeCoefficientBox (16 + j.val) = storedActiveCoefficient (16 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock5 : ∀ j : Fin 4,
    activeCoefficientBox (20 + j.val) = storedActiveCoefficient (20 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock6 : ∀ j : Fin 4,
    activeCoefficientBox (24 + j.val) = storedActiveCoefficient (24 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock7 : ∀ j : Fin 4,
    activeCoefficientBox (28 + j.val) = storedActiveCoefficient (28 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock8 : ∀ j : Fin 4,
    activeCoefficientBox (32 + j.val) = storedActiveCoefficient (32 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock9 : ∀ j : Fin 4,
    activeCoefficientBox (36 + j.val) = storedActiveCoefficient (36 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock10 : ∀ j : Fin 4,
    activeCoefficientBox (40 + j.val) = storedActiveCoefficient (40 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock11 : ∀ j : Fin 4,
    activeCoefficientBox (44 + j.val) = storedActiveCoefficient (44 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock12 : ∀ j : Fin 4,
    activeCoefficientBox (48 + j.val) = storedActiveCoefficient (48 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock13 : ∀ j : Fin 4,
    activeCoefficientBox (52 + j.val) = storedActiveCoefficient (52 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock14 : ∀ j : Fin 4,
    activeCoefficientBox (56 + j.val) = storedActiveCoefficient (56 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock15 : ∀ j : Fin 4,
    activeCoefficientBox (60 + j.val) = storedActiveCoefficient (60 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock16 : ∀ j : Fin 4,
    activeCoefficientBox (64 + j.val) = storedActiveCoefficient (64 + j.val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem coefficientBlock17 : ∀ j : Fin 4,
    activeCoefficientBox (68 + j.val) = storedActiveCoefficient (68 + j.val) := by
  decide +kernel

private theorem coefficient_blocks (k : ℕ) (hk : k < 72) :
    activeCoefficientBox k = storedActiveCoefficient k := by
  generalize hq : k / 4 = q
  have hqMax : q ≤ 17 := by omega
  interval_cases q
  · have hAt : 0 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock0 ⟨k % 4, by omega⟩
  · have hAt : 4 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock1 ⟨k % 4, by omega⟩
  · have hAt : 8 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock2 ⟨k % 4, by omega⟩
  · have hAt : 12 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock3 ⟨k % 4, by omega⟩
  · have hAt : 16 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock4 ⟨k % 4, by omega⟩
  · have hAt : 20 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock5 ⟨k % 4, by omega⟩
  · have hAt : 24 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock6 ⟨k % 4, by omega⟩
  · have hAt : 28 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock7 ⟨k % 4, by omega⟩
  · have hAt : 32 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock8 ⟨k % 4, by omega⟩
  · have hAt : 36 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock9 ⟨k % 4, by omega⟩
  · have hAt : 40 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock10 ⟨k % 4, by omega⟩
  · have hAt : 44 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock11 ⟨k % 4, by omega⟩
  · have hAt : 48 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock12 ⟨k % 4, by omega⟩
  · have hAt : 52 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock13 ⟨k % 4, by omega⟩
  · have hAt : 56 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock14 ⟨k % 4, by omega⟩
  · have hAt : 60 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock15 ⟨k % 4, by omega⟩
  · have hAt : 64 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock16 ⟨k % 4, by omega⟩
  · have hAt : 68 + k % 4 = k := by omega
    simpa only [hAt] using coefficientBlock17 ⟨k % 4, by omega⟩

private def computedCoefficient (odd : Bool) (k : ℕ) : Box :=
  discriminant23ReadingCoefficientBox (discriminant23StoredReadingAmplitudeBox odd) odd k

/-- Only the 72-term prefix is stored. The general enclosure remains
available for any unlisted order. -/
def discriminant23StoredReadingCoefficientBox (odd : Bool) (k : ℕ) : Box :=
  if k < 72 then
    if k % 2 = (if odd then 1 else 0) then storedActiveCoefficient k else constant 0
  else computedCoefficient odd k

theorem discriminant23_storedReadingCoefficientBox_contains (odd : Bool) (k : ℕ) :
    Contains (discriminant23StoredReadingCoefficientBox odd k) (discriminant23ReadingCoefficient odd k) := by
  have hEval := discriminant23_readingCoefficientBox_contains
    (discriminant23StoredReadingAmplitudeBox odd) odd k
    (fun j hj ↦ discriminant23_storedAmplitudeBox_contains odd hj)
  change Contains (computedCoefficient odd k) (discriminant23ReadingCoefficient odd k) at hEval
  unfold discriminant23StoredReadingCoefficientBox
  by_cases hK : k < 72
  · simp only [hK, ite_true]
    rw [← coefficient_blocks k hK]
    cases odd <;> rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
      simpa [activeCoefficientBox, activeParity, computedCoefficient, discriminant23ReadingCoefficientBox,
        h] using hEval
  · simpa only [hK, ite_false] using hEval

#print axioms coefficientBlock0
#print axioms coefficient_blocks
#print axioms discriminant23_storedReadingCoefficientBox_contains

end FieldTarget

