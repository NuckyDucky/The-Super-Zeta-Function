import DottieJointMomentRows
import DottieJointRowBody100From0
import DottieJointRowBody37983From0
import DottieJointRowBody37983From128
import DottieJointRowBody101From0

namespace QuarticModel.DottieFixedIntervals

open private rowLimit from DottieSymmetricScore

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

private theorem row100_size : dottiePairRowSize 1442840576 100 = 100 := by decide +kernel
private theorem row101_size : dottiePairRowSize 1442840576 101 = 101 := by decide +kernel

theorem dottie_sharp_row_shapes :
    100 < rowLimit 1442840576 100 ∧ 101 < rowLimit 1442840576 101 ∧
      ¬37983 < rowLimit 1442840576 37983 ∧ (1442840576 : ℕ).sqrt = 37984 := by
  decide +kernel

def dottieSharpRow100Ticks : List (ℤ × ℤ) := [
  (1097301455243191098, 610078168401652919),
  (-330285641627576069, -174673600657359178),
  (49704589998372155, 24973192974875656),
  (-4986390643118051, -2376816194254319),
  (375156733734323, 169381300494276),
  (-22579046603139, -9638771366059),
  (1132386251728, 456129402000),
  (-48676018737, -18457667682),
  (1830722991, 651777277),
  (-61200854, -20395037),
  (1841261, 572327)
]

private theorem row100_replay :
    dottieMomentTicksAdd (dottieJointMomentRowHead 11 1442840576 100) dottieSharpBody100From0Ticks =
      dottieSharpRow100Ticks := by
  decide +kernel

theorem dottie_sharp_row100_complete (k : Fin 11) :
    (dottieSharpRow100Ticks.getD k (0,0)) =
      (dottiePairedRowSpan 1442840576 (fun n => momentWeightRealTicks n k) 100 1,
       dottiePairedRowSpan 1442840576 (fun n => momentWeightImagTicks n k) 100 1) := by
  rw [← row100_replay]
  exact dottie_joint_moment_row_getD 11 1442840576 100 dottieSharpBody100From0Ticks
    (by decide +kernel) k.isLt (by rw [row100_size]; exact dottie_sharp_body100From0_moments k)

def dottieSharpRow101Ticks : List (ℤ × ℤ) := [
  (3430763170204281624, 299858096633425184),
  (-1011919773432566332, -88175384389014437),
  (149322676060235897, 12938299715816884),
  (-14698532739314609, -1263005411179246),
  (1085796888577237, 92265097449459),
  (-64207164362240, -5379568830324),
  (3166011185357, 260734670769),
  (-133898194136, -10803108215),
  (4958265157, 390535871),
  (-163313206, -12510276),
  (4844500, 359443)
]

private theorem row101_replay :
    dottieMomentTicksAdd (dottieJointMomentRowHead 11 1442840576 101) dottieSharpBody101From0Ticks =
      dottieSharpRow101Ticks := by
  decide +kernel

theorem dottie_sharp_row101_complete (k : Fin 11) :
    (dottieSharpRow101Ticks.getD k (0,0)) =
      (dottiePairedRowSpan 1442840576 (fun n => momentWeightRealTicks n k) 101 1,
       dottiePairedRowSpan 1442840576 (fun n => momentWeightImagTicks n k) 101 1) := by
  rw [← row101_replay]
  exact dottie_joint_moment_row_getD 11 1442840576 101 dottieSharpBody101From0Ticks
    (by decide +kernel) k.isLt (by rw [row101_size]; exact dottie_sharp_body101From0_moments k)

private def lastBodyTicks : List (ℤ × ℤ) := [
  (-6058736580068857, 1917080212585521),
  (3993055261228776, -1263466366955140),
  (-1315826336770857, 416348583107423),
  (289068367498043, -91465905326935),
  (-47628162672108, 15070326002134),
  (6277938742735, -1986442707800),
  (-689587011943, 218196708246),
  (64925347519, -20543458326),
  (-5348691469, 1692415407),
  (391677196, -123933261),
  (-25813775, 8167925)
]

private theorem lastBody_replay :
    dottieMomentTicksAdd dottieSharpBody37983From0Ticks dottieSharpBody37983From128Ticks = lastBodyTicks := by
  decide +kernel

private theorem lastBody_moments (k : Fin 11) :
    (lastBodyTicks.getD k (0,0)) =
      (dottiePairRowBlock (fun n => momentWeightRealTicks n k) 37983 0 (dottiePairRowSize 1442840576 37983),
       dottiePairRowBlock (fun n => momentWeightImagTicks n k) 37983 0 (dottiePairRowSize 1442840576 37983)) := by
  have hLeft : (k : ℕ) < dottieSharpBody37983From0Ticks.length := by
    simpa only [show dottieSharpBody37983From0Ticks.length = 11 by decide +kernel] using k.isLt
  have hRight : (k : ℕ) < dottieSharpBody37983From128Ticks.length := by
    simpa only [show dottieSharpBody37983From128Ticks.length = 11 by decide +kernel] using k.isLt
  rw [← lastBody_replay, dottie_moment_ticks_add_getD _ _ hLeft hRight,
    dottie_sharp_body37983From0_moments k, dottie_sharp_body37983From128_moments k,
    show dottiePairRowSize 1442840576 37983 = 128+109 by decide +kernel,
    dottiePairRowBlock_add, dottiePairRowBlock_add]

def dottieSharpRow37983Ticks : List (ℤ × ℤ) := [
  (-5573094568169628, 1918816488819242),
  (3672989241944343, -1264610672861320),
  (-1210355378543875, 416725664812939),
  (265897891493982, -91548744837983),
  (-43810493567173, 15083975002782),
  (5774726037317, -1988241803100),
  (-634312659117, 218394326126),
  (59721207832, -20562064262),
  (-4919963046, 1693948204),
  (360282008, -124045506),
  (-23744652, 8175322)
]

private theorem row37983_replay :
    dottieMomentTicksAdd (dottieJointMomentRowHead 11 1442840576 37983) lastBodyTicks =
      dottieSharpRow37983Ticks := by
  decide +kernel

theorem dottie_sharp_row37983_complete (k : Fin 11) :
    (dottieSharpRow37983Ticks.getD k (0,0)) =
      (dottiePairedRowSpan 1442840576 (fun n => momentWeightRealTicks n k) 37983 1,
       dottiePairedRowSpan 1442840576 (fun n => momentWeightImagTicks n k) 37983 1) := by
  rw [← row37983_replay]
  exact dottie_joint_moment_row_getD 11 1442840576 37983 lastBodyTicks
    (by decide +kernel) k.isLt (lastBody_moments k)

def dottieSharpRows100To102Ticks : List (ℤ × ℤ) := [
  (4528064625447472722, 909936265035078103),
  (-1342205415060142401, -262848985046373615),
  (199027266058608052, 37911492690692540),
  (-19684923382432660, -3639821605433565),
  (1460953622311560, 261646397943735),
  (-86786210965379, -15018340196383),
  (4298397437085, 716864072769),
  (-182574212873, -29260775897),
  (6788988148, 1042313148),
  (-224514060, -32905313),
  (6685761, 931770)
]

private theorem rows100To102_replay :
    dottieMomentTicksAdd dottieSharpRow100Ticks dottieSharpRow101Ticks = dottieSharpRows100To102Ticks := by
  decide +kernel

/-- The original sharp moment totals of the two adjacent interior rows. -/
theorem dottie_sharp_rows100To102_complete (k : Fin 11) :
    (dottieSharpRows100To102Ticks.getD k (0,0)) =
      (dottiePairedRowSpan 1442840576 (fun n => momentWeightRealTicks n k) 100 2,
       dottiePairedRowSpan 1442840576 (fun n => momentWeightImagTicks n k) 100 2) := by
  have hLeft : (k : ℕ) < dottieSharpRow100Ticks.length := by
    simpa only [show dottieSharpRow100Ticks.length = 11 by decide +kernel] using k.isLt
  have hRight : (k : ℕ) < dottieSharpRow101Ticks.length := by
    simpa only [show dottieSharpRow101Ticks.length = 11 by decide +kernel] using k.isLt
  rw [← rows100To102_replay]
  exact dottie_joint_moment_span_add 1442840576 100 1 1 _ _ hLeft hRight
    (dottie_sharp_row100_complete k) (dottie_sharp_row101_complete k)

#print axioms dottie_sharp_row_shapes
#print axioms dottie_sharp_row37983_complete
#print axioms dottie_sharp_rows100To102_complete

end QuarticModel.DottieFixedIntervals
