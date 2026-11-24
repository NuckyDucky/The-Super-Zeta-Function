import DottieProductionJoinOnly
import DottiePairedRowsThrough512
import DottieProductionRows513Through2509
import DottieProductionRows2510Through3511
import DottieProductionRows3512Through4285
import DottieProductionRows4286Through4939
import DottieProductionRows4940Through5516
import DottieProductionRows5517Through6038
import DottieProductionRows6039Through6518
import DottieProductionRows6519Through6966
import DottieProductionRows6967Through7386
import DottieProductionRows7387Through7783
import DottieProductionRows7784Through8162
import DottieProductionRows8163Through8523
import DottieProductionRows8524Through8870
import DottieProductionRows8871Through9204
import DottieProductionRows9205Through9526
import DottieProductionRows9527Through9837
import DottieProductionRows9838Through10139
import DottieProductionRows10140Through10432
import DottieProductionRows10433Through10718
import DottieProductionRows10719Through10995
import DottieProductionRows10996Through11266
import DottieProductionRows11267Through11531
import DottieProductionRows11532Through11790
import DottieProductionRows11791Through12049
import DottieProductionRows12050Through12316
import DottieProductionRows12317Through12589
import DottieProductionRows12590Through12870
import DottieProductionRows12871Through13161
import DottieProductionRows13162Through13464
import DottieProductionRows13465Through13779
import DottieProductionRows13780Through14112
import DottieProductionRows14113Through14466
import DottieProductionRows14467Through14849
import DottieProductionRows14850Through15276
import DottieProductionRows15277Through15783
import DottieProductionRows15784Through16638

namespace QuarticModel

private theorem joinedScore :
    dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 = dottiePairedCandidateTicks ∧
    dottieQuickReferenceScore = dottiePairedCandidateTicks ∧ 0 < dottieCircleReference :=
  dottieProductionScore_of_span_partitions
    dottiePairedRows_1_512
    dottieProductionRows_513_2509
    dottieProductionRows_2510_3511
    dottieProductionRows_3512_4285
    dottieProductionRows_4286_4939
    dottieProductionRows_4940_5516
    dottieProductionRows_5517_6038
    dottieProductionRows_6039_6518
    dottieProductionRows_6519_6966
    dottieProductionRows_6967_7386
    dottieProductionRows_7387_7783
    dottieProductionRows_7784_8162
    dottieProductionRows_8163_8523
    dottieProductionRows_8524_8870
    dottieProductionRows_8871_9204
    dottieProductionRows_9205_9526
    dottieProductionRows_9527_9837
    dottieProductionRows_9838_10139
    dottieProductionRows_10140_10432
    dottieProductionRows_10433_10718
    dottieProductionRows_10719_10995
    dottieProductionRows_10996_11266
    dottieProductionRows_11267_11531
    dottieProductionRows_11532_11790
    dottieProductionRows_11791_12049
    dottieProductionRows_12050_12316
    dottieProductionRows_12317_12589
    dottieProductionRows_12590_12870
    dottieProductionRows_12871_13161
    dottieProductionRows_13162_13464
    dottieProductionRows_13465_13779
    dottieProductionRows_13780_14112
    dottieProductionRows_14113_14466
    dottieProductionRows_14467_14849
    dottieProductionRows_14850_15276
    dottieProductionRows_15277_15783
    dottieProductionRows_15784_16638

theorem dottieProductionFullSpan_eq_candidate :
    dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 = dottiePairedCandidateTicks :=
  joinedScore.1

theorem dottieProductionFullSpan :
    dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 =
      (303339834966217300615369504615526421285720775755844666418981971508403960 : ℤ) :=
  dottieProductionFullSpan_eq_candidate

theorem dottieProductionQuickReferenceScore_eq_candidate :
    dottieQuickReferenceScore = dottiePairedCandidateTicks :=
  joinedScore.2.1

theorem dottieProductionCircleReference_pos : 0 < dottieCircleReference :=
  joinedScore.2.2

end QuarticModel
