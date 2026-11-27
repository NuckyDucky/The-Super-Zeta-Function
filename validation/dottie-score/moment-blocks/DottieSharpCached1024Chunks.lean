import DottieFastSharpWeights
import DottieJointSharp1024Assembly

namespace QuarticModel.DottieFixedIntervals

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000

theorem dottie_sharp_cached_chunk0 :
    dottieFastJointMomentBlock 11 26858 0 128
      0x69408041c9001021209045124824a34d209291189089242288241281050250c8004822a48944024209204a2022083810 = dottieSharpChunk0Ticks := by
  decide +kernel

#print axioms dottie_sharp_cached_chunk0

theorem dottie_sharp_cached_chunk128 :
    dottieFastJointMomentBlock 11 26858 128 128
      0x4944600924130a04920128a40140a041449c5124942928920a28904249240941214a2802452484122412892490512492 = dottieSharpChunk128Ticks := by
  decide +kernel

#print axioms dottie_sharp_cached_chunk128

theorem dottie_sharp_cached_chunk256 :
    dottieFastJointMomentBlock 11 26858 256 128
      0x9244a248a0926a46124924248848040824a24810225200641120100804924129204122800a249a512412104410892400 = dottieSharpChunk256Ticks := by
  decide +kernel

#print axioms dottie_sharp_cached_chunk256

theorem dottie_sharp_cached_chunk384 :
    dottieFastJointMomentBlock 11 26858 384 128
      0x4104a44928834805124c25220944904144a202481229209450c9104825104924244a49220c49124919208a20a01148a2 = dottieSharpChunk384Ticks := by
  decide +kernel

#print axioms dottie_sharp_cached_chunk384

theorem dottie_sharp_cached_chunk512 :
    dottieFastJointMomentBlock 11 26858 512 128
      0x845124901125246140a44888905149128a05120924920e29140218828905120a481200a41449a5044926a4514510414 = dottieSharpChunk512Ticks := by
  decide +kernel

#print axioms dottie_sharp_cached_chunk512

theorem dottie_sharp_cached_chunk640 :
    dottieFastJointMomentBlock 11 26858 640 128
      0x5245145125129040148524120934209101144125108a452000a8008126928a04920000824104904a34221044d0494922 = dottieSharpChunk640Ticks := by
  decide +kernel

#print axioms dottie_sharp_cached_chunk640

theorem dottie_sharp_cached_chunk768 :
    dottieFastJointMomentBlock 11 26858 768 128
      0x4a088290000248089282049c0924022228828041220820120244224104828544904848a24920a20924046a008241a014 = dottieSharpChunk768Ticks := by
  decide +kernel

#print axioms dottie_sharp_cached_chunk768

theorem dottie_sharp_cached_chunk896 :
    dottieFastJointMomentBlock 11 26858 896 128
      0x4022220800921104d28145104910005124c45028104828a248489488069208410a0848220804129224200100d2880521 = dottieSharpChunk896Ticks := by
  decide +kernel

#print axioms dottie_sharp_cached_chunk896

end QuarticModel.DottieFixedIntervals
