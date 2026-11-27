import DedekindDiscriminant23CharacterGrid

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

private theorem block00 : discriminant23CharacterGridBlock true 0 64 =
    ⟨37216952533589118054202791, 37216952533650993700127289⟩ := by
  decide +kernel

private theorem block01 : discriminant23CharacterGridBlock true 64 64 =
    ⟨1083848296986521228932792, 1083848297004633412154004⟩ := by
  decide +kernel

private theorem block02 : discriminant23CharacterGridBlock true 128 64 =
    ⟨-27475187622301953827136708, -27475187622249018150052750⟩ := by
  decide +kernel

private theorem block03 : discriminant23CharacterGridBlock true 192 64 =
    ⟨-22362897665807983594986619, -22362897665759881080718223⟩ := by
  decide +kernel

private theorem block04 : discriminant23CharacterGridBlock true 256 64 =
    ⟨-1726892637083880665192919, -1726892637072412144500807⟩ := by
  decide +kernel

private theorem block05 : discriminant23CharacterGridBlock true 320 64 =
    ⟨8079197170816653856741348, 8079197170840749645262501⟩ := by
  decide +kernel

private theorem block06 : discriminant23CharacterGridBlock true 384 64 =
    ⟨4994320099342607870536445, 4994320099360063232740764⟩ := by
  decide +kernel

private theorem block07 : discriminant23CharacterGridBlock true 448 64 =
    ⟨450408572782246038672053, 450408572785228888536791⟩ := by
  decide +kernel

private theorem block08 : discriminant23CharacterGridBlock true 512 64 =
    ⟨-653274647263682106155897, -653274647260296053563478⟩ := by
  decide +kernel

private theorem block09 : discriminant23CharacterGridBlock true 576 64 =
    ⟨-255312864425980623933733, -255312864424406375052261⟩ := by
  decide +kernel

private theorem block10 : discriminant23CharacterGridBlock true 640 64 =
    ⟨-17697008151396949550301, -17697008151240500827554⟩ := by
  decide +kernel

private theorem block11 : discriminant23CharacterGridBlock true 704 64 =
    ⟨6544672069950579662321, 6544672070011606613513⟩ := by
  decide +kernel

private theorem block12 : discriminant23CharacterGridBlock true 768 64 =
    ⟨1138807790372438133468, 1138807790385162008596⟩ := by
  decide +kernel

private theorem block13 : discriminant23CharacterGridBlock true 832 64 =
    ⟨35031512845613043771, 35031512846106774549⟩ := by
  decide +kernel

private theorem block14 : discriminant23CharacterGridBlock true 896 64 =
    ⟨-1901254521691265118, -1901254521658638532⟩ := by
  decide +kernel

private theorem block15 : discriminant23CharacterGridBlock true 960 63 =
    ⟨-78592161703164362, -78592161701523003⟩ := by
  decide +kernel

/-- Exact directed sum of the higher row's interior samples. -/
theorem discriminant23_characterGridUpper_exact : discriminant23CharacterGridBlock true 0 1023 =
    ⟨-658819239991245481460668, -658819239749025910658601⟩ := by
  simp only [
    show discriminant23CharacterGridBlock true 0 1023 =
      add (discriminant23CharacterGridBlock true 0 64)
        (discriminant23CharacterGridBlock true 64 959) from
      discriminant23_characterGridBlock_append true 0 64 959,
    show discriminant23CharacterGridBlock true 64 959 =
      add (discriminant23CharacterGridBlock true 64 64)
        (discriminant23CharacterGridBlock true 128 895) from
      discriminant23_characterGridBlock_append true 64 64 895,
    show discriminant23CharacterGridBlock true 128 895 =
      add (discriminant23CharacterGridBlock true 128 64)
        (discriminant23CharacterGridBlock true 192 831) from
      discriminant23_characterGridBlock_append true 128 64 831,
    show discriminant23CharacterGridBlock true 192 831 =
      add (discriminant23CharacterGridBlock true 192 64)
        (discriminant23CharacterGridBlock true 256 767) from
      discriminant23_characterGridBlock_append true 192 64 767,
    show discriminant23CharacterGridBlock true 256 767 =
      add (discriminant23CharacterGridBlock true 256 64)
        (discriminant23CharacterGridBlock true 320 703) from
      discriminant23_characterGridBlock_append true 256 64 703,
    show discriminant23CharacterGridBlock true 320 703 =
      add (discriminant23CharacterGridBlock true 320 64)
        (discriminant23CharacterGridBlock true 384 639) from
      discriminant23_characterGridBlock_append true 320 64 639,
    show discriminant23CharacterGridBlock true 384 639 =
      add (discriminant23CharacterGridBlock true 384 64)
        (discriminant23CharacterGridBlock true 448 575) from
      discriminant23_characterGridBlock_append true 384 64 575,
    show discriminant23CharacterGridBlock true 448 575 =
      add (discriminant23CharacterGridBlock true 448 64)
        (discriminant23CharacterGridBlock true 512 511) from
      discriminant23_characterGridBlock_append true 448 64 511,
    show discriminant23CharacterGridBlock true 512 511 =
      add (discriminant23CharacterGridBlock true 512 64)
        (discriminant23CharacterGridBlock true 576 447) from
      discriminant23_characterGridBlock_append true 512 64 447,
    show discriminant23CharacterGridBlock true 576 447 =
      add (discriminant23CharacterGridBlock true 576 64)
        (discriminant23CharacterGridBlock true 640 383) from
      discriminant23_characterGridBlock_append true 576 64 383,
    show discriminant23CharacterGridBlock true 640 383 =
      add (discriminant23CharacterGridBlock true 640 64)
        (discriminant23CharacterGridBlock true 704 319) from
      discriminant23_characterGridBlock_append true 640 64 319,
    show discriminant23CharacterGridBlock true 704 319 =
      add (discriminant23CharacterGridBlock true 704 64)
        (discriminant23CharacterGridBlock true 768 255) from
      discriminant23_characterGridBlock_append true 704 64 255,
    show discriminant23CharacterGridBlock true 768 255 =
      add (discriminant23CharacterGridBlock true 768 64)
        (discriminant23CharacterGridBlock true 832 191) from
      discriminant23_characterGridBlock_append true 768 64 191,
    show discriminant23CharacterGridBlock true 832 191 =
      add (discriminant23CharacterGridBlock true 832 64)
        (discriminant23CharacterGridBlock true 896 127) from
      discriminant23_characterGridBlock_append true 832 64 127,
    show discriminant23CharacterGridBlock true 896 127 =
      add (discriminant23CharacterGridBlock true 896 64)
        (discriminant23CharacterGridBlock true 960 63) from
      discriminant23_characterGridBlock_append true 896 64 63,
    block00, block01, block02, block03, block04, block05, block06, block07,
    block08, block09, block10, block11, block12, block13, block14, block15]
  decide +kernel

#print axioms discriminant23_characterGridUpper_exact

end FieldTarget
