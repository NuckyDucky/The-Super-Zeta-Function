import DedekindDiscriminant23CharacterGrid

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

private theorem block00 : discriminant23CharacterGridBlock false 0 64 =
    ⟨38479787214214697982434297, 38479787214278690544457704⟩ := by
  decide +kernel

private theorem block01 : discriminant23CharacterGridBlock false 64 64 =
    ⟨6605980001759957105216863, 6605980001778303876015090⟩ := by
  decide +kernel

private theorem block02 : discriminant23CharacterGridBlock false 128 64 =
    ⟨-22788583464840215922656574, -22788583464796184182902743⟩ := by
  decide +kernel

private theorem block03 : discriminant23CharacterGridBlock false 192 64 =
    ⟨-24808983976730887714217882, -24808983976677285459223197⟩ := by
  decide +kernel

private theorem block04 : discriminant23CharacterGridBlock false 256 64 =
    ⟨-8469147029347877559517002, -8469147029327129053399050⟩ := by
  decide +kernel

private theorem block05 : discriminant23CharacterGridBlock false 320 64 =
    ⟨4047550982756807124343617, 4047550982769130420762202⟩ := by
  decide +kernel

private theorem block06 : discriminant23CharacterGridBlock false 384 64 =
    ⟨5234250795422810740392147, 5234250795441280199564634⟩ := by
  decide +kernel

private theorem block07 : discriminant23CharacterGridBlock false 448 64 =
    ⟨1868635927286879696736212, 1868635927294685327838785⟩ := by
  decide +kernel

private theorem block08 : discriminant23CharacterGridBlock false 512 64 =
    ⟨-32366438388803857417520, -32366438387754389008760⟩ := by
  decide +kernel

private theorem block09 : discriminant23CharacterGridBlock false 576 64 =
    ⟨-217580151307357565198319, -217580151305996224908441⟩ := by
  decide +kernel

private theorem block10 : discriminant23CharacterGridBlock false 640 64 =
    ⟨-58092234758392957338683, -58092234757957535632062⟩ := by
  decide +kernel

private theorem block11 : discriminant23CharacterGridBlock false 704 64 =
    ⟨-3528413366001597345714, -3528413365967533402123⟩ := by
  decide +kernel

private theorem block12 : discriminant23CharacterGridBlock false 768 64 =
    ⟨609635086027945973649, 609635086034909465884⟩ := by
  decide +kernel

private theorem block13 : discriminant23CharacterGridBlock false 832 64 =
    ⟨83598644010532257522, 83598644011680410039⟩ := by
  decide +kernel

private theorem block14 : discriminant23CharacterGridBlock false 896 64 =
    ⟨2479352745952443599, 2479352745993853257⟩ := by
  decide +kernel

private theorem block15 : discriminant23CharacterGridBlock false 960 63 =
    ⟨-10728098743959380, -10728098743691711⟩ := by
  decide +kernel

/-- Exact directed sum of the lower row's interior samples. -/
theorem discriminant23_characterGridLower_exact : discriminant23CharacterGridBlock false 0 1023 =
    ⟨-141381084943698837853168, -141381084701490169800492⟩ := by
  simp only [
    show discriminant23CharacterGridBlock false 0 1023 =
      add (discriminant23CharacterGridBlock false 0 64)
        (discriminant23CharacterGridBlock false 64 959) from
      discriminant23_characterGridBlock_append false 0 64 959,
    show discriminant23CharacterGridBlock false 64 959 =
      add (discriminant23CharacterGridBlock false 64 64)
        (discriminant23CharacterGridBlock false 128 895) from
      discriminant23_characterGridBlock_append false 64 64 895,
    show discriminant23CharacterGridBlock false 128 895 =
      add (discriminant23CharacterGridBlock false 128 64)
        (discriminant23CharacterGridBlock false 192 831) from
      discriminant23_characterGridBlock_append false 128 64 831,
    show discriminant23CharacterGridBlock false 192 831 =
      add (discriminant23CharacterGridBlock false 192 64)
        (discriminant23CharacterGridBlock false 256 767) from
      discriminant23_characterGridBlock_append false 192 64 767,
    show discriminant23CharacterGridBlock false 256 767 =
      add (discriminant23CharacterGridBlock false 256 64)
        (discriminant23CharacterGridBlock false 320 703) from
      discriminant23_characterGridBlock_append false 256 64 703,
    show discriminant23CharacterGridBlock false 320 703 =
      add (discriminant23CharacterGridBlock false 320 64)
        (discriminant23CharacterGridBlock false 384 639) from
      discriminant23_characterGridBlock_append false 320 64 639,
    show discriminant23CharacterGridBlock false 384 639 =
      add (discriminant23CharacterGridBlock false 384 64)
        (discriminant23CharacterGridBlock false 448 575) from
      discriminant23_characterGridBlock_append false 384 64 575,
    show discriminant23CharacterGridBlock false 448 575 =
      add (discriminant23CharacterGridBlock false 448 64)
        (discriminant23CharacterGridBlock false 512 511) from
      discriminant23_characterGridBlock_append false 448 64 511,
    show discriminant23CharacterGridBlock false 512 511 =
      add (discriminant23CharacterGridBlock false 512 64)
        (discriminant23CharacterGridBlock false 576 447) from
      discriminant23_characterGridBlock_append false 512 64 447,
    show discriminant23CharacterGridBlock false 576 447 =
      add (discriminant23CharacterGridBlock false 576 64)
        (discriminant23CharacterGridBlock false 640 383) from
      discriminant23_characterGridBlock_append false 576 64 383,
    show discriminant23CharacterGridBlock false 640 383 =
      add (discriminant23CharacterGridBlock false 640 64)
        (discriminant23CharacterGridBlock false 704 319) from
      discriminant23_characterGridBlock_append false 640 64 319,
    show discriminant23CharacterGridBlock false 704 319 =
      add (discriminant23CharacterGridBlock false 704 64)
        (discriminant23CharacterGridBlock false 768 255) from
      discriminant23_characterGridBlock_append false 704 64 255,
    show discriminant23CharacterGridBlock false 768 255 =
      add (discriminant23CharacterGridBlock false 768 64)
        (discriminant23CharacterGridBlock false 832 191) from
      discriminant23_characterGridBlock_append false 768 64 191,
    show discriminant23CharacterGridBlock false 832 191 =
      add (discriminant23CharacterGridBlock false 832 64)
        (discriminant23CharacterGridBlock false 896 127) from
      discriminant23_characterGridBlock_append false 832 64 127,
    show discriminant23CharacterGridBlock false 896 127 =
      add (discriminant23CharacterGridBlock false 896 64)
        (discriminant23CharacterGridBlock false 960 63) from
      discriminant23_characterGridBlock_append false 896 64 63,
    block00, block01, block02, block03, block04, block05, block06, block07,
    block08, block09, block10, block11, block12, block13, block14, block15]
  decide +kernel

#print axioms discriminant23_characterGridLower_exact

end FieldTarget
