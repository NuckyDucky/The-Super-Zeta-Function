import MellinFixedRanges

open DottieOriented.NativeSpectrum.MellinFixed

/- This executable diagnostic locates failures before the kernel batch replay. -/
#eval (List.range' 576 1728).filter fun i => !(checkTablePanel i)
