import DottieFastReferenceRows320To328
import DottieFastReferenceRows328To336
import DottieFastReferenceRows336To344
import DottieFastReferenceRows344To352

namespace QuarticModel

private theorem span320_336 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 320 16 = (-31145527842928824128933485292106673349334982526319625967234360563446655530568 : ℤ) := by
  calc
    _ = (-13130024284828794559062453444206285512124753088966017829266613511057734832872 : ℤ) + (-18015503558100029569871031847900387837210229437353608137967747052388920697696 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows320To328, dottieFastReferenceRows328To336] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 320 8 8
    _ = _ := by decide +kernel

private theorem span336_352 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 336 16 = (-41506157806304042230502441031156671456335854369688870062802930471788384866776 : ℤ) := by
  calc
    _ = (-22721888677989991542878301281981951016235199838236104082835244453214633241912 : ℤ) + (-18784269128314050687624139749174720440100654531452765979967686018573751624864 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows336To344, dottieFastReferenceRows344To352] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 336 8 8
    _ = _ := by decide +kernel

private theorem span320_352 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 320 32 = (-72651685649232866359435926323263344805670836896008496030037291035235040397344 : ℤ) := by
  calc
    _ = (-31145527842928824128933485292106673349334982526319625967234360563446655530568 : ℤ) + (-41506157806304042230502441031156671456335854369688870062802930471788384866776 : ℤ) := by
      simpa only [Nat.reduceAdd, span320_336, span336_352] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 320 16 16
    _ = _ := by decide +kernel

theorem dottieDirectReferenceSpan320To352 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 320 32 = (-72651685649232866359435926323263344805670836896008496030037291035235040397344 : ℤ) := by
  simpa only [funext dottie_fast_reference_weight_eq] using span320_352

#print axioms dottieDirectReferenceSpan320To352

end QuarticModel
