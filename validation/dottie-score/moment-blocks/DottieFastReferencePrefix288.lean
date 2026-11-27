import DottieFastReferencePrefix256
import DottieFastReferenceRows256To272
import DottieFastReferenceRows272To288

namespace QuarticModel

theorem dottieDirectReferencePrefix288 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 288 = (154104062758536857482292782289419121720446641037027453597612618578989701814760 : ℤ) := by
  have hnew :
      dottiePairedRowSpan 276824064 dottieFastReferenceWeight 256 32 =
        (-12452098325352602316062630215611533854335715660576762728982441835826243755944 : ℤ) +
        (7193793827456344224942839753357127096359955415017176018792693895223767939000 : ℤ) := by
    simpa only [Nat.reduceAdd, dottieFastReferenceRows256To272,
      dottieFastReferenceRows272To288] using
      dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 256 16 16
  have hdirect := hnew
  rw [funext dottie_fast_reference_weight_eq] at hdirect
  calc
    _ = (159362367256433115573412572751673528478422401282587040307802366519592177631704 : ℤ) +
        ((-12452098325352602316062630215611533854335715660576762728982441835826243755944 : ℤ) +
         (7193793827456344224942839753357127096359955415017176018792693895223767939000 : ℤ)) := by
      simpa only [Nat.reduceAdd, dottieDirectReferencePrefix256, hdirect] using
        dottiePairedRowSpan_add 276824064 dottieDirectReferenceWeight 0 256 32
    _ = _ := by decide +kernel

#print axioms dottieDirectReferencePrefix288

end QuarticModel
