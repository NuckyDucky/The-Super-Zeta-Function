import DottieBandChunkReplay
import DottieBandLucasCheck

/-! Replay and join the first two contiguous chunks of the actual retained
band. Both the zero rows and the split prime rows pass the same row checker. -/

namespace QuarticModel

set_option autoImplicit false
set_option maxRecDepth 8192

private def dottieSecondBandPrimeTable : Array DottieBandPrimeNode := #[
  .leaf 2,
  .leaf 3,
  .leaf 5,
  .leaf 7,
  .leaf 13,
  .leaf 19,
  .leaf 37,
  .leaf 47,
  .leaf 59,
  .lucas 313 10 [0, 0, 0, 1, 4],
  .lucas 709 2 [0, 0, 1, 8],
  .lucas 13913 3 [0, 0, 0, 6, 7],
  .lucas 27827 2 [0, 11],
  .lucas 389579 2 [0, 3, 12],
  .lucas 499549 2 [0, 0, 1, 3, 5, 9],
  .lucas 552423023 5 [0, 10, 13],
  .lucas 7733922323 2 [0, 3, 15],
  .lucas 92807067877 2 [0, 0, 1, 16],
  .lucas 1854467118035498921 3 [0, 0, 0, 2, 14, 17]]

private theorem dottie_second_band_prime_table_checked :
    (List.range 19).all (dottieBandPrimeTableCheck dottieSecondBandPrimeTable) = true := by
  decide +kernel

theorem dottie_second_nonzero_band_prime : Nat.Prime 1854467118035498921 :=
  dottie_band_prime_table_sound dottieSecondBandPrimeTable 18 (fun j hj =>
    List.all_eq_true.mp dottie_second_band_prime_table_checked j (List.mem_range.mpr (by omega)))

private def dottiePilotPrimeOk (n : ℕ) : Bool :=
  decide (n = 1854467118035498909 ∨ n = 1854467118035498921)

private theorem dottie_pilot_prime_ok_sound (p : ℕ) (h : dottiePilotPrimeOk p = true) : p.Prime := by
  rcases of_decide_eq_true h with rfl | rfl
  · exact dottie_first_nonzero_band_prime
  · exact dottie_second_nonzero_band_prime

private def dottieFirstSixteenRows : List DottieBandRow := [
  .zero 1 927233559017749447 none,
  .zero 0 1854467118035498895 none,
  .zero 4 115904194877218681 (some 886705336),
  .zero 0 1854467118035498897 (some 787918361),
  .zero 1 927233559017749449 (some 721930297),
  .zero 0 1854467118035498899 none,
  .zero 2 17 (some 522346910),
  .zero 0 1854467118035498901 (some 384917740),
  .zero 1 927233559017749451 none,
  .zero 0 1854467118035498903 none,
  .zero 3 231808389754437363 none,
  .zero 0 1854467118035498905 (some 1085064926),
  .zero 1 991 none,
  .zero 0 1854467118035498907 none,
  .zero 2 463616779508874727 none,
  .factored 0 [⟨1854467118035498909, 1, some 595362390891366445⟩] 2]

private def dottieSecondSixteenRows : List DottieBandRow := [
  .zero 1 927233559017749455 none,
  .zero 0 1854467118035498911 none,
  .zero 5 11 none,
  .zero 0 3 none,
  .zero 1 927233559017749457 (some 89623146),
  .zero 0 1854467118035498915 none,
  .zero 2 463616779508874729 (some 516293793),
  .zero 0 1854467118035498917 (some 1186415325),
  .zero 1 927233559017749459 none,
  .zero 0 1854467118035498919 none,
  .zero 3 231808389754437365 (some 340241943),
  .factored 0 [⟨1854467118035498921, 1, some 627995296058649686⟩] 2,
  .zero 1 927233559017749461 (some 733400741),
  .zero 0 1854467118035498923 none,
  .zero 2 463616779508874731 none,
  .zero 0 7 none]

theorem dottie_retained_band_replay_first_sixteen :
    DottieBandChunk 1854467118035498894 16 ⟨2,0,2⟩ :=
  dottie_band_check_rows_sound dottie_pilot_prime_ok_sound
    (rows := dottieFirstSixteenRows) (by decide +kernel)

theorem dottie_retained_band_replay_second_sixteen :
    DottieBandChunk 1854467118035498910 16 ⟨2,0,2⟩ :=
  dottie_band_check_rows_sound dottie_pilot_prime_ok_sound
    (rows := dottieSecondSixteenRows) (by decide +kernel)

theorem dottie_retained_band_replay_first_thirty_two :
    DottieBandChunk 1854467118035498894 32 ⟨4,0,4⟩ :=
  dottie_band_append_chunks dottie_retained_band_replay_first_sixteen
    dottie_retained_band_replay_second_sixteen

theorem dottie_retained_band_first_thirty_two_integer_bounds :
    DottieBandIntegerSums 1854467118035498894 1854467118035498925 4 4 :=
  dottie_band_integer_sums_of_chunk dottie_retained_band_replay_first_thirty_two
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms dottie_second_nonzero_band_prime
#print axioms dottie_retained_band_replay_first_sixteen
#print axioms dottie_retained_band_replay_second_sixteen
#print axioms dottie_retained_band_replay_first_thirty_two
#print axioms dottie_retained_band_first_thirty_two_integer_bounds

end QuarticModel
