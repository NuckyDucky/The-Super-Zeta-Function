# Dottie quartic verification

I propose analysis for the **Extended Riemann Hypothesis for Dedekind zeta functions** through a series of techniques I outline in this github. The technique I refer to is 'tetrational lift', and I will also use a mathematical object called the Dottie spire (a tower that arises from this technique), and the Super Zeta spectrum, the formalization of extending our 'tetrational lift' technique to the complex plane with the the ordered pairing $(P,Q)\mapsto(e^{LQ},e^{-LP})$. This gives the two phases and the Dottie spire directly.

The spire supplies the height-selection rule through the marked orbit's return and winding. The measuring-circle theorem can be placed at a reference height $T\ge203$. By choosing a marked Dottie orbit, giving the specific height used in the archived tests, and then counting all the zeros of the ordinary zeta function in that rectangle, we can show there can be no off-line zeros in that rectangle. The two zeros counted there are both on the critical line. This can be rinsed and repeated to illustrate our conjecture. [Height selection](../../archive/2026-11-17-dottie-grid-match-v001/README.md#nomination-before-forecasting) · [Full-strip count](../../archive/2026-11-17-dottie-local-strip-v001/README.md#full-strip-corollary)

The proof strategy starts with a hypothetical zero and follows the **same complex input** into a Gaussian reading, specifically using two reflected Gaussian rings and carrying the input through our Super Zeta spectral construction. The Super Zeta function currently is the summation of the inverse powers of the squared cosine roots. This technique was useful because our next section has Lean proving that signed bounds on the measuring circle force the Gaussian reading to be nonzero on both reflected Dottie rings. [Signed ring theorem](../../lean-ideal73/ArchivedQuarticSpectralAddress.lean#L80)

Writing the quaternions as $Q_{\rm H}=a+bj$, with $a$ the completed Gaussian reading and $b$ the other slot, $iQ_{\rm H}j-jQ_{\rm H}i$ gives $\Im b$ and $\Re a$. The $jQ_{\rm H}k-kQ_{\rm H}j$ comparison reads both coordinates of $a$. Lean proves that adding ink, or what I call 'painting' in the $j,k$ slot, or specifically on that slice of our zeta domain that's mapped to the spectral zeta function, *still* leaves that second difference intact! The Super Zeta chart gives us a *reversible* way to work backwards through the Super Zeta construction. If we assume an ordinary zeta zero at $w$, our corrected Super Zeta reflects that at $s=w/2$. [Painting](../../lean-ideal73/ArchivedQuarticOrders.lean#L36) · [The address chart](../../lean-ideal73/SuperZeta/QuarterLine/QuarticTurn.lean#L79) · [Zero correspondence](../../lean/SuperZeta/UnitSpectrum.lean#L56)

The archived forced-Gaussian-zero theorem then says exactly what must happen at the original point and its mirror section on the Gaussian rings. Both Gaussian axes go to zero, so a certified surviving axis contradicts that. Murphy’s primitive Gauss-sum work supplies the $+1$ sign used to relate the two reflected readings. The field theorem then uses that exclusion at our recovered input after the ordinary zeta and beta factors are ruled out there. The low-height certificate puts every Gaussian zero in its specified rectangle on the critical line. The two high Dottie rings are our hunting ground. [Gauss sign and reflection](../../lean-ideal73/QuarticConductorSign.lean#L34) · [Field zero at the recovered input](../../lean-ideal73/ArchivedQuarticSpectralAddress.lean#L57) · [Low-height certificate](../quartic-kernel/source/QuarticVerifiedKernel.lean#L23)

## Lean verification records

These records use Lean 4.33.1 and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The [Lean package](../../lean-ideal73/README.md#the-exact-dottie-quartic-and-the-signed-ring-test) contains the sources and reproduction commands.

- [Quartic and smoothed contour proof](quartic-contour-replay.txt) rebuilt 68 project modules.
- [Gamma phase](reference-phase-replay.txt) rebuilt the five modules involved in the phase enclosure.
- [Reference projection](reference-bridge.txt) assembled the reference proof against those two replays.
- [Signed moments](signed-moments.txt) checked the exact Taylor error and absolute mass bounds.
- [Chart replay](chart-replay.txt) accepted all 43 modules of the original Super Zeta chart on the quartic toolchain.
- [Spectral bridge](spectral-bridge.txt) checked the original address, zero test, and Hamilton order implications.
- [Rational reference](rational-reference.txt) checked the sharper lattice-mass bound, the completed phase, the perturbation to a rational height, the conditional positivity test, and the integer log enclosures.
- [Integer reference score](integer-reference-score.txt) checked the rational phase reduction, Taylor cosine enclosure, integer reciprocal square root, exact signed lattice character, and the implication from the score inequality to positivity.
- [Score block replay](score-block-replay.txt) checked fixed-denominator phase reduction, exact row partition and recombination, and the first 1,024-point block.
- [Cached log evaluator](cached-log-score.txt) checked the lookup and eight-term residual, the per-weight error, and the original positivity implication.
- [First complete reference row](first-reference-row.txt) checked all 17 blocks and their exact sum.
- [Paired Gaussian score](paired-reference-score.txt) checked the swapped-coordinate sum, its batch decomposition, and its positivity implication.
- [Paired row spans](paired-row-span.txt) checked contiguous span assembly and the exact sum of the first 32 paired rows.
- [Signed Dottie budgets](signed-dottie-budgets.txt) audited the exact signed norm partition, range contour identity, retained and omitted margin implications, uniform sharp moments, Gamma ratio, and signed patch transfer.
- [Signed block variation](signed-block-variation.txt) checked both Gaussian signed partial-summation transfer estimates for complex displacement and the log-weighted derivative.
- [Omitted sharp block and reference candidate](omitted-sharp-and-candidate.txt) checked the exact block, the whole-circle anchor error, even norm reuse, the candidate integer margin, and row 11,000 of the actual certificate.
- [Candidate checkpoint receipt](full-paired-checkpoint-receipt.json) records the ordered coverage, SHA-256, and integer total for all 16,638 rows. The equality of the complete candidate to the Lean row-span sum remains an explicit input.
- [Lookup and horizontal slope](lookup-and-horizontal-slope.txt) checked the exact sign equivalences, the original block score, and the derivative implication for the exact Dottie ring.
- [Paired sign timings](paired-sign-timing.txt) record a same-process 256-position profile and the replay of row 11,000 using the original and lookup evaluators.
- [Packed witnesses and sharp derivative](packed-witness-and-sharp-derivative.txt) checked modular sign witnesses, exact packed block certification and the derivative estimate for the original sharp block.
- [Packed witness timings](packed-witness-timing.txt) record the same 256 positions, the rejection of a corrupted root, and the full row 11,000 replay.
- [Horizontal derivative](horizontal-derivative.txt) checks the pointwise contour derivative, a uniform integrable majorant, differentiation under the integral, and the exact signed-derivative implication for the ring.
- [Far contour shift](far-contour-shift.txt) checks the exact shifted expression for the far omitted block and proves a linear unsigned Gaussian coefficient count.
- [Absolute far bound](far-absolute-bound.txt) checks the weighted Gaussian coefficient count, the central and outer Gamma bounds, the scalar norm bound, and the lower bound for the reference Gamma ratio.
- [Lower smoothing and reference](lower-smoothing-budgets.txt) checks the exact rectangle, its four edge bounds, the prefix and lower omitted smoothing budgets, and the relative far budget from the exact row equality.
- [Retained band and tail split](retained-band-tail-budget.txt) checks the exact finite bands, the absolute infinite-tail bound, and the revised sufficient finite-band budget.
- [Signed finite-band variation](retained-band-variation.txt) checks the Abel bound, one-step bound for the original contour polynomial, and exact phase-length constants for its three intervals.
- [Integrated retained bands](retained-band-integration.txt) checks the original core and tail integrals, the conditional ring assembly, the coefficient zero checker, and the first eight actual zero coefficients.
- [First checked band chunk](retained-band-first-chunk.txt) checks the Lucas witness, the split prime-power formula and the actual 16-slot integer sum certificate.
- [Retained band batch replay](retained-band-chunk-replay.txt) checks the generic factor and prefix replay, the first 32 and 256 norms, and all 4,096 norms of the first archived short band. The single-worker short-band build took 44.003 seconds and peaked at 6,826.5 MiB of sampled private memory.
- [All short bands and the relative circle](retained-short-bands-relative-circle.txt) gives the remaining short-band certificates and the exact relative Gamma and sharp-circle transport. The second and third short bands took 40.702 and 45.412 seconds on one worker.
- [Transitive axiom audit](transitive-audit.txt) checked 249 named declarations in the package audit.

The numerical signed bounds appear as explicit hypotheses of the two ring implications. The clean transcripts capture the original module-by-module runs. The packaged sources preserve the Lean declarations and place the five adapted Murphy files alongside a copy of their upstream license and notice.

## Dottie flank interval and first complete retained band

- [Height and variation checks](flank-window-and-first-long-band.txt) include the exact half-unit height image of the archived one-winding calibration, its disk coverage, and the signed partial-sum bound for a pure vertical shift.
- [The directed flank replay](../../tools/dottie-compute-pilot/replay_dottie_flank_window.py) takes the archived quartet computation folder as its argument. It checks cap capture, primitive period and winding on both flanks and for both phase origins with 384-bit balls.
- [The assembly receipt](DottieLongBand1Assembly-receipt.json) records all 32 checked blocks of the first retained long band. The [join source](../../tools/dottie-compute-pilot/DottieQuarterCombinedCertificate.lean) imports that generated assembly and proves the integer bound for 135,168 rows after adjoining its checked short band. Its axiom output is in the checks linked above.
- [Sharp-circle scalar audit](sharp-circle-scalar-caps.txt) checks gap-free coverage of one turn and the rational inequalities on 2,077 arcs using `decide +kernel`. The margin theorem takes the actual reference projection and the model enclosures as premises.

## Second retained band and moment precision

- [The second assembly receipt](DottieLongBand2Assembly-receipt.json) records all 64 kernel batches covering 262,144 rows. The [join source](../../tools/dottie-compute-pilot/DottieHalfCombinedCertificate.lean) combines them with the adjacent short block to obtain the exact integer sum bound on 266,240 rows.
- [Lean axiom output](second-long-band-and-precise-height.txt) includes the joined band, a Dottie height enclosure of width $10^{-19}$, the 96-bit logarithm enclosure through the full sharp cutoff, and the small-error affine exponent for the relative Gamma factor on both reflected addresses.
- The same axiom report records the reflected Horner identity, signed fixed-point rectangles, high-order moment bounds from absolute mass, and rational phase reduction at the sharp cutoff.

## Sharp derivative transport and third retained band

- My local Lean 4.33.1 replay checked `dottie_completed_derivative_transport_error`, which uses both signed anchor sums, and `dottie_shorter_derivative_im_le_of_sharp_anchor`, which combines the sharp transport estimate with the signed smooth derivative. `dottie_grid_centered_log_error_ratio` bounds the centered-log error coefficient on each of the 64 cells by less than $1/150$ of its previous value. The source and matching replay transcript are verified locally. All six audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- At this checkpoint I checked eight consecutive 4,096-norm blocks of the third retained long band locally, covering 32,768 of its 524,288 norms.
- The signed omitted budget through $8\times10^{24}$ still needs the numerical signed sharp-anchor and smooth-derivative enclosures, together with bounds on the signed prefix sums used in the transport error.

## Affine derivative bounds and the next third-band checkpoint

- My local Lean replay uses Cauchy’s estimate on radius $1/125$ inside the checked radius-$1/25$ disk. `dottie_sharp_relative_derivative_sub_affine` bounds the derivative error by $2250/10^{12}$ for $|w-z_0|\le 1/32$. `dottie_sharp_logarithmic_slope_error_on_segment` bounds the slope error after subtracting $\log h$ by $28/10^9$ on the reflected horizontal segment. `dottie_sharp_signed_anchor_sub_affine` gives error at most $(2250/10^{12})|B|+(18/10^{12})|\log(h)B+C|$ in relative units. The source and transcript were verified locally. All five declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- The next local checkpoint covers the first 16 consecutive blocks of the third retained long band, or 65,536 of its 524,288 norms. The source and compiled-object hashes match all 16 receipts.
- The numerical signed anchor and smooth derivative enclosures remain inputs to the omitted bound.
