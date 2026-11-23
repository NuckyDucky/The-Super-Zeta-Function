# The quartic certificate in the Lean kernel

I used the two ordered exponential stages to put the completed Gaussian reading and its reflection at the same Super Zeta address. This packet preserves the finite arithmetic, the argument that uses it, and the widget I used to follow the replay. The completed replay checked 7,008 certificate modules and rebuilt 95 further modules from source in Lean 4.19.0. The final audit covered 41 analytic and 13 numerical theorems. [Full replay transcript](evidence/full-replay.txt)

## From the marked orbit to the two axes

On the square launch the lifted exponents satisfy $U/V=i$. Thus $(mV+nU)/V=m+ni$ recovers the two integer marks. The fixed quartic conductor assigns a sign at that mark. I use that sign to weight the Gaussian theta sum. The primitive Gauss amplitude gives the positive theta reflection, using Peter W. Murphy’s Lean formalization of the quadratic Gauss sum and [the specialization to this conductor](../../lean-quartic-orders/QuarticConductorSign.lean).

The folded Mellin reading of the theta kernel is $G(w)$. At the original address $s=w/2$, the two Hamilton axes read $j=\Re G(w)$ and $k=-\Im G(w)$. Reflection sends $w$ to $1-\overline{w}$, preserving $j$ and reversing $k$. Hence $j^2+k^2=|G(w)|^2$ on the address chart. The positive-height measuring disk can be placed at any reference $T\ge203$, with right center $33/64+i(T-1/512)$. [Ordered axes](source/QuarticStageAxes.lean) · [Height and reflection](source/QuarticHeightAssembly.lean)

## How I checked the arithmetic in the kernel

1. **Split the signed prefix calculation.** I partitioned the lattice rows into bands. Each closed numerical check records the band’s contribution in a small Lean source module. A concatenation lemma assembles the checked equalities and proves the signed running sum is at least one at every norm index from 1 through $2^{25}$. The replay uses 6,705 numerical batches and 181 prefix assemblies. [Band composition](source/QuarticAnnulusBands.lean) · [Prefix certificate](source/QuarticCheckedShellKernel.lean)
2. **Enclose the theta kernel over intervals.** I checked rational bounds for the terms and tails of the theta sum. The 66 enclosure modules supply pointwise bounds on real intervals for the compact part of the integral. A separate estimate controls the tail. [Rational checker](source/QuarticCellChecker.lean) · [Enclosure assembly](source/QuarticCheckedCellsKernel.lean)
3. **Carry the sign through the Mellin integral.** For $w=\tfrac12+a+it$, Lean gives $\Im G(w)=at\,S(a,t)$ with $S(a,t)>400000$ on $|a|\le\tfrac1{20}$, $|t|\le\tfrac{27}{100}$. The certificate also puts every zero in that rectangle on $\Re w=\tfrac12$. The three-point check at $t=0.25$ gives readings below $-1000$, exactly zero, and above $1000$ at real parts $0.49,0.50,0.51$, with the two side readings exact negatives. [Finished theorem](source/QuarticVerifiedKernel.lean) · [Three-point Lean check](source/Smoke.lean)
4. **Replay the imports and audit the theorem.** The numerical checks use Lean kernel reduction. Checkpoint receipts record source and dependency fingerprints and the hash of the compiled object. The full replay rechecks these fingerprints, then rebuilds the rest of the proof against the same inputs. The transitive audit permits `propext`, `Classical.choice`, and `Quot.sound`. [Certificate transcript](evidence/certificate.txt) · [Audit program](source/StageAudit.lean) · [Three-point transcript](evidence/smoke.txt)

## Run the replay

Use Python 3.11 or later and elan with the Lean revision pinned in [lean-toolchain](../../lean/lean-toolchain). Populate the repository’s Mathlib cache by running `lake exe cache get` from `lean/`. For an existing cache, both drivers accept `--lake-project` with the same lockfile and `--lean` with the path of an installed Lean 4.19.0 executable. From the repository root, run the following commands.

```sh
python verification/quartic-kernel/replay_certificate.py
python verification/quartic-kernel/replay_chain.py > verification/quartic-kernel/.replay/full.log
python verification/quartic-kernel/replay_chain.py --smoke
```

The first run extracts the exact checked Lean sources from [generated-sources.zip](generated-sources.zip) after checking its [SHA-256](generated-sources.sha256). It stages sources and checkpoints under `.replay/`. A rerun resumes from matching receipts. Use `--jobs` to adjust concurrency, and start with the default single worker on a smaller machine. The first run performs the finite kernel calculations from source. The [witness generators](generators/) preserve how candidate inputs were prepared. The archived Lean sources are the replay input, so regenerating witnesses is optional.

The second script prints the `#print axioms` output after the transitive audit. `--audit-only` checks the successful certificate log against the exact sources, dependency hashes, object hashes, and axiom reports in a completed checkpoint. `--smoke` runs the small three-point import check after that audit.

[Open the verification widgets](../../widgets/quartic-progress/README.md). The archived view displays this run’s saved evidence. The live view watches a local replay.

## Next check for the Gaussian rings

The next quantitative test is a uniform positive lower bound on $j^2+k^2$ over a chosen right annulus. The mirror law then transfers the same bound to the left. For the fixed-ring field route, the coverage proposition must place each possible off-line Gaussian zero inside a tested ring or its mirror. The assembled field theorem records that localization and axis survival as hypotheses, along with the field factorization, norm-series identification, and the two other factors’ critical-line statements. [Exact field theorem and hypotheses](source/QuarticHeightAssembly.lean)
