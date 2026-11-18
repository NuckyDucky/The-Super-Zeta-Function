# Ordered quartet returns, coupling recursion, and the Laplace phase

Research date 17 November 2026. This continuation builds on the [16 November Super Zeta deposit](../2026-11-16-super-zeta-v001/README.md).

[Editable TeX derivation](quartet-return-phase.tex) develops the signed frequency from the difference of the two ordered fourth-order germs, constructs the coupling-response recursion at the original quartet coupling, and proves the normalized Laplace limit for heights on the square-root scale.

| Evidence | Result and scope |
| --- | --- |
| Directed native reconstruction | From the signed return jets of 2,048 quartet levels and a 72-term coupling recursion, the finite scan certified opposite endpoint signs for $2158431/65536 < T < 1079217/32768$. The predictor evaluated the reconstructed response with 192-bit ball arithmetic. The separate Hardy check refined the sign-change bracket to $32.935061587739189691 \pm 4.30\times 10^{-19}$. [Prediction record](computations/quartet-return-signed-prediction.json) |
| High-precision quadrature | The fixed-height ratio was compared with the saddle rate $r_*\approx 0.3051834619462033864$. For $j=4096$ and $T=2\sqrt j$, the numerical normalized value had real part $0.36786655825141$ and imaginary part $0.0038321376316864$, approaching the analytic limit $e^{-1}$. The finite quadrature supplies point values. |
| High-height reference calculation | The dyadic phase and classical Riemann–Siegel predictor, followed by a separate 160-bit Hardy sign check, gave a root offset relative to $n\pi$ of $0.2372010092278\pm5.59\times10^{-14}$ at level $954985468715$. The next level $954985468716$ gave $0.0088975337261\pm4.90\times10^{-14}$. These are sign-change brackets from the continued reference spectrum. [Prediction record](computations/superzeta-offset-prediction.json) |

The sign checks establish existence in the displayed brackets.

## Dottie clock test

The [clock test](computations/dottie_multiplier_winding.py) uses directed 384-bit balls on three marked attracting cycles. Each return has 640 scalar stages, or 320 ordered pairs. The calculation uses principal logs for the stage rates $L,-L$ and measures winding from both rooted phase origins. The candidate frequency is $T=2\pi|k|/(-\log|\mu|)$.

| Sample | Rooted windings $(k_P,k_Q)$ | Candidate $T$ | Directed $\lvert\zeta(1/2+iT)\rvert$, approximate |
| --- | --- | --- | --- |
| Left | $(1,1)$ | 4.2980893150163605 | 0.6462277805636235 |
| Center | $(1,-1)$ | 0.16918232071949635 | 1.388323729123826 |
| Right | $(-1,-1)$ | 4.2980893150163605 | 0.6462277805636235 |

The test certified the rooted winding histories. The modulus balls exclude zero at the candidate heights for this single-cycle scale. A connection between cycle returns and the high-height Mellin scale remains open.

## Reproduce

Copy this snapshot to a new scratch directory for replay. Use Python 3.12 and its [recorded dependencies](requirements.txt). Run the commands below from that scratch directory. The prediction commands create new files and fail if the target already exists. The check commands use the retained predictions and evaluate the Hardy function independently of the predictors.

```text
python -m pip install -r requirements.txt
python -B computations/quartet_return_recursion.py predict native-replay.json
python -B computations/quartet_return_recursion.py check computations/quartet-return-signed-prediction.json
python -B computations/laplace_return_phase.py
python -B computations/superzeta_phase_offset.py predict high-replay.json
python -B computations/superzeta_phase_offset.py check computations/superzeta-offset-prediction.json
python -B computations/dottie_multiplier_winding.py
```

[Provenance](provenance.json) identifies the nine source files and their original byte hashes. [Manifest](manifest.json) records checksums for this complete deposit.
