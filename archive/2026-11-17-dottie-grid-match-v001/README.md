# Matched Dottie and grid height test

Research date 17 November 2026. This finite test links the [certified Dottie return](../2026-11-17-quartet-return-recursion-v001/README.md) to the forecast and directed counting methods from the [off-center experiment](../2026-11-17-offcenter-superzeta-v001/README.md) and [32-level screen](../2026-11-17-offcenter-screen32-v001/README.md).

## Nomination before forecasting

Use exact parameter witnesses $L_\pm=\pm x+iy$ and midpoint $L_0=iy$, with $x=4.749479070945369\times10^{-8}$ and $y=0.509892982511772$. The capped orbit has period 320 under the two-step map, so one rooted return contains 320 occurrences of each ordered arrow and 640 scalar exponential stages.

For $E_r(z)=e^{rz}$, the derivative in the log-output coordinate is $(\log E_r)'(z)=E_r'(z)/E_r(z)=r$ on any local branch. In the experiment's chart use the product of these coefficients for the 320 occurrences of one rooted arrow. Its magnitude is $|L|^{320}$. The magnitude ratio is the same for both sided witnesses and for either arrow:

$$
\delta=\log\frac{|L_\pm|^{320}}{|L_0|^{320}}
=160\log\bigl(1+(x/y)^2\bigr)>0.
$$

The ordinary full-return tangent winding is measured separately. At 384 bits the independently enclosed winding vectors $(k_P,k_Q)$ for the upper left, midpoint, and right witnesses are $(1,1)$, $(1,-1)$, and $(-1,-1)$. The lower witnesses have the opposite windings under conjugation. With the marked product ratio as the Mellin scale and scale power $c=1$, the first positive one-winding phase closure gives $T_D=2\pi/\delta$. The matched control is the nearest exact grid point $\pi n$.

| Quantity | Value |
| --- | --- |
| Dottie chart center $T_D$ | $4526119322477.94539331920732885695023$ |
| Nearest grid index $n$ | $1440708526392$ |
| Grid center $\pi n$ | $4526119322477.28394543748040426562185$ |
| Center difference $T_D-\pi n$ | $0.661447881726924591328377695144908$ |

The factor is state-independent because the exponential output cancels in the derivative ratio. The finite orbit supplies the marked witness selection, the period and the full tangent winding. The Mellin scale convention is the hypothesis under test. Forecast and contour evidence determine the behavior of zeros in the frozen boxes.

## Forecast and directed counts

Each arm uses the same interval around its center, $-1/4<\Delta T<1/4$. The broad strip is $1/16<\beta<15/16$ and the right slab is $5/8<\beta<7/8$. For each arm the finite degree-48 reference polynomial uses 848,736 dyadic cosine/Riemann–Siegel modes. Its roots and signed pairs are predictions. The frozen forecast records the broad rectangle, right slab, every positive candidate box, and the closest predicted adjacent line pair with a padded box.

The contour count uses the nonvanishing-prefactor identity for the reconstructed coupling response established in the predecessor deposit. It evaluates 144 directed complex samples per chart at 192 bits, with chart centers at offsets $-1/8$ and $+1/8$. Each chart covers half the height interval. Directed argument increments enclose the images of entire contour segments. Disjoint directed Hardy sign brackets give the corresponding lower bound for zeros on the critical line. The primary comparison is the count of windows containing a certified off-line zero.

| Arm | Forecast roots | Broad count | Disjoint line brackets | Right slab count | Windows with off-line hits | Selected pair signed square, outward decimal enclosure |
| --- | --- | --- | --- | --- | --- | --- |
| Dottie | 2 | 2 | 2 | 0 | 0 | $[-0.019772414113648,\,-0.019772412018329]$ |
| Grid | 3 | 3 | 3 | 0 | 0 | $[-0.007336024726657,\,-0.007336023450363]$ |

Both forecasts produced zero positive candidate boxes. In both arms, the disjoint line brackets account for every zero in the broad rectangle. Each preselected pair box contains two zeros at distinct critical-line heights, and both frozen signed estimates lie in their respective certified intervals. The uniform interpolation error is below $1.008\times10^{-15}$ in all four charts.

[Frozen nomination](dottie-grid-nomination.json) · [Frozen forecast and boxes](dottie-grid-forecast.json) · [Directed certificate](dottie-grid-certificate.json)

## Replay

Use Python 3.12 and the [dependency versions](../2026-11-17-offcenter-superzeta-v001/requirements.txt) from the prior off-center deposit. In a new scratch directory, copy this deposit's five research files and these four predecessor scripts:

- `dottie_multiplier_winding.py` and `verify_dottie_horn_slice.py` from `quartet-return-recursion-v001` under `computations/`.
- `offcenter_superzeta.py` and `signed_superzeta_split.py` from `offcenter-superzeta-v001`.

Run the commands below in the scratch directory. Each output name must be new.

```text
python -B dottie_grid_nomination.py nomination-replay.json
python -B dottie_grid_trial.py forecast dottie-grid-nomination.json forecast-replay.json
python -B dottie_grid_trial.py count dottie-grid-nomination.json dottie-grid-forecast.json certificate-replay.json
```

The forecast records the frozen nomination's SHA-256. The certificate records both nomination and forecast SHA-256 values. The [provenance record](provenance.json) identifies all original and predecessor source hashes.
