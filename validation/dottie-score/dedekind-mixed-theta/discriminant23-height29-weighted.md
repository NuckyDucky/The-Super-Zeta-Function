# A weighted Dottie disk at height 29

Take the splitting field $H$ for discriminant $-23$, the center $c=3/4+29i$, and the closed disk of radius $r=31/128$. I use the completed field reading $F$ on the larger disk of radius $\rho=63/256$. Both disks are inside the open critical strip. Lean gives $F$ at the same input as eight times the completed product of the two theta readings. [Field identification](DedekindDiscriminant23DottieReading.lean) · [Exact geometry](DedekindDiscriminant23Height29Dottie.lean)

## Enclose the completed field reading

If $Q_1(x,y)=x^2+xy+6y^2$ and $Q_2(x,y)=2x^2+xy+3y^2$, put $\alpha=2\pi/\sqrt{23}$ and evaluate the nonzero lattice points at $q=e^{-\alpha t}$. I take the sum with coefficients $1,2$ and the difference with coefficients $1,-1$. For each, integrate against $(t^{w-1}+t^{-w})/2$ on $t\ge1$. Write the two integrals as $U$ and $V$. The expression for $F$ is $8(U-3/(2w(1-w)))V^2$. [Theta forms and field formula](discriminant23-dottie.md)

Both forms satisfy $Q\ge(x^2+y^2)/2$. The number of lattice points of norm $n\ge1$ is at most $(2\sqrt{2n}+1)^2\le16n$ for each form. The absolute coefficient in either combination is at most $48n$. On the radius-$2$ disk around $c$, the folded weight has norm at most $t^2$ for $t\ge1$. Integrating $t^2e^{-\alpha n t}$ gives a bound for both tails. If $x=e^{-\alpha}$, the omitted norms above $112$ cost at most $240x^{113}/(1-x)$. If $L=e^5$ and $y=e^{-\alpha L}$, the omitted integral after $L$ costs at most $48(L^2+2L+2)y/(1-y)$. I integrate the retained polynomials on $0\le\log t\le5$ with outward Arb enclosures.

The same coefficient bound gives $|U|,|V|<240$ on the radius-$2$ disk. The pole term has norm below one there since $|\Im w|\ge27$. The integral formula is holomorphic there, and $2^{30}$ bounds its completed product. I take 128 readings on the circle of radius $1/2$, reconstruct degree $112$, and round the coefficients to a dyadic grid. If $q=\rho/2$, the Cauchy allowance is

$$
\frac{2^{30}}{1-q}\left(q^{113}+\frac{(1/4)^{128}}{1-(1/4)^{128}}\right).
$$

The interval uncertainty and the rounding allowance are added to this bound. The resulting rational model polynomial $P$ encloses $F$ with the error below. [Interval checker](check-discriminant23-height29-weighted.py) · [Exact rational polynomials](discriminant23-height29-weighted-polynomials.json)

## Check the sign around the disk

I take 49 Taylor coefficients of $-i/P$ about $c$ and round them to get $W$. If the residual $\lVert WP+i\rVert$ is small on the measuring disk, its imaginary part keeps the sign after charging the error in $P$. The replay bounds the entire residual by summing the norms of its polynomial coefficients with radius powers. The degree of the weight is $48$ and the mesh parameter is $1{,}048{,}576$ per quarter circle. The polynomial bounds give the sample inequalities on the whole circumference from the same 128 Fourier readings.

| Input | Exact bound supplied to Lean | Where it is checked |
| --- | --- | --- |
| Norm of the completed reading on radius $\rho$ | $4/10^{56}$ | Arb uniform error and exact rational model norm |
| Weighted coefficient sum on radius $\rho$ | $3\cdot10^{58}$ | `decide +kernel` |
| Norm of $F-P$ on radius $\rho$ | $2/10^{68}$ | Arb replay |
| Norm of $WP+i$ on radius $r$ | $32/125$ | Exact integer convolution and square-root ceilings |

If those bounds hold, the sign budget clears $3/5$, and Lean gives the conclusion for every $w$ in the closed measuring disk. The interval replay gives a lower margin above $0.6095$ at both tested precisions, with the same rational witness. The Lean theorem keeps the three analytic enclosure inputs explicit. [Lean theorem with exact polynomials](DedekindDiscriminant23Height29Polynomials.lean) · [Lean output and axioms](weighted-dottie-height29-replay-and-axioms.txt) · [Interval output](discriminant23-height29-interval-replay.txt)

## Check the whole disk directly

If I use the same $P$ and $W$ on the radius-$63/256$ disk, Lean checks $\|WP+i\|\le29/50$. I clear the denominator $2^{288}$ and compute the product in Gaussian integers. Each output coefficient is checked in a block of eight with `decide +kernel`. The sum of the integer square-root ceilings, weighted by the radius powers, gives the bound everywhere on the disk. [Gaussian polynomial rules](DottieGaussianPolynomial.lean) · [Exact convolution and bound](DedekindDiscriminant23Height29ExactBounds.lean)

If $h_E$ supplies $\|F-P\|\le2/10^{68}$ on that same closed disk, then

$$
\|WF+i\|
\le\|WP+i\|+\|W\|\,\|F-P\|
\le\frac{29}{50}+(3\cdot10^{58})\frac{2}{10^{68}}
\le\frac35.
$$

If $F(w)=0$, the left side is $1$. Lean gives nonvanishing of the field's Dedekind zeta at every $w$ in the radius-$63/256$ disk. The pointwise inequality removes the contour mesh. The model error $h_E$ is the one enclosure supplied by the Arb replay. Lean also checks the model norm budget from the same coefficients. [Dedekind theorem](DedekindDiscriminant23Height29ExactBounds.lean) · [Lean output and axioms](height29-exact-bounds-replay-and-axioms.txt) · [Interval output](discriminant23-height29-interval-replay.txt)

If either the base Dedekind zeta or the completed Hecke factor vanishes at $w$, then the product for $H$ vanishes at $w$. The same enclosure proves both factors nonzero on this disk. [Same-input factorization](DedekindDiscriminant23DottieReading.lean) · [Factor nonvanishing](DedekindDiscriminant23Height29ExactBounds.lean)

Run the pinned [Lean replay](README.md#replay-the-seven-eighths-proof) with `-Discriminant23Height29Dottie`. Then run [the exact-bounds replay](replay-height29-exact-bounds.ps1) with the same imports and the compiled output of that replay. Supply the import directories through `-Imports` or the current `LEAN_PATH`.

~~~powershell
$imports = @('<height-29-replay-library>', '<other-pinned-import-directories>')
& ./replay-height29-exact-bounds.ps1 -Lean '<pinned-lean-binary>' -OutputDirectory '<output>' -Imports $imports
~~~

From this directory, run the interval checker with the pinned Flint version. The optional witness argument writes the coefficients in powers of $w-c$.

```text
uv run --with python-flint==0.9.0 python check-discriminant23-height29-weighted.py
uv run --with python-flint==0.9.0 python check-discriminant23-height29-weighted.py --precision 352
```

## Check the Fourier coefficients

I keep the 128 circle readings as Gaussian integers divided by $2^{288}$. The Fourier grid has radius $1/2$ around $c$. If I enclose $\omega^{-1}$ with successive half-angle bounds and check each dyadic multiplication in the phase table, Lean gives $10^{-24}$ as an error bound for every phase. The readings have norm at most $10^{-53}$, so each Fourier coefficient pays at most $10^{-77}$ for the phase error. [Phase proof](ContourRoot128.lean) · [Fourier error theorem](ContourGaussianDFT.lean)

For the 113 retained coefficients, I check the integer dot products and then the rational differences from the saved model coefficients. The bound on the second part is $10^{-73}$. Each dot-product block runs in a separate Lean process and checks at most five coefficients. The exact arithmetic supplies `hRound`. [Sample and sum data](DedekindDiscriminant23Height29Samples.lean) · [Coefficient blocks](Height29DFTSum) · [Rounding theorem](DedekindDiscriminant23Height29DFT.lean)

## Set the reading tolerance from the signed margin

If each saved reading encloses the completed field reading to $10^{-60}$, then the Taylor tail, the reading errors, and the checked rounding errors give $\|F-P\|\le2/10^{60}$ throughout the disk. The weighted budget is $29/50+(3\cdot10^{58})(2/10^{60})=16/25$. If the field reading vanished, its weighted distance from $-i$ would be $1$. Lean gives nonvanishing of the splitting field's Dedekind zeta and both of its factors at the same input. The $10^{-60}$ reading enclosures are the remaining premise. [Outer disk and error transfer](DedekindDiscriminant23Height29CircleCertificate.lean) · [Final Lean theorem](DedekindDiscriminant23Height29DFT.lean)

Add `-CircleSamples` to the exact-bounds replay to check the outer Cauchy bound, the dyadic phases, the coefficient blocks and the final implication. Add `--circle-data <file>` to the interval replay to export the readings. At 288 and 352 bits the rational sample checksum is `3052b155f647ad48d285dbc00cd6c5e641a0cb0fc221269c9c431328ad40c5b3`. Both runs enclose every recorded reading within $1.36\cdot10^{-87}$. [Lean replay and axioms](height29-circle-reading-replay-and-axioms.txt) · [Interval replay](check-discriminant23-height29-weighted.py)

The audit records the 35 successful dependency builds and the successful replay of the final module against their compiled outputs. Each source hash identifies the exact file used for its Lean output.

## Replace the sample integrals by finite sums

At a sample $w=c+\omega^j/2$, write $A(w)=U(w)-3/(2w(1-w))$ and $B(w)=V(w)$. Then $F(w)=8A(w)B(w)^2$. If both factor enclosures fit $10^{-25}$, Lean gives the $10^{-60}$ enclosure of each field reading. The dyadic factor tables use denominator $2^{128}$. [Factor enclosure theorem](DedekindDiscriminant23Height29FactorEnclosures.lean)

I keep the nonzero lattice terms of norm at most 80 and integrate in $u=\log t$ over $[0,4]$. The same 32 panels of 24 rational nodes evaluate $U$ and $V$. Lean checks the omitted lattice terms, the integral past 4 in the log coordinate, and the quadrature error using two Cauchy radii. If $-1/4\le\Re w\le5/4$ and $|\Im w|\le30$, the total error after dividing by two is at most $2\cdot10^{-26}$ for either reading. [Truncation theorem](Discriminant23ClassMellinTruncation.lean) · [Gauss error bound](Discriminant23ClassMellinGauss.lean)

The base quadrature subtracts $3/(2w(1-w))$ at the same input. If each of the two finite sums agrees with its saved dyadic reading to $8\cdot10^{-26}$ at all 128 inputs, then Lean gives nonvanishing for the splitting field, its quadratic subfield, and the class character on the radius-$63/256$ disk. The theorem takes these finite-sum comparisons as its only enclosure premises. Both Arb runs check all 256 comparisons. [Lean theorem](DedekindDiscriminant23Height29QuadratureCertificate.lean) · [Interval output](height29-quadrature-interval-replay.txt)

Run the same Lean replay with `-FactorQuadrature` and supply the compiled circle replay through `-Imports`. Add both switches to rebuild both parts together.

~~~powershell
$imports = @('<height-29-circle-library>', '<other-pinned-import-directories>')
& ./replay-height29-exact-bounds.ps1 -Lean '<pinned-lean-binary>' -OutputDirectory '<output>' -Imports $imports -FactorQuadrature
~~~

~~~text
uv run --with python-flint==0.9.0 python check-discriminant23-height29-quadrature.py --precision 288
uv run --with python-flint==0.9.0 python check-discriminant23-height29-quadrature.py --precision 352
~~~

The replay prints the remaining premises and the transitive axioms. [Lean output and axioms](height29-quadrature-replay-and-axioms.txt)

## Use one expansion per factor

I write the finite quadrature at $w=c+d$ as a sum of $A_u e^{ud}+B_u e^{-ud}$ over the same nodes $u$. The coefficients use the weights, theta values and phases at the center $c$. If $0\le\Re c\le1$ and $|d|\le1/2$, the first 36 terms give the whole finite quadrature to $10^{-28}$. The proof sums the two exponential tails with an upper bound of 72 for the total amplitude. [Centered quadrature theorem](Discriminant23ClassMellinCentered.lean)

For $c=3/4+29i$ I save the two sets of 36 coefficients with denominator $2^{128}$. I evaluate the rounded polynomials at the rounded circle phases using Gaussian-integer Horner evaluation. The base comparison clears $w(1-w)$ before checking the integer residue for the pole. Lean checks the corresponding error when the phase goes back to its exact value. [Integer evaluation](GaussianRationalPolynomial.lean) · [Coefficient tables](DedekindDiscriminant23Height29TaylorData.lean) · [Phase and pole transfer](DedekindDiscriminant23Height29TaylorTransfer.lean)

If each of the 72 coefficient enclosures fits $10^{-27}$, the 16 integer check blocks supply both of the earlier quadrature premises at all 128 inputs. The same disk has the three nonvanishing conclusions. Both Arb runs match the saved coefficients and bound their absolute errors by $1.94\cdot10^{-39}$. [Final theorem](DedekindDiscriminant23Height29TaylorCertificate.lean) · [Interval replay](height29-centered-interval-replay.txt)

Run `-CenteredTaylor` with both compiled outputs from `-CircleSamples` and `-FactorQuadrature` in `-Imports`. The same script accepts all three switches together.

~~~powershell
$imports = @('<height-29-factor-library>', '<height-29-circle-library>', '<other-pinned-import-directories>')
& ./replay-height29-exact-bounds.ps1 -Lean '<pinned-lean-binary>' -OutputDirectory '<output>' -Imports $imports -CenteredTaylor
~~~

~~~text
uv run --with python-flint==0.9.0 python check-discriminant23-height29-quadrature.py --taylor-table DedekindDiscriminant23Height29TaylorData.lean --precision 288
uv run --with python-flint==0.9.0 python check-discriminant23-height29-quadrature.py --taylor-table DedekindDiscriminant23Height29TaylorData.lean --precision 352
~~~

The replay prints the two remaining coefficient bounds and their axiom audit. [Lean output and axioms](height29-centered-replay-and-axioms.txt)

## Keep the quadrature error while increasing height

If I take an integer panel count $P\ge32$ with $|\Im w|\le P-2$, then I can use the same 24 Gauss nodes on each panel of width $4/P$. The two Cauchy radii are $16/P$ and $4/P$. The outer Taylor ratio stays at $1/8$ and the inner ratio at $1/2$, with exponential bounds $24e^{17}$ and $24e^5$. If $-1/4\le\Re w\le5/4$ and the class combination has $|b|\le2$, then the normalized quadrature differs from the complete reading by at most $2/10^{26}$. The replay checks this for every $P$ in that range. [Lean theorem](Discriminant23ClassMellinGauss.lean) · [Exact statement and axioms](height-scaled-gauss-lean-audit.txt)

## Check the 72 coefficient enclosures in Lean

For a gauss node $u=A/D$, I use the integer quotient $\lfloor 2^{256} A^k/(D^k k!)\rfloor$ to represent $u^k/k!$ on a dyadic grid. If I use this one division for each node and degree, then Lean gives an error at most $2/10^{45}$ per moment. I check the 24 initial phase triples and the common panel step, then check the phase, heat, theta and positive exponential values at all 768 nodes. [Moment proof](Discriminant23GaussMoments.lean) · [Checks on the node table](Height29IntegerTrace/TraceChecked.lean)

If I sum the node products for either class combination, then Lean gives an error at most $2/10^{28}$ against the exact Taylor coefficient of the finite quadrature. If the resulting Gaussian integer numerator matches the saved coefficient to $1/10^{28}$ after scaling to the same denominator, then the combined error is at most $3/10^{28}$. All 72 checks for degrees 0 through 35 pass with `decide +kernel`. [Coefficient error](Discriminant23GaussCoefficientError.lean) · [Integer comparisons](Height29IntegerTrace/CoefficientsChecked.lean)

If $|w-(3/4+29i)|\le63/256$, Lean gives nonvanishing at $w$ for both completed Dedekind readings and the class-character reading. The theorem takes disk membership as its only hypothesis. Its transitive axioms are `propext`, `Classical.choice` and `Quot.sound`. [Lean theorem](DedekindDiscriminant23Height29KernelCertificate.lean) · [Exact statement and replay audit](height29-kernel-replay-and-axioms.txt)

Add `-IntegerCoefficients` to the replay. If the earlier replays already have compiled output directories, pass them in `-Imports`. The switches can also run together in a single output directory.

~~~powershell
& ./replay-height29-exact-bounds.ps1 -Lean '<pinned-lean-binary>' -OutputDirectory '<output>' -Imports $imports -CircleSamples -FactorQuadrature -CenteredTaylor -IntegerCoefficients
~~~
