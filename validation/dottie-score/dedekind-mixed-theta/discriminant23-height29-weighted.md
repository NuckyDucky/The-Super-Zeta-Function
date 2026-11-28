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

Run the pinned [Lean replay](README.md#replay-the-seven-eighths-proof) with `-Discriminant23Height29Dottie`. From this directory, run the interval checker with the pinned Flint version. The optional witness argument writes the coefficients in powers of $w-c$.

```text
uv run --with python-flint==0.9.0 python check-discriminant23-height29-weighted.py
uv run --with python-flint==0.9.0 python check-discriminant23-height29-weighted.py --precision 352
```
