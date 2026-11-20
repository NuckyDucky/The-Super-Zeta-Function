# Two complex inputs for the Dottie determinant

I evaluate two principal powers of each root of $`E(v)=\cos^2\sqrt v-v`$, conjugate the second reading, multiply, and sum. This pairs a root with itself at two independently chosen complex exponents. On a single plane of such inputs I can recover the radii and arguments of the entire squared-root spectrum. In a finite test, five real values of the sum recover the first nonreal pair's radius and angle to nine decimal places in the sense of absolute error below $`10^{-9}`$. [Cosine spectrum, equations (1)–(5)](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md) · [Directed intervals and five input values](two-inputs.json)

## Which two things enter the sum?

For ordinary zeta, pairing the two convergent Dirichlet series term by term gives $`\sum_{m\ge1}m^{-x}\overline{m^{-y}}=\zeta(x+\bar y)`$ when $`\Re(x+\bar y)>1`$. The individual ordinary series both converge absolutely when $`\Re x,\Re y>1`$. This pairing is the reproducing kernel of the classical Hilbert space of Dirichlet series. Multiplying the two already-summed values would instead include the terms with two different indices as well. [Hedenmalm, Lindqvist and Seip, §2](https://arxiv.org/abs/math/9512211)

I use the same pairing rule with the actual roots of my determinant. Write $`d=\cos d`$ for the positive Dottie value, $`u_n=\xi_n+i t_n`$ for the upper-right quartet representative, and $`u_n^2=r_ne^{i\psi_n}`$, where $`r_n=|u_n|^2`$ and $`0<\psi_n=2\arg u_n<\pi`$. Here $`r_n`$ is the modulus in the squared spectral coordinate. The original quartet parameter $`L`$ has its own modulus $`R_n`$. Define

~~~math
\mathrm{Sz}_E(x,y)=\sum_{\lambda:E(\lambda)=0}
 \lambda^{-x}\overline{\lambda^{-y}},\qquad
 z=x+\bar y,\quad q=x-\bar y.
~~~

Powers use the principal logarithm at each squared root. The archived classification lists $`d^2`$ and the pairs $`u_n^2,\bar u_n^2`$, each with multiplicity one. Pairing each conjugate pair gives

~~~math
\mathrm{Sz}_E(x,y)=d^{-2z}+2\sum_{n\ge1}r_n^{-z}\cos(q\psi_n).
~~~

Since $`r_n\sim\pi^2 n^2`$ and $`\psi_n=O(\log(n)/n)`$, the ungrouped series converges absolutely exactly when $`\Re x+\Re y>1/2`$. On the diagonal this gives $`\Re x>1/4`$. At $`\Re x=1/4`$ the positive terms from each pair are asymptotic to $`2/(\pi n)`$ for fixed imaginary part. This quarter is a square-summability threshold. On $`\Re x,\Re y>1/4`$ the sum is a positive semidefinite Hermitian kernel, since every finite matrix of its values is a Gram matrix of the vectors $`(\lambda^{-x})_\lambda`$.

The coupling in the older $`\mathcal Z(s;\varepsilon)`$ changes the determinant. Here the coupling stays at one, and the second input varies the complex exponent on the same spectrum. A literal choice $`x=\zeta(z_1),\ y=\zeta(z_2)`$ is allowed wherever the resulting arguments meet the convergence condition. For instance, with $`a=\pi/6`$,
$`\mathrm{Sz}_E(\zeta(2+ia),\zeta(3-ia))\approx4.63050631-1.35736273i`$. Both input zeta series converge absolutely. In these examples $`a`$ is an additive imaginary displacement of an exponent. [Numerical inputs](two-inputs.json)

## The angular term and the Riemann reference

At $`y=0`$ the sum recovers the archived spectral zeta $`\mathcal Z(x;1)`$. At two general inputs the cosine difference identity gives

~~~math
\mathrm{Sz}_E(x,y)=\mathcal Z(z;1)+P_E(x,y),\qquad
P_E(x,y)=4\sum_{n\ge1}r_n^{-z}\sin(x\psi_n)\sin(\bar y\psi_n).
~~~

On each compact subset of $`\Re z>-1/2`$ both sines are $`O(\psi_n)`$, so the correction converges locally uniformly by comparison with $`n^{-2\Re z-2}\log^2n`$. It is holomorphic in the independent variables $`x,\bar y`$ there. On its diagonal where it converges it is nonnegative, since it is itself a sum of squared absolute values. For the reference determinant $`\cos^2\sqrt v`$, every root is positive real and this angular term vanishes identically. The original Mellin correction therefore gives the meromorphic identity

~~~math
\mathrm{Sz}_E(x,y)-P_E(x,y)-J(z;1)
 =2\pi^{-2z}(2^{2z}-1)\zeta(2z),\qquad \Re z>-1/2 .
~~~

The simple pole at $`z=1/2`$ has residue $`1/\pi`$ in the $`z`$ direction. Holding $`z`$ fixed holds the Riemann factor fixed, while the two-input left side before subtraction can still vary with $`q`$. For example $`\mathcal Z(2;1)=10/3`$ by the second trace, whereas $`\mathrm{Sz}_E(1,1)\in[3.37530321,3.37530322]`$. [Spectral reconstruction, equations (20)–(23)](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md) · [Unshifted root sum in Lean](../../lean/SuperZeta/UnitSpectrum.lean)

## A plane indexed by two imaginary displacements

Fix $`r>1/4`$ and put $`x=r+ih,\ y=r+ik`$. Both $`h`$ and $`k`$ can vary on the entire real line. Write $`\delta=h-k`$ and $`\eta=h+k`$. The two coordinates control separate parts of the same measurement:

~~~math
K_r(\delta,\eta)
=(d^2)^{-2r-i\delta}
 +2\sum_{n\ge1} r_n^{-2r}e^{-i\delta\log r_n}\cosh(\eta\psi_n).
~~~

The difference $`\delta`$ multiplies each log radius to give a phase. The sum $`\eta`$ weights each pair according to its angle. For unequal real parts $`p,t`$ the radial exponent becomes $`p+t+i\delta`$ and the angular factor is $`\cos((p-t+i\eta)\psi_n)`$. Thus opposite imaginary shifts cancel the angular dependence exactly when the real parts also agree.

| Imaginary inputs at $`r=1,\ a=\pi/6`$ | Coordinates $`(\delta,\eta)`$ | $`\mathrm{Sz}_E(x,y)`$, rounded |
| --- | --- | --- |
| $`(+a,+a)`$ | $`(0,2a)`$ | 3.398210 |
| $`(+a,-a)`$ | $`(2a,0)`$ | 2.685091 + 1.968416i |
| $`(-a,+a)`$ | $`(-2a,0)`$ | 2.685091 − 1.968416i |
| $`(-a,-a)`$ | $`(0,-2a)`$ | 3.398210 |

**Recovery from the full plane.** For fixed $`\eta`$, recover the coefficient at frequency $`\ell`$ by averaging $`K_r(\delta,\eta)e^{i\delta\ell}`$ over $`-A\le\delta\le A`$ and sending $`A\to\infty`$. Each frequency other than $`\ell`$ averages to zero. Absolute convergence, uniform in $`\delta`$ for fixed $`\eta`$, permits termwise averaging. At $`\eta=0`$ the positive coefficients identify exactly the log radii and their multiplicities. At $`\ell=\log R`$ the recovered coefficient for general $`\eta`$ is

~~~math
A_R(\eta)=R^{-2r}\sum_{|\lambda|=R}e^{\eta\arg\lambda}.
~~~

There are finitely many roots at each radius. Distinct real exponentials in $`\eta`$ are linearly independent (differentiate at zero to get a Vandermonde system). Thus the full function on this one plane determines all the **squared determinant roots with multiplicities**. For one conjugate pair at radius $`R`$, $`A_R(\eta)/A_R(0)=\cosh(\eta\psi)`$ gives its unsigned angle. The conjugate arguments are $`+\psi,-\psi`$. Taking both square roots of both values and using equation (3) of the quartet classification recovers the set of original ordered parabolic phases. Choosing a marked member of that set requires its sign or conjugation label. The squared spectrum contains no marking of a particular finite period-640 trajectory.

**Finite check on that same plane.** At $`r=1`$ the verifier uses the first radius as the frequency and withholds its angle. A triangular average with $`|\delta|\le A=524{,}288`$ multiplies the term at radius $`R'`$ by $`\mathrm{sinc}^2(\tfrac12 A\log(R/R'))`$, where $`\mathrm{sinc}(t)=\sin(t)/t`$. The gap in log radius to the other terms exceeds $`g=0.85348`$, by the real Dottie point and $`|u_n|>(n-1/2)\pi`$ for $`n\ge2`$. Their total contribution is at most $`4\sum_\lambda |\lambda|^{-2r}e^{\eta\arg\lambda}/(Ag)^2`$. The two averages at $`\eta=0,1`$ enclose the angle in [1.25796974, 1.25796978] radians. The verifier evaluates the triangular integrals termwise.

## Recovering the first nonreal pair from five full readings

For a second inverse that receives neither the radius nor the angle, write $`H_r(\eta)=K_r(0,\eta)`$ and subtract two diagonal readings:

~~~math
D_r(\eta)=H_r(\eta)-H_r(0)
=2\sum_{n\ge1} r_n^{-2r}\,[\cosh(\eta\psi_n)-1].
~~~

Every positive real root cancels. Every nonreal conjugate pair contributes a strictly positive quantity when $`\eta\ne0`$. Increasing $`r`$ reduces the weight of the higher levels. For $`r=16,17`$ the error after keeping level one lies between zero and

~~~math
2[\cosh(|\eta|\pi)-1]\,(3\pi/2)^{-4r}
 \left(1+\frac{3/2}{4r-1}\right).
~~~

Indeed all higher levels satisfy $`r_n>[\pi(n-1/2)]^2`$. Bound their sum by its first term at $`n=2`$ and the integral of the decreasing majorant from two to infinity. Let $`D_r^{(1)}(\eta)`$ be the level-one term. The certified error above isolates it, and cancellation of its common factors gives

~~~math
r_1=\sqrt{\frac{D_{16}^{(1)}(1)}{D_{17}^{(1)}(1)}},\qquad
\psi_1=\mathrm{arcosh}\left(
 \frac{D_{16}^{(1)}(2)}{2D_{16}^{(1)}(1)}-1\right).
~~~

The second formula uses $`\cosh(2t)-1=2(\cosh t-1)(\cosh t+1)`$. The inverse receives five outward-rounded **real totals** at $`(r,\eta)=(16,0),(16,1),(16,2),(17,0),(17,1)`$ and the tail formula. Their values are about $`2.53\times10^8`$ and $`8.49\times10^8`$. The smallest difference used is about $`1.20\times10^{-33}`$, so precision matters. The forward calculation uses 320-bit balls, 32 conjugate pairs and the whole remaining tail. The inverse reads only the published decimal intervals. I checked the result afterward against an independent interval evaluation of the root's polar coordinates:

| First nonreal squared pair | From five totals | Directly from the cosine equation |
| --- | --- | --- |
| Modulus $`r_1`$ | [9.458388942732, 9.458388942826] | [9.45838894281130, 9.45838894281131] |
| Angle $`\psi_1`$, radians | [1.257969768180, 1.257969768339] | [1.25796976830920, 1.25796976830921] |

The test recovers conjugate determinant roots from simulated values of this same spectrum. The full-plane uniqueness proof uses exact data at all frequencies. Finite readings have the error bounds above. [Five stored totals](two-inputs.json) · [Forward evaluation and inverse](verify_two_inputs.py)

## The corresponding two-input mean at Riemann zeros

The mean-square calculation in this deposit also permits independent displacements. With $`G(w)=(3/\pi)L(1+w,\chi_{-3})/(1-3^{-w})`$, take fixed $`\Re u,\Re v>-1/8`$ and write $`j=u+\bar v`$. Counting zeros with multiplicity, the limit of $`N(T)^{-1}\sum_{0<\Im\rho\le T}G(\rho+u)\overline{G(\rho+v)}`$ is

~~~math
C(u,v)=\frac9{\pi^2}\,
   \frac{1-3^{-3-j}}{1-3^{-1-j}}\,\zeta(3+j).
~~~

Indeed the density bound and the bounded derivatives of the two shifted absolutely convergent series let us replace the conjugate by $`G(1-\rho+\bar v)`$ at a cost tending to zero in the average. To see this, bound each difference by a shift-dependent constant times $`|\Re\rho-1/2|`$ and apply Cauchy–Schwarz and the squared-displacement estimate in the mean-square proof. In the resulting product, Landau’s formula at fixed truncation leaves only the terms with matching indices in the limit. Uniform absolute tails permit removal of the truncation. Those terms give $`(9/\pi^2)\sum a_n^2 n^{-1-j}`$, and writing $`n=3^k m`$ with $`3\nmid m`$ gives the displayed expression. The point $`u=v=0`$ recovers $`13\zeta(3)/\pi^2`$. For $`u=ia,v=-ia,a=\pi/6`$ the limit is about $`0.98518426-0.46506287i`$. This arithmetic mean depends only on the combined shift $`j`$. The original determinant retains both $`\delta`$ and $`\eta`$. [Mean-square proof, including the density and tail bounds](README.md#controlling-the-errors) · [Liu, Theorem 1.1](https://hexagonmath.org/2611.00421v1)

At the first 1,024 Riemann zeros the measured opposite-shift mean is $`0.964346-0.299738i`$ to the precision shown (rounded). The same-sign means are about $`1.453157`$ and $`1.453595`$. Both have limiting value $`13\zeta(3)/\pi^2`$. These finite calculations use the actual shifted arithmetic quotient; its modulus at an unshifted simple zero is the normalized speed. [Finite sums and limiting values](two-inputs.json)

## Verification

The proof uses the archived index classification and principal logarithms. The 320-bit verifier encloses 1,024 conjugate pairs using scalar bisection and directed endpoint signs. It checks the cosine equation, the direct principal-power products, the grouped polar form and the angular-correction identity. All four signed samples include the entire tail. For an independent check of the recovered root it proves a complex contraction for $`u+\cos u=0`$ near $`2.5+1.8i`$ using the derivative on a closed disk. The ordinary Dirichlet kernel, the limiting arithmetic formula, and an example composed with two convergent ordinary zeta values are in the same record. Lean checks conjugation, the diagonal, reduction to the archived root sum on its Mellin strip, the cosine difference and the double-shift identity used in the inversion. The convergence, uniqueness and tail estimates here have written proofs. [Lean statements](../../lean/SuperZeta/Oriented/TwoInputSpectrum.lean)

~~~sh
python -B archive/2026-11-20-hurwitz-speed-mean-square-v001/verify_two_inputs.py
~~~
