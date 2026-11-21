# Removing the opposite-sign Gaussian primes from the Dottie circles

At the split rational prime 73, my quartic gives its two Gaussian prime ideals opposite signs. Their combined local Euler factor is $(1-73^{-2w})^{-1}$. Removing that factor changes the observed spiral phase on the right circle by between 0.007676 and 0.011138 radians. Removing the first 404 such factors together changes it by less than 0.005241 radians in absolute value there. Both bounds cover the whole circumference.

## The infinite product on the right disk

Let $\mathcal E$ consist of the split rational primes whose two Gaussian signs are opposite. Exclude primes dividing $2D$, where $D=41\cdot457\cdot1414835497$ is the norm of the character conductor. Each $p\in\mathcal E$ gives the same factor whichever ideal receives the minus sign. Put

$$
E(w)=\prod_{p\in\mathcal E}(1-p^{-2w})^{-1}.
$$

On a compact subset of $\Re w>1/2$, take $\sigma_0=\min\Re w$. The logarithm obtained by expanding each Euler factor converges absolutely and uniformly there, since

$$
\sum_{p\in\mathcal E}\sum_{k\ge1}\frac{|p^{-2kw}|}{k}
\le \frac{1}{1-2^{-2\sigma_0}}\sum_{n=2}^{\infty}n^{-2\sigma_0}<\infty.
$$

Consequently $E$ is holomorphic and nowhere zero in that half-plane. The right outer disk has center $33/64+i(T_D-1/512)$ and radius $31/2048$, so its leftmost real coordinate is $1025/2048>1/2$. Dividing the Gaussian Hecke function by the **entire** product $E$ preserves every zero and its multiplicity throughout that closed disk. This follows by division of the continued Hecke function by $E$. The full Gaussian disk count remains open.

## A Dirichlet identity for the fourth power

Let $\xi=\chi_{-4}$ and $\nu(p)=\prod_{q\mid D}(\frac{p}{q})$ at primes $p\nmid 2D$. For a split $p$ the product of the two Gaussian signs is $\nu(p)$. Thus $\mathcal E$ consists of the primes with $(\xi(p),\nu(p))=(+1,-1)$. Write $\zeta^{(S)}$ and $L^{(S)}$ for rational zeta and Dirichlet functions with the Euler factors at $S=\{p:p\mid 2D\}$ removed. [Derivation of the norm character](../2026-11-20-dedekind-phase-v001/README.md#the-conductor-and-the-sign-at-every-gaussian-integer)

$$
E(w)^4=
\frac{\zeta^{(S)}(2w)L^{(S)}(2w,\xi)}
     {L^{(S)}(2w,\nu)L^{(S)}(2w,\xi\nu)}
\,E(2w)^2.
$$

**Proof.** On $\Re w>1/2$ all products in this identity converge absolutely. At $p\in\mathcal E$, put $x=p^{-2w}$. The rational Dirichlet ratio contributes $(1+x)^2/(1-x)^2$, while $E(2w)^2$ contributes $(1-x^2)^{-2}$. Their product is $(1-x)^{-4}$. In the other three character classes both sides have factor one. This continues $E^4$ meromorphically to $\Re w>1/4$, where $E(2w)$ is holomorphic and nonzero. Thus, on the reflected disk, the possible zero or pole order of this continued fourth power is exactly the order of the displayed rational Dirichlet ratio at doubled input. On that disk the statement for $E$ itself requires a choice of a local fourth root. The replay checks the four cleared-denominator identities in $\mathbb Z[x]$.

## Spiral-phase change from the first 404 primes

For the first 404 primes in $\mathcal E$, from 17 to 13697, define the finite multiplier $M(w)=\prod_p(1-p^{-2w})$. Use the same principal lift of the period-640 multiplier as in the earlier circle experiment. With its slope $\kappa$, the change on multiplication by $M$ is, modulo $2\pi$,

$$
\Phi(M)=\Im\sum_p\log(1-p^{-2w})-\kappa\,\Re\sum_p\log(1-p^{-2w}).
$$

All individual divisors have positive real part on both disks, fixing the indicated logarithms. Each row encloses every input angle on its circle. Values are in radians and endpoints are rounded outward. [Definition of the spiral phase and the two circles](../2026-11-20-gaussian-circle-phases-v001/README.md)

| Divisors multiplied into the reading | Right circle | Reflected circle |
|---|---:|---:|
| 73 alone | $(0.007676,\ 0.011138)$ | $(0.010015,\ 0.014527)$ |
| First 404, including 73 | $(-0.005241,\ 0.003232)$ | $(-0.001353,\ 0.012468)$ |

The previous interval calculation gives clearance greater than $0.91$ radians from $3.9$ on the right at each of the 193 cutoffs. Distance on the angle circle obeys the triangle inequality, so after multiplication of each previously measured finite reading by $M$, its right-circle clearance is greater than $0.904759$ radians. This operation multiplies the existing approximant by the exact divisor. Truncating a newly sieved series at the same norm can give a different approximant. Both the finite product $M$ and its reciprocal are holomorphic and nonzero on both disks, so either normalization leaves the zero count of the full Gaussian function unchanged. Certifying its count still requires controlling that function on the boundary.

Run the [replay](replay.py) with Python 3.12 and python-flint 0.9.0 using the command below. It checks the rational norm-character criterion on every split prime through 100000, then uses 192-bit complex ball arithmetic on 256 closed arcs covering each circle. The height and character signs come from the [Gaussian arithmetic inputs](../2026-11-20-gaussian-reflected-disks-v001/gaussian_inputs.py). The slope comes from the [interval for the logarithmic lift](../2026-11-19-dottie-plane-atlas-v001/atlas/phase_lift.json).

```text
python -B replay.py
```
