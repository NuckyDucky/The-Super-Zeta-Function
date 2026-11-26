# A balanced prime sum for the Gaussian quartic

I use the archived Gaussian theta to remove the short-divisor terms in Vaughan's identity. After a finite change to the Mellin weight, the terms containing higher prime powers meet the square-root error bound too. The surviving sum pairs an actual signed Gaussian Möbius coefficient with a prime weight. Both indices are within a small power of $\sqrt X$, and I can require the two indices to be coprime. [Lean identities and routes](GaussianVaughanWindow.lean) · [Independent replay and axioms](gaussian-vaughan-window-audit.txt)

## The identity with the actual coefficients

Write $B$ for the coefficients of $G$, $A$ for its Dirichlet inverse, and $L$ for the coefficients of $-G'/G$. Thus $L(p^j)=a(p^j)\log p$. Convolution gives $A*B=\mathbf1$, the unit at norm one, and $L*B=(\log)B$ with the log applied coefficientwise. For any smooth cutoffs $A_0$ in $A$ and $L_0$ in $L$, I get

$$
L=A_0*((\log)B)+L_0-A_0*B*L_0+(A-A_0)*B*(L-L_0).
$$

This is Vaughan's identity with the two archived Gaussian convolutions. Lean specializes the ring identity to the actual coefficients. [Tao, Lemma 4.11](https://arxiv.org/pdf/1201.6656) · [Gaussian log-derivative convolution](ArchivedGaussianLogDerivative.lean) · [Gaussian Möbius inverse](GaussianBalancedMoebius.lean)

## Separating the higher powers

Let $\mathcal B(z)=-G'(z)/G(z)$ and let $\mathcal P(z)=\sum_p L(p)p^{-z}$ be the prime series. Write $\mathcal E(z)$ for the part with even exponents in $\mathcal B(z)$. The actual odd weights equal the first-prime weights, including at the conductor. Therefore

$$
\mathcal B(z)-\mathcal E(z)=\sum_{j\ge1,\ j\ {\rm odd}}\mathcal P(jz).
$$

Lean checks the inverse coefficient at every $p^j$. Multiply the reading with iteration count $d$ by $\mu(d)$ and retain it only when both $d$ and $j/d$ are odd. The sum over $d\mid j$ is $a(p)$ for $j=1$ and zero otherwise. For example, at $p=5$ and $j=15$, the four terms have multipliers $1,-1,-1,1$ on the same weight $a(5)=2$. Thus the higher-power series is

$$
\Pi(z)=\mathcal B(z)-\mathcal P(z)
=\mathcal E(z)-\sum_{\substack{j\ge3\\j\ {\rm odd}}}
  \mu(j)\bigl(\mathcal B(jz)-\mathcal E(jz)\bigr).
$$

These sums may first be rearranged for $\Re z>1$ by absolute convergence. [Actual odd and even prime powers](GaussianPrimeSupport.lean) · [Lean odd inversion](GaussianVaughanWindow.lean)

For each of the four rational characters $1,\chi_{-4},\chi_D,\chi_{-4}\chi_D$, let $L_\chi^{(2D)}$ denote its $L$-function with the primes dividing $2D$ omitted, and put $\mathcal D_\chi=-{L_\chi^{(2D)}}'/{L_\chi^{(2D)}}$. The checked even weights give

$$
\mathcal E(z)=\mathcal D_1(2z)+\mathcal D_{\chi_{-4}}(2z)+
\mathcal D_{\chi_D}(2z)-\mathcal D_{\chi_{-4}\chi_D}(2z)
+\sum_{p\mid 2D}\frac{\log p}{p^{2z}-1}.
$$

The last term uses the actual weight $1$ at every even power of a prime dividing $2D$. Its denominators are nonzero for $\Re z>0$.

## A finite normalization of the weight

Fix a small $\tau>0$ and choose an integer $M$ with $M\tau>2$. In the formula for $\Pi(z)$, the sum over $j>M$ is bounded and holomorphic on closed strips in $\Re z\ge\tau$. On these iterates the Euler series are absolutely convergent. For instance, a series bounded termwise by a fixed multiple of $\Lambda(n)$ satisfies $\sum_{n\ge 2}\Lambda(n)n^{-j\tau}\ll 2^{-j\tau}$ once $j\tau\ge2$.

For each logarithmic derivative of an $L$-function at $kz$ in the finite part of this formula, use the clearing factor

$$
(1-2^{1/k-z})^2 L_\chi(kz),
$$

where $L_\chi$ means $G$ or the appropriate $L_\chi^{(2D)}$. Use each pair of function and scale only once. Write $D_M(z)$ for the product of these factors. Every scale $k$ is at least two. At a zero of an $L$-function the factor cancels the log-derivative pole. At a principal pole the log derivative times the $L$-function can have a double pole. The dyadic square cancels it. Thus $D_M$ is entire, and $D_M\Pi$ is holomorphic on a neighborhood of every fixed closed strip in $\Re z\ge\tau$. The finite part after multiplication consists of products of $L$-functions and their derivatives, with the stated principal poles removed. These and the tail have polynomial vertical bounds there.

The original weight is $H(v)=\Theta(v^7/C)$, with $\widehat H(z)=\Lambda(z/7)/7$, using the Mellin convention $\widehat H(z)=\int_0^\infty H(v)v^{z-1}\,dv$. Define $H_M$ by Mellin inversion with weight $\widehat H_M=D_M\widehat H$. On fixed vertical strips $\widehat H$ supplies exponential decay, and $D_M$ and $G$ have polynomial growth. The same growth bound holds for their derivatives by Cauchy's formula on a slightly larger strip. All three kernels with transforms
$$
\widehat H_M(z),\qquad
G(z)\widehat H_M(z),\qquad -G'(z)\widehat H_M(z)
$$
are therefore entire in the transform variable. Their inverse weights are $O_A(v^A)$ at zero and $O_A(v^{-A})$ at infinity for each $A>0$, by shifting to $\Re z=-A$ and $\Re z=A$. Call the second and third inverse weights $K_M,J_M$. On an initially rightward line, absolute convergence shows that these are obtained by summing the $B$ and $(\log)B$ factors against $H_M$. The same argument shows that the higher-power kernel $\sum_{b,c}L_{\rm pow}(b)B(c)H_M(bcv)$ has transform $\Pi(z)G(z)\widehat H_M(z)$. Shifting to $\Re z=\tau$ bounds this kernel by $O_\tau(v^{-\tau})$ for $0<v\le1$. [Original theta Mellin weight](gaussian-seventh-free.md) · [Original growth and decay calculation](gaussian-balanced-moebius.md#the-kernel-after-summing-the-third-factor)

The multiplier and its reciprocal have absolutely convergent Dirichlet series at every real exponent greater than $1/2$. The $L$-factors use $kz$ with $k\ge2$, and each inverse dyadic factor uses a convergent geometric series there. Their effect on a smoothed sum is a linear combination of earlier scales $X/n$. A square-root bound for all $\varepsilon>0$ can thus be transferred in both directions between the original and normalized sum. The sums at small $X$ satisfy the required bounds by the large-argument decay of the kernels.

## The terms that fit at square-root scale

For a target error exponent $\varepsilon>0$, take the small positive constants $\delta,\tau$ as in the Lean exponent check. I set $U=V=X^{1/2-\delta}$ and choose a smooth $W$ equal to one through $1$, zero from $2$ onward, and between zero and one. The cutoffs are $A_0(a)=A(a)W(a/U)$ and $L_0(b)=L(b)W(b/V)$.

In the smoothed sum of the four Vaughan terms, $A_0*((\log)B)$ uses $J_M(a/X)$ with $a\le2U$. The term $L_0$ uses $H_M(b/X)$ with $b\le2V$. The term $A_0*B*L_0$ uses $K_M(ab/X)$ with $ab\le4UV=4X^{1-2\delta}$. Each is $O_N(X^{-N})$ for any fixed $N>0$ by the small-argument bounds and polynomial bounds on the coefficient sums.

Write $L_{\rm pow}$ for the terms at rational prime powers of exponent at least two, and use $L_{{\rm pow},0}$ for its cutoff. The higher-power part of the remaining Vaughan term is exactly

$$
(A-A_0)*B*(L_{\rm pow}-L_{{\rm pow},0})
=L_{\rm pow}-L_{{\rm pow},0}-A_0*B*L_{\rm pow}+A_0*B*L_{{\rm pow},0}.
$$

The two short terms have arbitrary power saving as above. The first term is $O_\varepsilon(X^{1/2+\varepsilon})$ by the absolute count of prime powers and the rapid decay of $H_M$. For $A_0*B*L_{\rm pow}$, I apply the higher-power kernel bound at $v=a/X$ and $|A(a)|\le d(a)\ll_\epsilon a^\epsilon$. Summing over $a\le2U$ gives

$$
O_{\tau,\epsilon}\bigl(X^\tau U^{1-\tau+\epsilon}\bigr).
$$

The exponent without the arbitrarily small divisor bound is $(1/2-\delta)(1-\tau)+\tau$, which Lean checks is less than $1/2+\varepsilon/2$.

The remaining prime term uses $W$ on the norm $a$ and the prime $p$. The large-argument bound of $K_M$ discards $ap>X^{1+\delta}$ with arbitrary power saving by absolute summation. For $p\mid a$, write $a=pq$ and use $\sum_{p>V}X^{1+\delta}/p^2\ll X^{1+\delta}/V$. The weights cost an arbitrarily small power and the exponent before that cost is $1/2+2\delta$. Lean checks that this too is below $1/2+\varepsilon/2$.

## The signed sum to estimate

I obtain the written estimate
$$
\sum_{n\ge1}L(n)H_M(n/X)=
\sum_{\substack{a>U,\ p>V\ {\rm prime}\\ap\le X^{1+\delta},\ p\nmid a}}
A(a)L(p)(1-W(a/U))(1-W(p/V))K_M(ap/X)
+O_\varepsilon(X^{1/2+\varepsilon}).
$$

Both indices are at most $X^{1/2+2\delta}$. The signed prime arm uses $+2\log p$, $-2\log p$, or zero at the two marked Frobenius classes and the remaining primes away from the conductor. The Möbius arm uses the original inverse coefficients. [Prime signs](gaussian-prime-classes.md)

A square-root bound for these signed sums for every $\varepsilon>0$ would give the Gaussian critical-line result. The Mellin transform of the left side in the cutoff variable is $\widehat H_M(z)(-G'(z)/G(z))$ on the initial rightward half-plane. For any proposed zero $\rho$ with $\Re\rho>1/2$, choose $\varepsilon<\Re\rho-1/2$. The bound at that exponent would continue the transform for that choice of $M$ holomorphically to $\Re z>1/2+\varepsilon$. At $\rho$, $\Lambda(\rho/7)$ is nonzero by the checked reflection and the Gaussian zero-free boundary. The factor $D_M(\rho)$ is nonzero by absolute Euler convergence. The simple pole of $-G'/G$ with residue equal to minus the zero multiplicity would therefore persist. This is the same quartic field transfer used in the seventh-power calculation, with the rational Dirichlet result supplied for the two cofactors. The convolution identities, odd inversion and exponent checks are in Lean. The absolute-convergence, contour and uniform error estimates in this note are written proofs. [Nonzero numerator and field transfer](GaussianSeventhFreeMellin.lean) · [Gaussian zero-free boundary, Theorem 7.33](https://hexagonmath.org/pdf/2611.00741v1#page=66)
