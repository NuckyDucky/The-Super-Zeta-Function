# Counting every quartet in the squared determinant

At unit coupling put $D(u)=\cos^2 u-u^2$ and define $E$ by $E(u^2)=D(u)$. The ordered exponential phases give a positive Dottie root $d=\cos d$ and a sequence $u_n=x_n+it_n$ in the upper right quadrant, indexed from one. Lean verifies that the **complete zero list** of $E$ is

$$
d^2,\qquad u_n^2,\qquad \overline{u_n^2}\qquad(n\ge1).
$$

Every entry is simple, distinct and present. In the original $u$-plane each nonreal level has the four addresses $u_n,-u_n,\bar u_n,-\bar u_n$. Squaring identifies each sign pair and preserves conjugation. These are the zeros of the cosine determinant used to build the spectral zeta. [Original cosine-spectrum manuscript, §1](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md).

## Why the enumeration is exact

For $t>0$, set $\cos\theta=-t/\sinh t$, $x=\cosh t\sin\theta$ and $H(t)=2(\theta+x)-\pi$. The inequality $t\cosh t>\sinh t$ follows by differentiating their difference, whose derivative is $t\sinh t>0$. It implies $\theta'<0$ and $1+\cosh t\cos\theta<0$. Thus

$$
H'(t)=2\{\sinh t\sin\theta+(1+\cosh t\cos\theta)\theta'\}>0.
$$

Together with the existing existence theorem, this gives exactly one positive solution of $H(t_n)=2\pi n$ per index. Conversely, for any upper-right root $x+it$ with $t>0$, the real and imaginary parts of the signed cosine equation force $x=\cosh t\sin\theta$ and $\cos(x+\theta)=0$. This recovers a positive integral level. Reflection covers the other quadrants, and the real axis contributes precisely $\pm d$. At a multiple root $D=D'=0$ would imply $\sin^2u=1$, then $u^2=\cos^2u=0$, whereas $D(0)=1$. [Lean proof of uniqueness, exhaustion and simplicity](../../lean/SuperZeta/QuartetLevels.lean).

## How this advances reconstruction

Lean verifies the entire power series for $E$, its normalization $E(0)=1$, the nonzero derivative at each zero, and the uniform bound

$$
|E(w)|\le \exp(2\sqrt{|w|})+|w|.
$$

In particular the growth order is at most one half. In the handwritten argument, Hadamard’s factorization theorem for order strictly below one gives the product over simple zeros, with a constant multiplier. Evaluating at zero fixes that constant at one. [Squared-variable Lean proof](../../lean/SuperZeta/CoupledDeterminant.lean) · [Hadamard factorization, chapter 14](https://www.utsc.utoronto.ca/people/kupers/wp-content/uploads/sites/50/2020/12/complex-analysis-2019.pdf).

For the listed roots $\lambda_j$, Lean proves that the normalized product converges at every complex argument and vanishes exactly at the listed values. On $r>0$ its value $P(r)=\prod_j(1+r/\lambda_j)$ is nonzero and its derivative is $P(r)\sum_j(r+\lambda_j)^{-1}$. The remaining Lean dependency is the general genus-zero factorization step identifying this product with $E(-r)$. The theorem `reconstruction_of_genus_zero` accepts that classical principle as an explicit argument, supplies its hypotheses from the quartet geometry, and derives, for $1/2<\Re s<1$,

$$
\sum_j\lambda_j^{-s}-J(s;1)=2\pi^{-2s}(2^{2s}-1)\zeta(2s).
$$

The public file `CoupledProduct.lean` states the exact principle and its scope. [Formal reconstruction](../../lean/SuperZeta/CoupledProduct.lean) · [Preceding verification release](../2026-11-18-binary-law-v001/README.md).

## Replay and provenance

The mathematical source is NuckyDucky’s November 16 cosine-spectrum manuscript linked above. This deposit adds the November 18 Lean port, the growth estimate and the alternative application of genus-zero factorization. From a checkout with Python 3 and elan, run the following from the repository root. The project pins Lean 4.19.0 and mathlib. The proofs quantify over all complex inputs and all positive integer levels.

~~~sh
python tools/check_lean.py --fetch-cache
python tools/verify_archive.py
~~~

The proof modules are linked above. The source checksum file identifies their Git contents together with the encompassing library, build and audit. The annotated milestone tag is `lean-quartets-v1`.
