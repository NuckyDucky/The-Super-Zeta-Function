# Binary traces and the relative Mellin integral

Starting from the cosine determinant of the ordered reciprocal exponential equations, this deposit verifies a law at every positive integer index and an analytic continuation in the complex spectral parameter. [Original derivation](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md) · [Original papers and numerical certificates](../2026-11-18-lean-foundations-v001/README.md)

## What the binary digits measure

Write $E_q(u^2)=\cos^2(u)-qu^2$, with $q=\varepsilon^{-2}$. Let $S_m(q)$ denote the coefficient of $z^{m-1}$ in $-E'_q(z)/E_q(z)$. The valuation $v_2(a/b)$ counts factors of two in $a$ minus those in $b$. For every $m\ge1$, with $h$ the number of ones in the binary expansion of $m$, Lean verifies

$$
v_2(S_m(1))=h,\qquad
v_2(S_m(0))=v_2(S_m(1)-S_m(0))=h-1.
$$

In fact $(2m)!S_m(1)/4^m$ is an integer congruent to $1$ modulo $4$. At $m=3$, the actual coefficient is $92/15$. Its valuation is two, and the integer is $69$. At $m=4$, the coefficient is $3538/315$, its valuation is one, and the integer is $1769$. The first snapshot recorded the valuation subject to a formal-series identity. This deposit proves that identity from the determinant and then proves the laws. [Coupled traces](../../lean/SuperZeta/BinaryLaw.lean) · [Reference and relative traces](../../lean/SuperZeta/BinaryReference.lean) · [Integer congruence](../../lean/SuperZeta/BinaryInteger.lean)

## Where Riemann zeta enters

At $q=0$ the positive squared roots are $\lambda_n=[(n+1/2)\pi]^2$, for $n=0,1,\ldots$. The determinant vanishes quadratically, with leading coefficient $1/(4\lambda_n)$. Lean sums the double spectrum for $\Re s>1/2$:

$$
2\sum_{n=0}^\infty \lambda_n^{-s}
=2\pi^{-2s}(2^{2s}-1)\zeta(2s).
$$

For real $q\ge0$, the relative determinant on the integration ray gives $K_q(x)=\log(1+q(x/\cosh x)^2)$. Its Mellin integral defines the correction $J_q$ on $\Re s<1$. Subtracting $qx^2$ at the origin gives $J_q(1)=q$. At every order $M$, subtracting the first $M$ even Taylor terms yields a holomorphic expression on $\Re s<M+1$. These expressions agree on their overlaps and define one entire function. Its value at each positive integer $m$ is $(-1)^{m+1}m$ times the coefficient of $x^{2m}$ in $K_q(x)$. [Entire continuation](../../lean/SuperZeta/MellinContinuation.lean) The reference plus correction has residue $1/\pi$ at $s=1/2$, vanishes at the nonpositive integers, and has derivative $-\log4$ at zero. These results concern this specific expression. [The Stieltjes theorem](../../lean/SuperZeta/Stieltjes.lean) proves the spectral-integral interchange for any countable sequence on the slit plane with a uniform angular margin and the stated absolute summability. Identifying this expression with the **coupled** root sum still requires the coupled determinant’s canonical product and its application on the integration ray. [Reference and Mellin integral](../../lean/SuperZeta/Reference.lean) · [First subtraction](../../lean/SuperZeta/MellinStep.lean) · [Special values](../../lean/SuperZeta/SpecialValues.lean)

## The factorial quarter and the meme quartic

The binomial factor $D_n=\pi n[4^{-n}\binom{2n}{n}]^2$ satisfies $4n(n+1)(D_{n+1}-D_n)=D_n$. Wallis’ product and a finite error interval give $\lim n(1-D_n)=1/4$. For every selection of positive roots of the quartet level equation, Lean also proves that $R_n-2\pi n\to0$ and $n(1-R_nB_n^2/2)\to1/4$. Positive level roots exist at every index. The finite Barnes product uses the sampled Gamma recurrence. [Quartet phase and radius](../../lean/SuperZeta/QuartetRadius.lean) [Factorial proof](../../lean/SuperZeta/Barnes.lean)

For the original six coefficients, Lean constructs the explicit map from the homogeneous meme quartic to the elliptic cubic. Any rational projective point would force a nonzero negative-square abscissa on that cubic. Lean constructs actual $p$-adic points at all nine primes listed in the archived discriminant factorization using Hensel’s lemma, including the prime $2$. [Local proofs](../../lean/SuperZeta/HasseLocal.lean). The four-class containment that excludes this abscissa comes from the archived arithmetic descent. [Covering proof](../../lean/SuperZeta/Hasse.lean) · [Original descent and computational record](../2026-11-18-lean-foundations-v001/arithmetic/research/hasse-obstruction.md)

### Four rational inputs cover every prime

For every prime $p$, at least one of $51/26,\ 9/5,\ 2/3,\ 2$ has a $y\in\mathbb Q_p$ with $y^2=f(x)$ on the original quartic. The first three squarefree parts are $ab,ac,bc$ with $a=5$, $b=41\cdot101$, $c=1033$. At every odd prime where $a,b,c$ are units, two have the same quadratic character. Their product is a square modulo the prime, and Hensel’s lemma lifts the square root. The explicit exceptional lifts complete the proof. [All-prime theorem](../../lean/SuperZeta/HasseCover.lean)

For the original meme approximation Lean also isolates the signed error between $2.6231439430444\times10^{-20}$ and $2.6231439430445\times10^{-20}$. [Directed proof](../../lean/SuperZeta/MemePrecision.lean)

## How to replay

From the root of a clone at the milestone revision, run

```sh
python tools/check_lean.py --fetch-cache
python tools/verify_archive.py
```

The first command builds the pinned proof library and audits the transitive axiom dependencies of every project theorem. Python 3 and [elan](https://lean-lang.org/install/) are needed. The [proof index](../../lean/README.md) identifies the declarations and their mathematical scope. The [source hashes](lean-source-sha256.json) identify the Git contents of the proof files. The [snapshot manifest](manifest.json) checks the archive files themselves. Dated November 18, 2026, this deposit extends the [foundational release](../2026-11-18-lean-foundations-v001/README.md).
