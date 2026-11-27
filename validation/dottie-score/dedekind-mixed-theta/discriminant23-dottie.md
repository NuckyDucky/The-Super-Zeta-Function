# First Dottie disk for the discriminant-23 class product

Let $L$ be the splitting field of $X^3-X-1$ over $\mathbb Q$. Lean proves that the cubic is irreducible and that $\mathrm{Gal}(L/\mathbb Q)\simeq S_3$. Inside $L$, the product of the differences of the three roots has square $-23$. Lean identifies the resulting subfield with $F=\mathbb Q(\sqrt{-23})$ and proves that $L/F$ is cyclic of degree three. [Splitting field](DedekindDiscriminant23Field.lean) · [Quadratic subfield](DedekindDiscriminant23Quadratic.lean)

Classically, $L$ is the Hilbert class field of $F$. The three ideal classes have forms $Q_0(m,n)=m^2+mn+6n^2$ and $Q_{\pm}(m,n)=2m^2\pm mn+3n^2$. Changing the sign of $m$ matches the two nonprincipal theta sums. The two nontrivial class characters therefore have the same completed reading. Their sum of weights on the nonprincipal classes is $-1$ for each character. [Splitting field and class character](https://orbilu.uni.lu/bitstream/10993/51645/1/OnSerreJordan-7.pdf) · [Zagier's discriminant-23 example](https://www.its.caltech.edu/~matilde/Zagier123ModularForms.pdf#page=42)

## The reading on the disk

Put $\alpha=2\pi/\sqrt{23}$ and $q(t)=\exp(-\alpha(1+t))$. The sums below omit the origin, and $Q_1=Q_+$.

$$
\Theta_j(t)=\sum_{(m,n)\ne(0,0)} q(t)^{Q_j(m,n)},\qquad
U(t)=\Theta_0(t)+2\Theta_1(t),\qquad D(t)=\Theta_0(t)-\Theta_1(t).
$$

Write $v=\log(1+t)$ and $M_w(t)=(e^{(w-1)v}+e^{-wv})/2$. The folded Mellin readings and their product are

$$
A(w)=\int_0^\infty U(t)M_w(t)\,dt,\qquad
C(w)=\int_0^\infty D(t)M_w(t)\,dt,\qquad
P(w)=\left(A(w)-\frac{3}{2w(1-w)}\right)C(w)^2 .
$$

The height parameter $T=1/512$ and scale index $n=0$ give the closed disk $|w-3/4|\le31/128$. For every point in this disk, Lean proves

$$
\operatorname{Re} P(w)\le -1/400,\qquad P(w)\ne0 .
$$

The contour rotation is multiplication by $i$, so the imaginary part of the rotated reading has the same ceiling. The estimate covers the boundary and interior with one proof. [Disk theorem](Discriminant23DottieDisk.lean) · [Lean output and axiom audit](discriminant23-replay-and-axioms.txt)

## The exact bounds

- For $0\le q\le3/11$, Lean proves $2q\le\Theta_0\le(21/10)q$ and $0\le\Theta_1\le(3/4)q$. The two principal terms at $(1,0)$ and $(-1,0)$ give the lower bound. The upper bounds use the exact sum over $|m|,|n|\le4$ with the origin omitted. For the rest, $m^2+n^2\le 2Q_j(m,n)$ gives the geometric bound $(440/3)(3/5)^{25}$ on the sum after removing one power of $q$. The two finite rational inequalities are checked with `decide +kernel`. [Lattice and theta bounds](Discriminant23ThetaEnvelope.lean)
- The scale satisfies $13/10\le\alpha\le4/3$ and $1/4\le e^{-\alpha}\le3/11$. Combining these inequalities with the lattice bounds gives $0\le U(t)\le(54/55)e^{-13t/10}$ and $(5/16)e^{-4t/3}\le D(t)\le(63/110)e^{-13t/10}$. [Exponential majorants](Discriminant23DottieDisk.lean)
- For $1/2\le\operatorname{Re}w\le1$ and $|\operatorname{Im}w|\le1/4$, the folded weight has norm at most $1$. Its real part is bounded below by $e^{-v/2}-(\operatorname{Im}w)^2v^2/2$, and its imaginary part has magnitude at most $|\operatorname{Im}w|(\operatorname{Re}w-1/2)v^2$. Lean uses $v^2\le(5/7)t$ and integrates the exponential majorants. This gives $|A(w)|\le4/5$, $\operatorname{Re}C(w)\ge1/8$, and $|\operatorname{Im}C(w)|\le|\operatorname{Im}w|(\operatorname{Re}w-1/2)/4$. [Integral bounds](DottieClassMellinBounds.lean)
- These three inequalities imply the ceiling on $P(w)$. Lean applies them on the actual Dottie disk using its center, radius, and strip containment. [Product sign](DottieCompletedProductSign.lean)

## Handoff to the field reading

With $(2\pi)^{-w}\Gamma(w)$ per complex place, the classical completed product for $L$ is $P(w)$. Poisson summation folds the three class sums. The trivial class character gives $A(w)-3/(2w(1-w))$, and each nontrivial class character gives $C(w)$. The relative extension is unramified and $L$ has three complex places, so the library convention with $2(2\pi)^{-w}\Gamma(w)$ per complex place introduces a factor of $8$. [Class product and character](https://orbilu.uni.lu/bitstream/10993/51645/1/OnSerreJordan-7.pdf) · [Lean Gamma convention](https://github.com/leanprover-community/mathlib4/blob/0493595ecd5da8ef14742febab99728f98e948e8/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean#L53)

Lean proves that `mixedThetaCompletedReading Discriminant23GaloisField w` equals `8 * discriminant23CompletedClassProduct w` throughout the open strip. The real part of the field reading is at most $-1/50$ throughout the closed disk, and the continued Dedekind zeta is nonzero there. [Same-input identity](DedekindDiscriminant23DottieReading.lean) · [Continuation and replay](discriminant23-dottie-field-reading.md)

## Replay

Use the pinned AxiomMath checkout and Lean 4.35.0-rc3 described in the [archive README](README.md).

~~~powershell
pwsh ./validation/dottie-score/dedekind-mixed-theta/replay-discriminant23.ps1 `
  -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin>
~~~
