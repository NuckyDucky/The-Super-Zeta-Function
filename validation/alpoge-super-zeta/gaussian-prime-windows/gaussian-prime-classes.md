# The two Gaussian prime signs and the normalized window bound

For the actual quartic, put $k=\mathbb Q(i)$, $\delta=-5045155+1027708i$, and $K=k(\sqrt\delta)$. Write $D=N_{k/\mathbb Q}(\delta)=26509772707289$. The normal closure $L=k(\sqrt\delta,\sqrt{\bar\delta})$ has degree eight over $\mathbb Q$. Away from $2D$, its maximal abelian subfield $A=\mathbb Q(i,\sqrt D)$ determines where the first Gaussian prime weight is nonzero. Two different Frobenius classes of $L$ measure the two signs among those contributing primes. [Original quartic and Gaussian Euler factors](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/docs/proofs/gaussian-ideals-and-super-zeta.md)

## What the rational characters measure

Write $a(p)$ for the first Gaussian weight in the logarithmic derivative of the archived factor $G$. For $p\nmid2D$, Lean proves

$$
a(p)^2=(1+\chi_{-4}(p))(1+\chi_D(p)).
$$

Here $\chi_D(p)=(D/p)$. At a prime splitting over $k$, the two marked signs are the quadratic characters of the two reductions of $\delta$. Their product is $(D/p)$ and their sum is $a(p)$. At $p=5$ both signs are $+1$. At $p=13$ both are $-1$. Their rational character pairs are identical. At norm $73$, the ordered conjugate Gaussian generators have opposite signs. Lean supplies a same-norm conjugate pair with opposite signs away from the prime factors of any prescribed nonzero rational modulus. [Prime weight, support and examples](GaussianPrimeSupport.lean) · [Conjugate-pair theorem](GaussianNormOrientation.lean)

## Which Frobenius classes carry the signs

The three possible nontrivial products of $\delta,\bar\delta$ have nonsquare classes in $k$. Each of $\delta,\bar\delta$ has nonsquare rational norm $D=41\cdot457\cdot1414835497$. If $(u+iv)^2=D$ with $u,v\in\mathbb Q$, then $uv=0$. Positivity of $D$ forces $v=0$, leaving the impossible rational square $u^2=D$. In particular the two quadratic extensions over $k$ are distinct and independent. Their compositum $L$ is stable under complex conjugation and is Galois over $\mathbb Q$.

Let $\sigma,\tau$ flip $\sqrt\delta,\sqrt{\bar\delta}$ separately. Complex conjugation exchanges the two flips. It follows that the Galois group is dihedral of order eight. Its commutator subgroup is $\{1,z\}$ with $z=\sigma\tau$. Indeed, $z$ is the commutator of conjugation and $\sigma$, and the quotient by $z$ is abelian. This subgroup fixes $i$ and $\sqrt\delta\sqrt{\bar\delta}$, whose square is $D$. The fixed field therefore equals $A$ by degree.

At an unramified prime split in $k$, the $\sigma,\tau$ bits of Frobenius give the signs on the two square roots. This is the finite-field quadratic character test used by the archived Euler-factor comparison. The identity class gives $a(p)=2$. The central class $z$ gives $a(p)=-2$. The single-flip elements $\sigma,\tau$ give $a(p)=0$, as do rational primes inert in $k$. Chebotarev gives density $1/8$ to each of the two nonzero signs among rational primes. [Chebotarev and splitting, Section 1](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf#page=2)

For any positive integer $m$, let $C=\mathbb Q(\zeta_m)$. The subfield $L\cap C$ is abelian over $\mathbb Q$, so $z$ fixes it. In $\operatorname{Gal}(LC/\mathbb Q)$ there is an automorphism restricting to $z$ on $L$ and to $1$ on $C$. To see this, the restriction of $\operatorname{Gal}(LC/C)$ to $L$ has fixed field $L\cap C$, so its image is $\operatorname{Gal}(L/L\cap C)$. Both this lift of $z$ and the identity are central, since the map to the product of the two Galois groups is injective. Chebotarev therefore gives infinitely many primes $p\equiv1\bmod m$ of **each** sign. No fixed rational congruence modulus recovers the signed prime weights. [Frobenius in cyclotomic fields and singleton classes](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf#page=2)

## The exact signed estimate to carry over

Exclude a finite set $B$ containing the prime factors of $2D$ and the primes ramified in $L$. Let $\Theta_+(x)$ and $\Theta_-(x)$ be the sums of $\log p$ over $p\le x$ outside $B$ in the classes $1,z$ respectively. Define the two centered, smoothed prime counts by

$$
R_\pm(x)=\sum_{\substack{p\le x,\ p\notin B\\a(p)=\pm2}}
(\log p)(1/p-1/x)-\tfrac18\log x-d_\pm,\qquad
d_\pm=\int_1^\infty\frac{\Theta_\pm(t)-t/8}{t^2}\,dt.
$$

For this fixed field, the unconditional effective Chebotarev theorem gives $\Theta_\pm(t)-t/8=O(t e^{-c\sqrt{\log t}})$ for some $c>0$ by partial summation. A possible real exceptional zero has fixed exponent less than 1 and can be included in this bound after decreasing $c$. The integrals converge absolutely, and a finite partial summation gives $R_\pm(x)=-\int_x^\infty(\Theta_\pm(t)-t/8)t^{-2}dt$. [Lagarias and Odlyzko, Theorem 1.3](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf#page=3)

To identify the centering of the Lean window, write $b(p)=a(p)\log p$ and $P(t)=\sum_{p\le t} b(p)$, including the finitely many exceptional primes. Its normalized Gaussian error $E_G(x)$ is

$$
E_G(x)=c_G+Q+\int_1^x \frac{P(t)}{t^2}\,dt,\qquad
c_G=\operatorname{Re}\frac{G'(1)}{G(1)},\qquad
Q=\sum_{p,j\ge2}\frac{a(p^j)\log p}{p^j}.
$$

For real $\sigma>1$ the exact logarithmic derivative equals $-G'(\sigma)/G(\sigma)=\sum_p b(p)p^{-\sigma}+\sum_{p,j\ge2}a(p^j)(\log p)p^{-j\sigma}$. The prime part is $\sigma\int_1^\infty P(t)t^{-\sigma-1}dt$. The bound above dominates this integral as $\sigma\downarrow1$, and the higher powers converge absolutely at 1. Since $G(1)\ne0$, this gives $c_G+Q+\int_1^\infty P(t)t^{-2}dt=0$. For $x$ beyond $B$ we get the exact identity

$$
E_G(x)=2R_+(x)-2R_-(x)-\frac1x\sum_{p\in B} b(p).
$$

[Lean logarithmic derivative and Gaussian factor at one](ArchivedGaussianLogDerivative.lean) · [Lean normalization and higher-power correction](GaussianPrimeOnlyWindow.lean)

The sum $\Theta_+(x)+\Theta_-(x)$ counts rational primes splitting completely in $A$ up to the finite exclusions. The Dedekind zeta of this biquadratic field is the product of the ordinary zeta and the three Dirichlet factors for $\chi_{-4},\chi_D,\chi_{-4}\chi_D$. Applying Dirichlet GRH to these factors supplies the hypothesis of effective Chebotarev for $A$. Theorem 1.1 and partial summation give $\Theta_++\Theta_-=x/4+O(\sqrt{x}\log^2 x)$. In particular,

$$
R_+(x)+R_-(x)=O(x^{-1/2}\log^2 x),\qquad
E_G(x)=4R_+(x)+O(x^{-1/2}\log^2 x).
$$

For every $\theta>1/2$ the last error is bounded in absolute value by a constant times $x^{\theta-1}$. So the original cofinal-window upper bound is equivalent, with the Dirichlet input supplied, to an upper bound of that order for $R_+$ on the same family of windows. This specifies a single Frobenius class for the arithmetic step. Sernau's smoothed count uses the same kernel $1/p-1/x$, applied to non-split primes with a rational residue-class weight. Our target for an **upper** bound counts the completely split primes of $L$. [Dirichlet GRH verification](https://math.mit.edu/~drew/shortgrh/) · [Lagarias and Odlyzko, Theorem 1.1](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf#page=3) · [Sernau’s normalization](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/PrimeError.lean#L23)

The Frobenius and prime-counting arguments above use classical theorems. The Lean audits cover the exact prime weights, the two rational character values, the conjugate norm obstruction, and the earlier normalized window reduction. [Prime support audit](GaussianPrimeSupport-audit.txt) · [Norm orientation audit](GaussianNormOrientation-audit.txt)
