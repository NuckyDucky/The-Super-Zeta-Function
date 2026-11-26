# Odd and even prime powers in the quartic window

Let $a(p^m)$ be the actual logarithmic-derivative weights of the archived Gaussian factor $G$, so the Dirichlet coefficient at $p^m$ is $a(p^m)\log p$. Put $D=26509772707289$, $M=4D$, $\chi_4=\chi_{-4}$, and $\chi_D(p)=(D/p)$. Lean proves the following identities at every rational prime and every indicated exponent. [Coefficient identity with $G'/G$](ArchivedGaussianLogDerivative.lean) · [Parity theorems and axiom audit](GaussianPrimeSupport.lean) · [Build output](GaussianPrimeSupport-audit.txt)

$$
\begin{aligned}
a(p^{2j+1}) &= a(p) &&(j\ge0),\\
a(p^{2j}) &= 1+\chi_4(p)^j+\chi_D(p)^j-(\chi_4(p)\chi_D(p))^j
    &&(j\ge1,\ p\nmid 2D),\\
a(p^{2j}) &= 1 &&(j\ge1,\ p\mid 2D).
\end{aligned}
$$

For a split prime the two residue characters sit at degree one. Their odd powers retain both signs and their even powers give $1$ or $0$. For an inert prime the single Gaussian prime has degree two. It contributes at even exponents of the rational prime, with its sign given by the rational norm character. At the conductor primes one split reading vanishes and the other has square $1$. At two the single degree-one reading is $+1$.

## The even series in Dirichlet terms

Write $L_M(v,\chi)$ for the rational Dirichlet $L$-function with Euler factors at primes dividing $M$ removed. Include the trivial character in this convention. Define

$$
H(v)=
\frac{L_M(v,1)L_M(v,\chi_4)L_M(v,\chi_D)}
{L_M(v,\chi_4\chi_D)}
\prod_{p\mid 2D}(1-p^{-v})^{-1}.
$$

In $\Re s>1/2$, take the logarithmic derivative in $v$ at $v=2s$. Absolute convergence and the checked local identities give

$$
\sum_p\sum_{j\ge1}a(p^{2j})(\log p)p^{-2js}
=-\frac{H'(2s)}{H(2s)}.
$$

All Euler terms on the right come from rational Dirichlet factors and the four specified primes $2,41,457,1414835497$. With the Dirichlet GRH input, its only possible pole for $\Re s>1/4$ is the positive real pole at $s=1/2$ inherited from the trivial character. The odd powers retain the original Gaussian sign $a(p)$. [Dirichlet GRH statements and independent replay](https://math.mit.edu/~drew/shortgrh/)

## The signed square term at the cutoff

Let $W_G(x)$ be the original ramp and $W_1(x)$ the ramp with just the first prime powers and the exact compensating linear term. Lean gives

$$
W_G(x)-W_1(x)=-\sum_p\sum_{m\ge2}a(p^m)(\log p)\min(1,x/p^m).
$$

For $m=2$ and $p\nmid 2D$, put $c(p)=a(p^2)=1+\chi_4(p)+\chi_D(p)-\chi_4(p)\chi_D(p)$. Its mean across the four Frobenius classes of the biquadratic field $\mathbb Q(i,\sqrt D)$ is $1$. Its other three terms are nontrivial quadratic characters. Under the supplied rational Dirichlet GRH, the Dedekind zeta of that biquadratic field satisfies RH by its Dirichlet factorization. Effective Chebotarev for its four classes, followed by partial summation, gives

$$
C(y)=\sum_{p\le y}a(p^2)\log p
=y+O(\sqrt y\log^2y).
$$

For $y=\sqrt x>1$, the square contribution before the minus sign is exactly

$$
C(y)+y^2\sum_{p>y}\frac{a(p^2)\log p}{p^2}
=2y^2\int_y^\infty\frac{C(t)}{t^3}\,dt
=2y+O(\sqrt y\log^2 y).
$$

For the sum with $m\ge3$, use $|a(p^m)|\le2$ and $\min(1,u)\le u^\alpha$ for $1/3<\alpha\le1$. Its absolute value is at most

$$
\frac{2x^\alpha}{1-2^{-\alpha}}\sum_p\frac{\log p}{p^{3\alpha}},
$$

which is finite. Thus for every $\varepsilon>0$,

$$
W_G(x)=W_1(x)-2\sqrt x+O_\varepsilon(x^{1/3+\varepsilon}).
$$

The negative square term explains a systematic downward shift in the original one-sided ramp. The remaining ERH estimate for the quartic concerns the signed prime contributions in $W_1$, at the same cofinal norm windows as before. The parity formulas and the exact ramp identity have Lean audits. The asymptotic above uses classical effective Chebotarev and is derived here. [Exact ramp proof](GaussianPrimeOnlyWindow.lean) · [Chebotarev bound, Theorem 1.1](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf#page=3) · [Frobenius classes and remaining estimate](gaussian-prime-classes.md)
