# The signed norm bound above the fixed zero-free exponent

I use two Frobenius classes of the actual quartic's degree-eight splitting field $L$. Their main terms cancel because each class has one element. A zero-free half-plane for $\zeta_L$ then gives a power-saving upper bound for the signed, centered log-norm expression in $\texttt{hcut}$ at every sufficiently large real cutoff. With Liu's Theorem 1.1 as the analytic input, this gives each exponent $\theta>B_{\rm tw}=0.874058503791859\ldots$. The remaining exponents for the quartic criterion are $1/2<\theta\le B_{\rm tw}$. [Liu, Theorem 1.1](https://hexagonmath.org/pdf/2610.00655v3#page=4) · [Exact quartic criterion](ArchivedGaussianNormCriterion.lean)

## The two prime counts

Let $z$ be the central involution of the dihedral group of order eight, and let $g_p$ be an arithmetic Frobenius label for an unramified rational prime $p$. Away from the finite coefficient exceptions the archived coefficient is $a(p)=2(\mathbf 1_{g_p=1}-\mathbf 1_{g_p=z})$. The coefficient used in the squared cutoff is $b(p)=-a(p)\log p$ at primes and zero at other integers. Define $P(u)=\sum_{p\le u}a(p)\log p$. The archive checks the coefficient against arithmetic Frobenius at any good prime. [Arithmetic Frobenius coefficient](GaussianClosurePrimeTrace.lean)

For a singleton class $C=\{1\}$ or $\{z\}$, write $\Theta_C(u)=\sum_{p\le u,\ g_p\in C}\log p$. Theorem 1.1 of Frei, Sofos and Widmer, followed by partial summation, gives
$$
\Theta_C(u)=\frac{u}{8}+O_L\bigl(u^{B_{\rm tw}}\log^2 u\bigr).
$$
Each class has size one, and Liu's result applies to the Dedekind zeta of the splitting field. Subtracting the two estimates gives $P(u)=O_L(u^{B_{\rm tw}}\log^2 u)$. Finite prime exceptions contribute $O_L(1)$. Hence for each $B_{\rm tw}<\theta<1$ there is an $A\ge0$ such that $|P(u)|\le A u^\theta$ for $u\ge1$, enlarging the constant on any bounded initial interval. [Effective Chebotarev estimate](https://arxiv.org/html/2610.18491v2#Thmtheorem1)

The same argument applies with any zero-free exponent $1/2\le b_0<1$ for $\zeta_L$. For example, the $31/32$ theorem of Cureton and Thorner gives every $\theta>31/32$ through the same steps. Their Lean proof is a separate package. [Cureton and Thorner, version 2](https://hexagonmath.org/2610.00200v2) · [Their Lean package](https://github.com/AxiomMath/DedekindZetaZeroFree)

The reciprocal sum converges by partial summation. If $G$ denotes the archived Gaussian factor and $Q(s)$ is the higher-prime-power part of its negative logarithmic derivative, the Euler-factor identity gives
$$
\sum_{p} \frac{b(p)}{p^s}=\frac{G'(s)}{G(s)}+Q(s) \qquad (\Re s>1).
$$
The prefix bound makes the left side locally uniformly convergent on $\Re s>\theta$. The higher-power sum converges absolutely there, since its coefficients at $p^j$ are bounded by $2\log p$ for $j\ge2$. In particular $G'/G$ is bounded as $s$ tends to $1$ along the real axis, so the nontrivial entire function $G$ has $G(1)\ne0$. The archived real center is then $c=\Re(G'/G)(1)+Q(1)=\sum_p b(p)/p$. For $x\ge1$,
$$
\left|\sum_{p\le x}\frac{b(p)}p-c\right|
 \le A\left(1+\frac{1}{1-\theta}\right)x^{\theta-1}.
$$
Here the two terms in the constant bound $|P(x)|/x$ and $\int_x^\infty |P(u)|u^{-2}\,du$. [Logarithmic derivative](ArchivedGaussianLogDerivative.lean) · [Higher prime powers](GaussianHigherPrimePowers.lean) · [Archived center](GaussianPrimePrefix.lean)

## The squared cutoff keeps the signed saving

Set
$$
R(y)=\frac y3-\sum_{1\le m\le y}(1-m/y)^2\quad(y>0),\qquad R(0)=0.
$$
On $n\le y\le n+1$, expand the finite sum through $n$. The extra summand at $y=n+1$ is zero. Writing $r=y-n$ gives
$$
3y^3R'(y)=y^3-3n(n+1)y+n(n+1)(2n+1)=n\bigl(1-3r(1-r)\bigr)+r^3\ge0.
$$
At the endpoints the formulas for the adjacent intervals agree. For $0\le y\le1$ the function is $y/3$, and $R(n)=1/2-1/(6n)$ at every positive integer $n$. Thus $R$ is increasing with $0\le R(y)\le1/2$. [Lean monotonicity and bound](GaussianSquaredRoundingResidual.lean)

For the exact centered squared cutoff this gives
$$
A_{\rm sq}(x)=\sum_{p\le x}(-b(p))R(x/p)
   +\frac x3\left(\sum_{p\le x}\frac{b(p)}p-c\right).
$$
The weights $R(x/p)$ decrease with $p$. Summation by parts writes the first term as a sum of prefixes $P(u)$ with nonnegative weights of total mass at most $1/2$. Its upper bound is therefore $Ax^\theta/2$. The reciprocal estimate bounds the remaining term by a constant times $x^\theta$. The checked comparison at scale $2\sqrt{x}$, together with the eventual arithmetic Frobenius data, adds an $O_\theta(x^\theta)$ error to give the same eventual upper bound for the retained norm expression. [Lean transfer with its exact hypotheses](ArchivedGaussianNormPowerBound.lean) · [Triangle error](GaussianSqrtTriangleWindow.lean)

Lean checks the transfer from the signed prefix and reciprocal-center estimates to the actual retained norm expression. The application of the cited zero-free theorem and Chebotarev, and the identification of the reciprocal limit with the archived center, are the written analytic inputs.
