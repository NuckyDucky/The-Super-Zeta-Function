# A logarithmic window for the largest-prime sum

If I use the rational Dirichlet critical-line input, one difference of theta scales clears the higher-prime-power part. The resulting kernel lets me keep only

$$
\frac{X}{(\log X)^{5/2}}<p<X,\qquad
(\log X)^{1/6}<m\le(\log X)^{8/3}.
$$

Here $p$ is the unique largest prime of $n=mp$. The discarded terms together contribute $O(X^{3/8}(\log X)^{1/6})$. The same kernel carries a signed prime-prefix bound into this window with only a factor of powers of $\log X$. [Lean identities and inequalities](GaussianVaughanLogWindow.lean) · [Independent replay and axioms](gaussian-vaughan-log-window-audit.txt)

## Two readings of the original theta

I use $A,B,L$ for the same Gaussian reciprocal, ideal, and signed Mangoldt coefficients as before. Put $C=\sqrt{26509772707289}/\pi$, $\Lambda(w)=C^w\Gamma(w)G(w)$ and $H(v)=\Theta(v^7/C)$. For the Mellin convention $\widehat H(z)=\int_0^\infty H(v)v^{z-1}\,dv$, we have $\widehat H(z)=\Lambda(z/7)/7$. I now take

$$
D(z)=1-2^{1/2-z},\qquad H_D(v)=H(v)-\sqrt2 H(2v),\qquad
\widehat H_D(z)=D(z)\widehat H(z).
$$

Lean checks the scale difference in the Mellin integral, its zero at $1/2$, and its nonvanishing on $\Re z>1/2$. I use $K_D$ and $J_D$ for the inverse Mellin weights of $G\widehat H_D$ and $-G'\widehat H_D$. [Original theta and reflection](gaussian-seventh-free.md) · [Previous choice of clearing factors](gaussian-vaughan-window.md)

Write $\Pi(z)$ for the higher-prime-power part of $-G'(z)/G(z)$. The checked odd-power inversion gives $\Pi(z)=\mathcal E(z)-\sum_{j\ge3,\ j\ \mathrm{odd}}\mu(j)(\mathcal B(jz)-\mathcal E(jz))$, where $\mathcal B=-G'/G$ and $\mathcal E$ is its even-power part. I use $\tau=3/8$. Then $3\tau>1$. On $\Re z\ge\tau$ the odd iterates are bounded by absolutely convergent Euler series, with a geometric factor $2^{-(j-3)\tau}$ after taking absolute values. The even part uses the log derivatives of the four rational Dirichlet functions at $2z$, with the finite Euler adjustments, as in the earlier formula. With the rational Dirichlet input, these have no zero poles at $\Re(2z)\ge3/4$. The only pole on the resulting half-plane is the simple principal pole at $z=1/2$. The factor $D$ clears it.

The log derivatives have polynomial vertical bounds in the fixed strips used here. One way to see this is to remove the principal pole by multiplying its $L$-function by $w-1$, to use the analytic log on disks centered at $2+it$ of radius $7/5$, and to apply Borel–Carathéodory and Cauchy's estimate on smaller disks containing $3/4+it$. The upper bound for the real part of the log comes from polynomial strip growth. The value at the center is controlled by the absolutely convergent Euler product there, and the finitely many omitted Euler factors and their reciprocals are bounded for $\Re w\ge3/4$. After multiplication by $\widehat H_D$, this gives the exponential vertical decay needed to shift both $\Pi\widehat H_D$ and $\Pi G\widehat H_D$ to $\Re z=\tau$. [Odd inversion and even Euler formula](gaussian-vaughan-window.md#separating-the-higher-powers) · [Rational Dirichlet input](https://math.mit.edu/~drew/shortgrh/)

## The kernel at a small argument

At either end of the positive axis, $H_D$ decays exponentially in $v^7$ or $v^{-7}$. For $H$ this follows from the absolutely convergent theta series at large argument and $\Theta(v^7/C)=v^{-7}\Theta(v^{-7}/C)$ at small argument. It carries to each of the two scales of $H_D$ with a change of constants. At infinity, $K_D(v)=\sum_{n\ge1}B(n)H_D(nv)$ gives the same $O(e^{-c v^7})$ bound. For $J_D$ the entire transform and vertical decay give arbitrary power decay at zero by shifting to each fixed left line.

For $K_D$ at zero I can control the dependence on the line. For $z=-N+it$ and positive integer $N$, reflection of $G$ gives

$$
G(z)=C^{1-2z}\frac{\Gamma(1-z)}{\Gamma(z)}\,G(1-z).
$$

The quotient means $\Gamma(1-z)$ times reciprocal Gamma, including at the nonpositive real integers. I use the Gamma recurrence and conjugation to obtain the exact norm

$$
\left|\frac{\Gamma(1+N-it)}{\Gamma(-N+it)}\right|
=|t|\prod_{j=1}^{N}(j^2+t^2)
\le (N+1+|t|)^{2N+1}.
$$

Lean checks the equality including $t=0$. The two reflected Euler readings, $G(1-z)$ and $G(1-z/7)$, are uniformly bounded for $N\ge1$. The conductor powers and $D$ cost at most $c_0^{N+1}$ for a fixed $c_0$. The one Gamma factor left in $\Lambda(1-z/7)$ satisfies

$$
|\Gamma(a-ib)|\le(\cos(\pi/4))^{-a}\Gamma(a)e^{-\pi|b|/4},
\qquad a=1+N/7,\quad b=t/7.
$$

This follows from the Euler integral by rotating the ray toward $-\operatorname{sgn}(b)\pi/4$. Bounding the real $\Gamma(a)$ by Stirling and integrating the polynomial in $N+1+|t|$ against $e^{-\pi|t|/28}$ gives

$$
\int_{\mathbb R}|(G\widehat H_D)(-N+it)|\,dt
\ll c_1^{N+1}(N+1)^{15N/7+2}.
$$

For instance, I bound the polynomial by $2^{2N+1}((N+1)^{2N+1}+|t|^{2N+1})$ and integrate the two terms. In Mellin inversion the line $-N$ adds the factor $v^N$. Taking $N=\lfloor c_2 v^{-7/15}\rfloor$ with $c_2>0$ sufficiently small makes $c_1 v(N+1)^{15/7}\le1/2$ for all sufficiently small $v$. I get $K_D(v)=O(e^{-c_3 v^{-7/15}})$ at zero. Inserting $-z$ in the inversion bounds $vK_D'(v)$ the same way with a change of constants. At infinity a termwise derivative of the theta sum bounds $vK_D'(v)$ by $O(e^{-c_4v^7})$. Thus $K_D$ is bounded and has integrable derivative on $(0,\infty)$. [Gamma recurrence](https://dlmf.nist.gov/5.5.E1) · [Real Stirling bound](https://dlmf.nist.gov/5.11) · [Mellin inversion](https://dlmf.nist.gov/2.5.E2) · [Lean Gamma product](GaussianVaughanLogWindow.lean)

## The surviving numbers

I put $\ell=\log X$, $U=\ell^{1/6}$, $V=X/\ell^{5/2}$, and $N_X=X\ell^{1/6}$. I use a fixed smooth nonincreasing $W$ between zero and one, with $W=1$ through $1$ and $W=0$ from $2$ onward. The cutoff terms in Vaughan's formula use $A_0(m)=A(m)W(m/U)$ and $L_0(b)=L(b)W(b/V)$.

The three short terms have arguments at most $2U/X$, $2V/X$, and $4UV/X$. The first uses $J_D$, the second $H_D$, and the third $K_D$. The bound just proved for $K_D$ at $4UV/X=4\ell^{-7/3}$ yields $\exp(-c\ell^{49/45})$. This and the other two bounds beat every fixed inverse power of $X$ after summing the polynomially bounded coefficients.

I expand the higher powers of the last term as in the earlier argument. The term at the higher powers alone is $O(X^\tau)$ by shifting $\Pi\widehat H_D$. The term with $A_0$ and the full higher-power sequence is

$$
O\!\left(X^\tau\sum_{m\le2U}|A(m)|m^{-\tau}\right)=O(X^\tau U)
$$

by shifting $\Pi G\widehat H_D$ at argument $m/X$ and using $|A(m)|\le d(m)\ll_\tau m^\tau$. The other two higher-power terms have the short cutoffs above. In the remaining prime term the product tail $mp>N_X$ is arbitrarily small in powers of $X$, since $K_D$ decays as $e^{-c(mp/X)^7}$ and $\ell^{7/6}$ grows faster than $\ell$. This uses the polynomial growth of the divisor sums over each product $mp$.

For sufficiently large $X$, $\ell^{31/6}\le X$. The marked prime $p>V$ then satisfies $p^2>N_X$, and the inequalities $m>U$, $mp\le N_X$ give $m\le\ell^{8/3}$ and $p<X$. Lean checks these implications. The exact largest-prime reading therefore gives

$$
\sum_{n\ge1}L(n)H_D(n/X)
= -\!\!\sum_{\substack{2\le n\le N_X\\ p=P^+(n)>V,\ m=n/p>U}}
 A(n)\log p\,(1-W(m/U))(1-W(p/V))K_D(n/X)
 + O\bigl(X^{3/8}\ell^{1/6}\bigr).
$$

Here $p,m$ are recovered from each $n$. The derivation uses the supplied rational Dirichlet input. The scale identity, Gamma product and cutoff implications are in Lean, and the contour shifts and summability estimates are written above. [Largest-prime coefficient and reindexing](GaussianVaughanLargestPrime.lean) · [Vaughan identity on the actual coefficients](GaussianVaughanWindow.lean)

## Completing the prime sum at each cofactor

The prime sum with the same $K_D$ and the cutoff removed already fits below square root after summing over these cofactors. Its transform in the argument $v$ of $\sum_p L(p)K_D(pv)$ is

$$
(\mathcal B-\Pi)G\widehat H_D
=-G'\widehat H_D-\Pi G\widehat H_D.
$$

Both terms allow the shift to $\Re z=\tau$, so the completed prime sum is $O(v^{-\tau})$ for $0<v\le1$. On $m\le\ell^{8/3}$, its contribution at $v=m/X$ is $O(X^\tau\ell^{8/3})$ by the same bound $|A(m)|\ll_\tau m^\tau$.

I can thus read the same signed sum using the other side of the prime cutoff. I first extend the prime range at the retained cofactors to all $p$ with the weight $1-W(p/V)$. The product tail is arbitrarily small in powers of $X$. Then I subtract the $W(p/V)$ reading from the completed sum. The completed sum meets the bound above. On the subtracted reading, $p\le2V$ allows me to include $m\le2U$ with arbitrary power saving from the small-argument bound for $K_D$. Also, for $p\le X/\ell^5$ and $m\le\ell^{8/3}$ we have $mp/X\le\ell^{-7/3}$, so this part has the same arbitrary power saving. I obtain the alternative formula

$$
\sum_{n\ge1}L(n)H_D(n/X)
=-\sum_{m\le\ell^{8/3}}A(m)
 \sum_{X/\ell^5<p\le2X/\ell^{5/2}} L(p)W(p/V)K_D(mp/X)
 +O\bigl(X^{3/8}\ell^{8/3}\bigr).
$$

The inner sum is over primes. For large $X$ they still exceed every cofactor in the sum. This estimate uses cancellation from $G\mathcal B=-G'$ at the completed prime reading. It leaves a signed estimate on the surviving cutoff interval. [Archived log-derivative identity](ArchivedGaussianLogDerivative.lean)

## The signed prefix at the marked primes

For $V\le t\le X$, let $P_V(t)=\sum_{V<p\le t}a(p)\log p$, and let $D_X=\sup_{V\le t\le X}|P_V(t)|$. The two classes in the normal closure contribute with opposite signs. Once $V$ is beyond the finite exceptions, $P_V(t)$ is twice the difference of the log-weighted identity and central-involution prime counts in $(V,t]$.

For a fixed cofactor $m$ the weight of this signed prefix is $g_m(t)=(1-W(t/V))K_D(mt/X)$. Its supremum and variation on any subinterval are bounded independently of $X,m$, using the boundedness and integrable derivative of $K_D$ and the monotone cutoff. Partial summation bounds the corresponding prime sum through $N_X/m$ by a fixed constant times $D_X$. Lean supplies the finite prefix inequality using the endpoint and sum of successive weight differences. Summing $|A(m)|$ up to $\ell^{8/3}$ by the divisor bound gives a total of

$$
O\bigl(D_X\,\ell^{8/3}(1+\log\ell)\bigr).
$$

The same variation bound works with $W$ and the interval $[X/\ell^5,2V]$ in the alternative formula. Either transfer spends only powers of $\log X$. The square-root estimate I need is for the weighted sum across cofactors. A uniform square-root bound on the individual signed prime prefixes would suffice. The rational Dirichlet criterion controls the combined mass of the two classes, so one can also express the signed prefix on $(V,t]$ as four times the excess of the completely split count over $(t-V)/8$, with a square-root-scale error up to logs. [Two Frobenius classes and the abelian input](gaussian-prime-classes.md) · [Lean partial summation bound](GaussianVaughanLogWindow.lean)

## The one-sided estimate on late windows

Write $F(X)=\sum_n L(n)H_D(n/X)$ for the full real reading, with value zero for $X\le0$. The series converges locally uniformly for $X>0$. The coefficient bound $|L(n)|\le2\log n$ and the large-argument bound for $H_D$ give $F(X)=O(X\log(2X))$ for $X\ge1$ by summing below $X$ and over dyadic intervals above it. At zero, $F$ decays to arbitrary powers. Its Mellin transform on $\Re z>1$, using the weight $X^{-z-1}$, is $D(z)\Lambda(z/7)(-G'(z)/G(z))/7$.

I can apply the existing Lean window theorem with the transform from $1$ to infinity. This subtracts the entire function $\int_0^1 F(X)X^{-z-1}\,dX$ from the formula above. At a zero $\rho$ of $G$ with $\Re\rho>1/2$ and multiplicity $r$, the logarithmic derivative has a simple pole with residue $-r$ by locally factoring $G(z)=(z-\rho)^r U(z)$ with $U(\rho)\ne0$. Both $D(\rho)$ and the reflected numerator $\Lambda(\rho/7)$ are nonzero under the existing zero-free input. The subtraction leaves the same pole. The real-axis positivity input rules out real Gaussian poles, which supplies the real-residue condition of the window theorem.

Let $T_{\rm low}(X)$ be the signed double sum, **including** its leading minus sign, in the alternative formula. For every $1/2<\theta<1$, it suffices to find a constant $C_\theta$ and $\delta>0$ such that $T_{\rm low}(X)\le C_\theta X^\theta$ throughout arbitrarily late intervals $[Y,Y^{1+\delta}]$. The error $O(X^{3/8}(\log X)^{8/3})$ fits the same exponent, so this would supply the window bound for $F$. This is a written application of the Lean window theorem using the stated Mellin and positivity inputs. [Exact window theorem and premises](GaussianRawWindowCriterion.lean) · [Real-axis positivity replay](quartic-real-positivity-audit.txt) · [Nonzero numerator](GaussianSeventhFreeMellin.lean) · [Hecke zero-free input, Theorem 7.33](https://hexagonmath.org/pdf/2611.00741v1#page=66)
