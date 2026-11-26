# The primitive norms up to the square root of the cutoff

I can bound part of the actual signed Gaussian Möbius sum below the square-root scale. I split the rational content of each ideal from its primitive part. Then I use the rational zeta input on the content and the existing Gaussian zero-free bound on the primitive variable. With a smooth cutoff covering primitive norms through $\sqrt Y$, the contribution is $O(Y^{1997/4000})$, where $1997/4000=0.49925$. [Original weighted ideal sum](gaussian-seventh-free.md#the-actual-signed-sum-at-the-shorter-scale) · [Exact Lean local factors and exponents](GaussianMoebiusContent.lean) · [Build and axiom output](gaussian-moebius-content-audit.txt)

## Two variables at each prime

For each squarefree Gaussian ideal $\mathfrak d$, write $\mathfrak d=(m)\mathfrak b$, where $m$ is the gcd of the coordinates of a Gaussian generator, and $\mathfrak b$ is divisible by no ideal of the form $(p)$ for a rational prime $p$. Equivalently, no rational prime divides both coordinates of a generator of $\mathfrak b$. Its norm $n=N\mathfrak b$ is squarefree as a rational integer, and $\gcd(m,n)=1$. The norm of $\mathfrak d$ is $m^2n$.

At an odd split prime either one marked prime contributes to $\mathfrak b$, or both belong to $(m)$. Their product in the latter case has sign $\chi((p))=\chi_D(p)$, where $D=26509772707289$ and $\chi_D$ is the rational quadratic character of the norm discriminant. At an inert prime only the rational choice is possible, and ideal Möbius contributes a minus sign. At $2$, a single Gaussian prime can occur in $\mathfrak b$. The rational choice would repeat it. Thus the rational content has Dirichlet character $\psi=\chi_{-4}\chi_D$ and squarefree weight $\mu(m)^2\psi(m)$. The primitive norm weight is

$$
U(n)=\mu(n)^2\prod_{p\mid n}(-a(p)),
$$

where $a(p)$ is the archived Gaussian prime coefficient. For example, at $5$ the primitive choice has summed weight $-2$ and the rational choice has weight $+1$. At $73$ the primitive choices cancel and the rational choice has weight $-1$. I checked the grouped coefficients through norm $8192$ against direct enumeration of the $6436$ Gaussian ideal representatives in that range. The test used the three archived Legendre readings. [Exact prime signs](gaussian-inert-windows.md#which-positive-count-to-bound) · [Lean diagonal identity](GaussianMoebiusContent.lean)

For $\Re s,\Re w>1$, the joint Dirichlet series is

$$
F(s,w)=
\sum_{\gcd(m,n)=1}
\frac{\mu(m)^2\psi(m)U(n)}{m^s n^w}
=\prod_p(1+\psi(p)p^{-s}-a(p)p^{-w}).
$$

Put $R(s)=L(s,\psi)/L(2s,\psi^2)$. Lean checks the diagonal identity at $p^{-s}=p^{-2w}$ and the bound on the difference from the product of the separate local factors of $R(s)$ and $1/G(w)$. If $u=p^{-s}$ and $v=p^{-w}$, that difference has modulus at most $2|u||v|+|v|^2+|u||v|^2$. The two local denominators are bounded away from zero on positive closed substrips by $1-p^{-\Re s}$ and $(1-p^{-\Re w})^2$. Therefore the quotient correction $\mathcal E(s,w)$ converges normally and is bounded on closed strips inside $\Re s>0$, $\Re w>1/2$, $\Re(s+w)>1$. I obtain

$$
F(s,w)=R(s)\frac{\mathcal E(s,w)}{G(w)}.
$$

Here $\psi$ is nonprincipal since its mod-four factor changes under $n\mapsto n+2D$ on odd integers. The denominator of $R(s)$ is $\zeta(2s)$ with finitely many Euler factors removed. The ordinary RH input therefore makes $R$ analytic for $\Re s>1/4$, with a zero where the denominator has its pole. Using the Gaussian zero-free input $b=873333/10^6$ from Liu, the joint expression is analytic on $\Re s>1/4$, $\Re w>b$. Both reciprocal factors have polynomial growth on the closed vertical strips used below. This follows from Borel–Carathéodory in the corresponding zero-free half-planes, regularizing $\zeta$ at its pole before taking a logarithm. [Lean local correction bound](GaussianMoebiusContent.lean) · [Liu, Lemma 4.3 and Theorem 7.33](https://hexagonmath.org/pdf/2611.00741v1)

## The part with primitive norm at most the square-root scale

Write $M(Y)=S(CY^7)$ and $H(v)=\Theta(v^7/C)$, with $C=\sqrt D/\pi$. Choose a smooth $V$ between zero and one, equal to one through $1$ and zero from $2$ onward. Insert $V(n/A)$ in the exact ordered sum for $M(Y)$. If I Mellin-invert both weights, the part with this cutoff is

$$
M_{\le}(Y,A)=
\frac{1}{(2\pi i)^2}
\int\!\!\int
\widehat H(z)\widehat V(u)\,Y^z A^u\,F(2z,z+u)\,du\,dz.
$$

The integral starts on lines to the right of absolute convergence. The transform $\widehat H(z)=C^{z/7}\Gamma(z/7)G(z/7)/7$ on $\Re z>0$ has exponential vertical decay on closed strips. This follows by the checked theta tails, the Mellin identity on the initial strip, and Stirling's estimate. The transform $\widehat V$ has rapid decay on strips with $\Re u>0$ by integration by parts against the compactly supported derivative of $V$. These bounds justify moving the two lines in succession, first $z$ with $u$ far to the right, then $u$ with $z$ fixed. [Checked theta reflection and tails](GaussianSeventhFreeMellin.lean)

I move to $\Re z=1251/10000$ and $\Re(z+u)=8734/10000$. Lean verifies $2\Re z>1/4$, $\Re(z+u)>b$, $\Re(3z+u)>1$, and $\Re u>0$. The resulting bound is $O(Y^{\Re z}A^{\Re u})$. At $A=\sqrt Y$ the exponent is $1997/4000$. The ordinary RH input, the cited Hecke half-plane, and the written two-variable contour argument are the analytic inputs to this estimate. [Lean contour coordinates](GaussianMoebiusContent.lean)

## The contribution still to bound

If I subtract $M_{\le}(Y,\sqrt Y)$, the same weighted Möbius sum now takes $n>\sqrt Y$ with weight $1-V(n/\sqrt Y)$. The target remains $O_\varepsilon(Y^{1/2+\varepsilon})$ for that residual. Its dominant norm range is $m^2n$ at scale $Y$. More precisely, for any prescribed power saving, the checked exponential upper tail lets me discard $m^2n>Y(c\log Y)^{1/7}$ with $c$ large enough. To see the total error, factor out half the exponential at the cutoff and sum the rest using the Gaussian ideal count $O(T)$ for norms up to $T$. On the remaining part, $m\le Y^{1/4}(c\log Y)^{1/14}$. The signed primitive coefficients there still require an estimate. [Original square-root criterion](gaussian-seventh-free.md#why-seven-works)

If I replace the ideal Möbius weight by two shorter factors and sum the unrestricted Gaussian coefficient into the kernel, both variables are confined to the square-root norm up to logarithms. The earlier $O(Y^{1997/4000})$ estimate lets me use this for the large-primitive-norm part. [Two-factor calculation](gaussian-balanced-moebius.md)
