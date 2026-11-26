# The largest prime in the Gaussian Vaughan sum

I can make one prime carry the address of each retained norm. For any fixed $0<\kappa<1/2$, the marked prime is larger than $X^{1-\kappa/2}$ and its cofactor is at most $X^{3\kappa/4}$. The terms outside this sum have total size $O_\kappa(X^{\kappa/2})$. Lean checks the signed coefficient at that address, the uniqueness of the prime, and the cutoff exponents. [Lean proof](GaussianVaughanLargestPrime.lean) · [Independent replay and axioms](gaussian-vaughan-largest-prime-audit.txt)

## The signed coefficient at one norm

Let $A$ be the Dirichlet inverse of the actual signed Gaussian coefficients $B$ and let $L$ be the signed Mangoldt sequence. I use the same $A,B,L$ and Mellin normalization as in the balanced formula. At every rational prime $p$, the archived Euler factors give $A(p)=-a_p$ and $L(p)=a_p\log p$. Since the inverse of a multiplicative arithmetic function is multiplicative, I get

$$
A(m)L(p)=-A(mp)\log p\qquad (p\nmid m).
$$

Lean proves the inverse is multiplicative by assembling its prime-power values and checking that the assembled sequence still convolves with $B$ to the unit. It also checks the weighted reindexing from ordered pairs $(m,p)$ to their product $n$. If $p\mid n$ and $p^2>n$, then the cofactor $n/p$ is smaller than $p$ and coprime to it. All other prime factors divide that cofactor. [Actual reciprocal Euler factors](GaussianMoebiusCommonDivisor.lean) · [Prime reindexing](GaussianVaughanLargestPrime.lean)

For example, $5$ and $13$ have opposite archived signs. Lean gives $A(65)=-4$. With the prime cutoff at $10$, the norm $65$ has the sole marked prime $13$, so its prime-weighted reading before multiplication by the cutoff and kernel is $4\log 13$. [Signs at 5 and 13](GaussianPrimeSupport.lean) · [Norm 65](GaussianVaughanLargestPrime.lean)

## Moving the two cutoffs apart

I fix $\kappa$ and put $\alpha=\eta=\tau=\kappa/4$ and $\beta=1-\kappa/2$. With $U=X^\alpha$, $V=X^\beta$, I take $A_0(m)=A(m)W(m/U)$ and $L_0(b)=L(b)W(b/V)$ in Vaughan's identity. Here $0\le W\le1$, $W=1$ through $1$ and $W=0$ from $2$ onward. I choose $M\tau>2$ once, independent of $X$ and of the exponent in the remaining signed bound. I use the same normalized weight $\widehat H_M(z)=D_M(z)\Lambda(z/7)/7$ and the kernels with transforms $G\widehat H_M$ and $-G'\widehat H_M$, denoted by $K_M$ and $J_M$. [Vaughan identity and Mellin normalization](gaussian-vaughan-window.md)

The arguments in the three short terms are at most $2U/X$, $2V/X$, and $4UV/X$. Since $UV=X^{1-\kappa/4}$ and the kernels decay to arbitrary powers at zero, each short term saves an arbitrary power of $X$. In the fourth term I separate off the higher prime powers $L_{\rm pow}$ and write their part as

$$
L_{\rm pow}-L_{{\rm pow},0}-A_0*B*L_{\rm pow}+A_0*B*L_{{\rm pow},0}.
$$

Both cutoff terms are short. For the rest I use the higher-power Dirichlet series $\Pi(z)=\sum_n L_{\rm pow}(n)n^{-z}$. The clearing factors of $D_M$ make both $\Pi\widehat H_M$ and $\Pi G\widehat H_M$ holomorphic down to $\Re z=\tau$, with exponential decay on that line. This lets me shift the contour for $L_{\rm pow}$ itself and bound it by $O_\kappa(X^\tau)$. For $A_0*B*L_{\rm pow}$, the same shift with argument $m/X$ bounds the smoothed contribution by

$$
O_\kappa\!\left(X^\tau\sum_{m\le2U}|A(m)|m^{-\tau}\right)
=O_\kappa(X^\tau U)=O_\kappa(X^{\kappa/2}).
$$

I used $|A(m)|\ll_\tau m^\tau$ from the reciprocal Euler factors. The upper tail of $K_M$ lets me restrict the surviving prime term to $mp\le X^{1+\eta}$ with arbitrary power saving. On this support, $p>V$ gives $p^2>X^{1+\eta}$, since $2\beta>1+\eta$. The marked prime is therefore the largest prime factor $P^+(n)$, and $n/P^+(n)\le X^{1+\eta-\beta}=X^{3\kappa/4}$. [Checked cutoff exponents](GaussianVaughanLargestPrime.lean)

## The signed bound at the remaining addresses

For $n\ge2$, put $p=P^+(n)$ and $m=n/p$. The result of the split is

$$
\sum_{n\ge1}L(n)H_M(n/X)
=-\!\!\sum_{\substack{2\le n\le X^{1+\kappa/4}\\
                      P^+(n)>X^{1-\kappa/2}\\
                      n/P^+(n)>X^{\kappa/4}}}
A(n)\log P^+(n)
\bigl(1-W(m/U)\bigr)\bigl(1-W(p/V)\bigr)K_M(n/X)
+O_\kappa(X^{\kappa/2}).
$$

Here the $m,p$ in each summand are recovered from that $n$. For $\kappa=1/3$, the sum uses $p>X^{5/6}$ and $X^{1/12}<m\le X^{1/4}$, with error $O(X^{1/6})$. The terms with two large marks have disappeared because the new prime cutoff puts their product beyond the retained range.

For any fixed $\kappa$ in this range, a bound $O_{\kappa,\varepsilon}(X^{1/2+\varepsilon})$ for the signed sum for every $\varepsilon>0$ would exclude all Gaussian zeros to the right of the critical line. The left side decays to arbitrary powers at $X=0$ by the large-argument bound on $H_M$. Its Mellin integral in $X$ with weight $X^{-z-1}$ equals $\widehat H_M(z)(-G'(z)/G(z))$ for $\Re z>1$. The proposed signed bound and the error would make that integral holomorphic on $\Re z>1/2$. For any proposed zero $\rho$ with $\Re\rho>1/2$, the numerator $\Lambda(\rho/7)$ is nonzero by reflection and the stated Gaussian Hecke zero-free bound. The factor $D_M(\rho)$ is nonzero there by its absolutely convergent Euler factors. Thus the pole of $-G'/G$ would persist, contradicting holomorphy. The rational Dirichlet cofactor theorem then carries the Gaussian conclusion to the quartic's Dedekind zeta. This uses the existing analytic inputs and the written contour estimates above. [Nonzero numerator](GaussianSeventhFreeMellin.lean) · [Hecke zero-free region, Theorem 7.33](https://hexagonmath.org/pdf/2611.00741v1#page=66) · [Quartic transfer](ArchivedGaussianNormCriterion.lean)
