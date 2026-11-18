# Seven regrouped blocks account for every zero in both windows

Let $G(w)=F(w/2)$ and $h(v)=v\,\operatorname{sech}^2\sqrt v$. By the [coupling-response identity](../2026-11-17-quartet-return-recursion-v001/quartet-return-phase.tex),

$$
G(w)=K(w)\int_0^\infty v^{-w/2-1}h(v)\,dv,\qquad
K(w)=\frac{\sin(\pi w/2)}{\pi(w-1)}.
$$

Indeed, the coupling derivative at zero equals both $(w/2)\sin(\pi w/2)/\pi$ times the integral and $w(w-1)G(w)/2$. The Mellin integral is holomorphic for $\Re w<2$ because $h(v)=O(v)$ near zero and decays exponentially in $\sqrt v$ at infinity. At our heights $K$ is holomorphic on a neighborhood of each closed rectangle.

For each window choose $S=\sin(1/H)$, $g=S^2/8$ and $r_g=gh/(1+gh)$. Replace $h$ in the integral by the finite sum $g^{-1}\sum_{j=1}^Jr_g^j$ to define $G_J(w)$. The omitted kernel is exactly $h r_g^J$. To identify what is being counted, write $r=h/(1+h)$ for the original layer variable. On the original positive ray,

$$
\frac{r_g^j}{g}
=\sum_{m=j}^{\infty}\binom{m-1}{j-1}g^{j-1}(1-g)^{m-j}r^m.
$$

This is the binomial expansion of $r_g=gr/(1-(1-g)r)$. Thus each block is a weighted sum of original layers. The approximant is an explicit sum of $J$ Mellin integrals. The choice of $g$ uses only the window center.

## Uniform truncation error

Set $v=z^2$. Fix a positive $\tau$ with $\tau/H<\pi/2$, set $S_\tau=\sin(\tau/H)$ and require $S_\tau^2>2g$. Rotate the positive ray for $z$ clockwise by $\theta=\pi/2-\tau/H$, taking the logarithm continuously in the swept sector. Changing the ray estimates the same remainder for the same finite approximant. For $z=x e^{i\phi}$ in this sector, $\Re z\ge S_\tau x$ and

$$
|\cosh z|^2=\sinh^2(\Re z)+\cos^2(\Im z),\qquad
|h(z^2)|\le S_\tau^{-2},\qquad |r_g(z^2)|\le q_\tau=\frac{g}{S_\tau^2-g}<1.
$$

These bounds follow from $\sinh(S_\tau x)\ge S_\tau x$ and $|1+gh|\ge1-g/S_\tau^2$. They exclude the denominator poles throughout the rotation. The small circular arc tends to zero since $h(z^2)=O(z^2)$, and the large arc tends to zero by the exponential growth of $\sinh(S_\tau x)$. For $w=\beta+iT$ the new ray contributes $|z^{-w}|=x^{-\beta}e^{-\theta T}$.

For $0\le\beta\le1$, bound the integral of $x^{-\beta-1}|h(z^2)|$ in three parts.

- On $(0,1/2)$, $|\cosh z|^2\ge\cos^2(1/2)>1/2$ gives an integral at most $2$.
- On $[1/2,1/S_\tau]$, use $x^{-\beta}\le2$ and $|h|\le S_\tau^{-2}$ to get at most $2S_\tau^{-2}\log(2/S_\tau)$.
- On $[1/S_\tau,\infty)$, use $x^{-\beta}\le1$ and $\sinh(S_\tau x)\ge(1-e^{-2})e^{S_\tau x}/2$. The integral is bounded by $3e^{-2}S_\tau^{-2}/(1-e^{-2})^2<S_\tau^{-2}$.

The Jacobian contributes a factor of two. Multiplying by $|K(w)|\le e^{\pi T/2}/(\pi T)$ cancels the main exponential from the rotated ray. The resulting bound on the entire closed window is

$$
\sup |G-G_J|
\le \frac{2e^{\tau(H+1/2)/H}}{\pi(H-1/2)}\,q_\tau^{\,J}
\left[2+\frac{2\log(2/S_\tau)+1}{S_\tau^2}\right].
$$

The initial choice $\tau=1$ gives $q_\tau=1/7$. Larger values trade a larger exponential for a smaller geometric factor raised to the $J$th power. Here are rigorous, outward-rounded bounds. The position column measures distance from a finite-model zero to its assigned exact zero in the $s$-plane.

| Blocks $J$ | Ray parameter $\tau$ | Uniform error at $2T_D$ | Uniform error at $3T_D$ | Position errors at $2T_D$, $3T_D$ |
|---:|---:|---:|---:|---|
| 21 | 1 | $0.00174038$ | $0.00264469$ | $0.000482$, $0.000563$ |
| 7 | 15 | $0.000077762$ | $0.000118312$ | $0.0000216$, $0.0000252$ |
| 21 | 43 | $2.164\times10^{-58}$ | $3.293\times10^{-58}$ | $6.0\times10^{-59}$, $7.1\times10^{-59}$ |

Every entry meets the $0.003$ tolerance in the [local factorization proof](README.md). Each of the seven- and 21-block functions therefore has exactly one simple zero in each prescribed disk and none elsewhere in its rectangle. The position errors follow by dividing the tail bounds by the published distance coefficients. They measure the separation of two mathematically specified roots. Computing that many digits of either ordinate is a separate operation. [Directed tail calculation](native_complete.py)
