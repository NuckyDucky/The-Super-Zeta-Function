# Two simple preimages throughout two real target intervals

Let $f(w)=B^w\Gamma(w)L_{\mathbb Q(i)}(w,\eta_\delta)/S$ be the completed quartic Gaussian factor in the normalization of the contour figure. Here $T=T_D$, $h=1/16$, $B=\sqrt{106039090829156}/(2\pi)$, $S=B^2|\Gamma(2+iT)|$, and $D=[-1,2]+i[T-h,T+h]$. For every real $y$ satisfying

~~~math
1.05238\times 10^{-18}\le |y|\le 6\times10^{-16},
~~~

the equation $f(w)=y$ has exactly two simple solutions in the interior of $D$. They have the same imaginary part and lie on opposite sides of the whole critical strip. One has real part greater than $1.018$, and its partner has real part less than $-0.018$. The argument follows both target intervals continuously from the previously counted levels $y=\pm6\times10^{-16}$. The nearest endpoint is about 570 times closer to zero. [Anchor counts](gaussian-preimage-counts.json) · [Directed calculation](gaussian-target-corridor.json) · [Replay](check_gaussian_target_corridor.py)

## Bounding the central image with the actual prime phases

Write $r=509/500$, $a=r-1/2$, $\lambda=1/2$, $d=t-T$. On the boundary of the vertical strip $1-r\le\Re w\le r$, the reflection $w\mapsto1-\bar w$ preserves the modulus of $f$. Multiply $f$ by

~~~math
\exp\!\left[-\tfrac{i\pi}{2}(w-iT)+\lambda(w-\tfrac12-iT)^2\right].
~~~

The first factor compensates for most of the vertical change of $\Gamma$ near $T$. The second makes the product tend to zero as $|t|\to\infty$, uniformly across this strip, by the order-one growth of the completion. The finite-rectangle maximum modulus principle and passage to infinity reduce the central image bound to one supremum on the right boundary. More explicitly, put

~~~math
A(d)=\log|\Gamma(r+i(T+d))|-\log|\Gamma(r+iT)|+\pi d/2 .
~~~

The core image radius is at most

~~~math
\frac{B^r|\Gamma(r+iT)|}{S}
\exp\{\lambda(a^2+h^2)+\pi h/2\}
\sup_{d\in\mathbb R}|L(r+i(T+d))|\exp\{A(d)-\lambda d^2\}.
~~~

For $|d|\le12$, $|A(d)|\le3|d|/(T-12)$. Indeed $A'(d)=\pi/2-\Im\psi(r+i(T+d))$, and for $v>0$ the Euler summation estimate $|\psi(r+iv)-\log(r+iv)|\le(1/2+\pi/4)/v$ combines with $0\le\pi/2-\arg(r+iv)\le r/v$. For every real $d$, $|A(d)|\le\pi|d|$ by the digamma bound $|\Im\psi(r+iv)|\le\pi/2$. [Digamma estimates and reflection](gaussian-strip-image.md)

For $|d|\le5$, take 800 equal cells and $X=100000$. With $q=N\mathfrak p$, bound the omitted logarithm and the finite product's logarithmic derivative by

~~~math
E_X(r)=\log\!\left[\zeta_{\mathbb Q(i)}(r)\prod_{q\le X}(1-q^{-r})\right],
\qquad
D_X(r)=\sum_{q\le X}\frac{\log q}{q^r-1}.
~~~

Each prime ideal occurs separately in these envelopes. The midpoint product $L_X$ uses the actual signs of the Gaussian character. At any point of its cell the modulus is bounded by $|L_X(\mathrm{mid})|\exp(E_X(r)+D_X(r)/160)$. For $5<|d|\le12$ use the bound $\zeta_{\mathbb Q(i)}(r)e^{36/(T-12)-25\lambda}$ on the weighted expression under the supremum. For $|d|>12$, use $\zeta_{\mathbb Q(i)}(r)e^{12\pi-144\lambda}$, since $x\mapsto\pi x-\lambda x^2$ is decreasing there. The directed upper bounds on these three regions are respectively $2.825104$, $0.000165021$ and $5.618\times10^{-14}$. Multiplying by the displayed prefactor puts the full image of the core in $|f(w)|<1.052376322\times10^{-18}$.

## Connecting the central bound to the two known counts

At each height $T\pm h$, subdivide the remaining segment $r\le\sigma\le9/8$ into 128 equal cells. For a cell centered at $w_0$ with width $b$ and lower abscissa $\sigma_0$, compare the true value with $c=B^{w_0}\Gamma(w_0)L_X(w_0)/S$. The logarithmic error is bounded by

~~~math
\epsilon= E_X(\sigma_0)+\tfrac b2
\bigl(\log B+\log|2+i(T+1)|+\pi/2+1+D_X(r)\bigr).
~~~

The term in parentheses bounds the finite product and gamma logarithmic derivatives throughout the cell. A signed real ray at angular distance more than $\epsilon$ from $c$ misses the cell image. For every remaining ray, all possible crossings have modulus at most $|c|\exp(\epsilon)$. On the top edge all cells exclude both rays. On the bottom edge all cells exclude the positive ray. Fifteen bottom cells require the modulus test for the negative ray, and each possible crossing lies below $1.013979\times10^{-18}$. Reflection supplies the other side. The older 320 arc enclosures stay at positive distance from the entire real segment $[-6\times10^{-16},6\times10^{-16}]$. [Outer arcs](gaussian-loop-arcs.json)

Thus both target intervals avoid the whole boundary image $f(\partial D)$. Its winding around the target is constant along each interval. The earlier winding count of two at each outer endpoint carries over to every target on that interval. The core estimate excludes real parts in $[1-r,r]$. For each real target reflection supplies a distinct companion to each preimage, with the same multiplicity. Total multiplicity two forces exactly one simple preimage on each side.

The common inward cutoff in this calculation comes from the upper bound on the core image. Reflection also gives a reason to distinguish the two signs of the target. Both $f(1/2+i(T-h))$ and $f(1/2+i(T+h))$ are real by the functional equation, and each has absolute value below $1.052376322\times10^{-18}$. The real interval between the two certified corridors therefore contains at least one genuine boundary value. Its sign, its possible equality with zero, and the change in count at that value remain open. [Field functional equation and endpoint sign test](README.md#the-remaining-target-and-two-ways-to-test-it)
