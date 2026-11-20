# Where the untraced Gaussian contour can go

For the untwisted quadratic Hecke character of the quartic, let $H(w)=B^w\Gamma(w)L_{\mathbb Q(i)}(w,\eta_\delta)$, with $B=\sqrt{106039090829156}/(2\pi)$. Put $T=T_D$, $h=1/16$ and $S=B^2|\Gamma(2+iT)|$. The loop plot uses the single positive scale $S$ on every side. Both missing horizontal pieces, together with the whole two-dimensional rectangle between them, have their images in the following disks about the origin:

| Input real parts at $\vert \Im w-T\vert \le1/16$ | Uniform upper bound for $\vert H(w)\vert /S$ |
| --- | ---: |
| $[-1/8,9/8]$ (both missing passages in their entirety) | $5.733181\times10^{-16}$ |
| $[-1/44,45/44]$ (includes the critical strip) | $2.913022\times10^{-17}$ |

These are upper bounds for the image of the closed rectangles, including all interior points. A bound from below on the modulus, or a phase measurement, answers a different question. The disks include zero. A loop inside either disk can have more than one possible winding. [192-bit interval calculation](gaussian-strip-image.json) · [Replay](check_gaussian_strip_image.py)

## A maximum-modulus estimate on the full input strip

For $r>1$ let $a=r-1/2$. The Euler product gives $|L_{\mathbb Q(i)}(r+it,\eta_\delta)|\le\zeta_{\mathbb Q(i)}(r)=\zeta(r)\beta(r)$. This inequality permits the largest absolute contribution from each prime. Completing the function and using its reflection gives the same modulus on the opposite line $\Re w=1-r$. The original field is needed here: it gives one entire function of order one with this completion and functional equation. Independent sign choices can give Euler products on $\Re w>1$ without supplying those other properties. [Quartic field and character](https://github.com/NuckyDucky/The-Super-Zeta-Function/tree/main/archive/2026-11-20-dedekind-phase-v001) · [Hecke functional equation and order, §2](https://msp.org/ant/2017/11-5/ant-v11-n5-p04-s.pdf#page=8)

For $r\ge1/2$, the digamma series for $t>0$ and the reflection identity at $1/2$ give

~~~math
0\le\Im\psi(r+it)
  =\sum_{n\ge0}\frac{t}{(n+r)^2+t^2}
  \le \Im\psi(1/2+it)=\frac{\pi}{2}\tanh(\pi t).
~~~

Conjugation handles $t<0$. Integrating the derivative of $\log|\Gamma(r+it)|$ now yields, for all real $t$,

~~~math
|\Gamma(r+it)|\le|\Gamma(r+iT)|\,e^{(\pi/2)|t-T|}.
~~~

Apply the maximum modulus principle to $H(w)\exp\{\lambda(w-1/2-iT)^2\}$, for $\lambda>0$, on the strip $1-r\le\Re w\le r$. On either side its modulus is bounded above by

~~~math
B^r|\Gamma(r+iT)|\,\zeta_{\mathbb Q(i)}(r)\,
e^{\lambda a^2+\pi^2/(16\lambda)} .
~~~

Indeed, the largest exponent $-\lambda(t-T)^2+(\pi/2)|t-T|$ is $\pi^2/(16\lambda)$. On horizontal lines at imaginary parts tending to either infinity the damped function tends uniformly to zero across this fixed-width strip, since $H$ is entire of order one. The usual finite-rectangle maximum principle therefore gives the same bound everywhere inside. For $|\Im w-T|\le h$ removing the damping costs a factor at most $e^{\lambda h^2}$. Minimizing $\lambda(a^2+h^2)+\pi^2/(16\lambda)$ gives the explicit estimate

~~~math
\sup_{\substack{1-r\le\Re w\le r\\|\Im w-T|\le h}}\frac{|H(w)|}{S}
\ \le\
\frac{B^r|\Gamma(r+iT)|\,\zeta_{\mathbb Q(i)}(r)}{B^2|\Gamma(2+iT)|}
\exp\!\left(\frac{\pi}{2}\sqrt{a^2+h^2}\right).
~~~

The minimizing parameter is exact within this family of test functions. Equality in the final bound for $H$ has not been established.

## Enclosures on the plotted arcs

The plot also evaluates $H/S$ directly on the right outer arc at 160 bits, truncating its Euler product after prime-ideal norm $100000$. Write $q=N\mathfrak p$, $\sigma=\Re w$. The missing log-product has absolute value at most

~~~math
\log\!\left[\zeta_{\mathbb Q(i)}(\sigma)
             \prod_{q\le100000}(1-q^{-\sigma})\right],
~~~

where the product includes each prime ideal separately. This follows by majorizing each omitted log-Euler series by its positive untwisted series. The log-derivative $H'/H$ on the plotted pieces has modulus below $60$: bound the archimedean part using $|\psi(w)-\log w|\le(1/2+\pi/4)/|\Im w|$ from first Euler summation, and its Euler-product part by $-2\zeta'(9/8)/\zeta(9/8)$. Each small segment is consequently enclosed in a complex disk about the value of the numerical Euler product at its midpoint. The disk covers both the missing product and the log-value variation along the segment. All 320 disks exclude zero and contain the chord between adjacent sampled centers. The left pieces are conjugate copies with direction reversed. A straight homotopy from each chord to its true arc in the covering disk provides a continuous argument lift. Correcting the two endpoint arguments by their disk uncertainties gives **1.65940707 to 1.80703020 turns** for the two outer arcs together. The winding of the full contour remains undetermined. [Sample and segment disks](gaussian-loop-arcs.json) · [Replay](check_gaussian_loop_arcs.py)

## Sets of targets with an exact inverse-image count

For $D=[-1,2]+i[T-h,T+h]$, each row counts the solutions of $H(w)/S=y$ in the interior of $D$, with multiplicity, uniformly for the indicated closed target disk. The output value $y=0$ belongs to none of these disks.

| Output target $y$ | Preimages in $D$ |
| --- | ---: |
| $\vert y-0.5\vert \le0.3$ | 2 |
| $\vert y-0.91i\vert \le0.01$ | 1 |
| $\vert y-1.2\vert \le0.2$ | 0 |
| $\vert y-6\times10^{-16}\vert \le2\times10^{-17}$ | 2 |
| $\vert y+6\times10^{-16}\vert \le2\times10^{-17}$ | 2 |

The calculation bounds the clearance from each target disk to every known segment enclosure and to the disk of radius $5.733181\times10^{-16}$ containing the entire unknown image. Each known segment may be deformed to its plotted chord within its own disk. The two unknown arcs may be deformed to chords inside the small disk about zero, preserving the winding about $y$. The argument principle now gives the exact counts from the polygon by interval arithmetic. This construction of counting chords is used only for the specified target disks; it gives no data points for the missing arcs. Boundary avoidance also makes the count locally constant throughout each target disk. Crossing the image of the boundary is necessary for the count to change. At singular or overlapping boundary points the net change can be zero.

At the real target $y=0.5$ there are exactly two *distinct, simple* preimages. They lie outside the central rectangle by its image bound, and reflection exchanges them since the target is real. Both have the same multiplicity and the sum is two. This gives an actual two-to-one fiber of the completed Gaussian function. For the tiny target disks the same central-rectangle bound puts every preimage in the padding. The targets are levels of the normalized analytic function; counts refer to preimages of a value, not attraction under an iteration. [Directed preimage counts](gaussian-preimage-counts.json) · [Replay](check_gaussian_preimage_counts.py)
