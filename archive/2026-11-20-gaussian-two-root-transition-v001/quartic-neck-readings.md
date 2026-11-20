# Reading two inverse branches from a surrounding contour

For the original quartic polynomial $P$, the outlines in the figure are $|P(z)|=v$, with real $v>0$. The marked points on an outline instead solve the single equation $P(z)=v$. The original roots of $P$ stay fixed as the marked points move.

## The two-root contour

Let $D$ be a bounded domain with positively oriented piecewise smooth boundary. Suppose $h$ is holomorphic on a neighborhood of its closure and $h-v$ is nonzero on the boundary. For any origin $b$ put

~~~math
S_k(v)=\frac{1}{2\pi i}\int_{\partial D}
             (z-b)^k\frac{h'(z)}{h(z)-v}\,dz .
~~~

If $S_0=2$, call the solutions in the window $z_1,z_2$, repeating a double root. The residues give $S_k=(z_1-b)^k+(z_2-b)^k$. Consequently the midpoint is $b+S_1/2$ and

~~~math
G(v)=2S_2-S_1^2=(z_1-z_2)^2.
~~~

This signed squared separation is independent of $b$. In a window invariant under reflection about the real axis (quartic), or about the critical line (untwisted Gaussian completion for real targets), the reflection permutes the two solutions, so they lie on a common vertical or horizontal line. A positive reading means a horizontal separation; a negative reading means a vertical separation. A zero reading means one double solution. This gives the earlier half-separation convention $\Delta=G/4$. For a horizontal reflected Gaussian pair at $1/2\pm a+it$, its contribution to the squared horizontal spread is $2a^2=G/2$. A count other than two requires another isolating contour or a different moment analysis.

## The original quartic

Take $b=7/5$ and $d=1/10$. The 192-bit verifier expands the polynomial on the circle $z=b+dt,\ |t|=1$, as $P(z)-v=c_2t^2(1+u(t))$. It checks $\max|u|\le\sum_j |u_j|<2/5$ for the four target values. Rouché gives exactly two roots for each. Integration by parts gives $S_k/d^k=-k[t^{-k}]\log(1+u)$ for $k=1,2$. The calculation uses 100 terms of the logarithm with a uniform remainder $\eta^{101}/(101(1-\eta))$, where $\eta=\sum_j|u_j|$. The inputs are the polynomial coefficients, the circle and the target; neither root location is supplied. The merger target uses the previously isolated critical point. The equality at the merger follows from $P(c)=r_*,\ P'(c)=0,\ P''(c)>0$ and the count of two. [Verifier](check_quartic_neck.py) · [Numerical intervals](quartic-neck.json)

Write the original near pair as $m\pm ib$ in the next formula only. Its contribution to the quartic can be separated exactly:

~~~math
P(z)=((z-m)^2+b^2)K(z),\qquad
2b^2=\frac{2r_*}{K(c)}-2(c-m)^2 .
~~~

Here $K$ includes the leading coefficient and the other two roots. On the real line $K>0$. The displacement correction is $4.2040531475663\ldots\times10^{-7}$. The change in ordinary neck width follows from $P(c+x)=r_*+P''(c)x^2/2+O(x^3)$. For $v\downarrow r_*$ from above, the separation of the two real solutions is $2\sqrt{2(v-r_*)/P''(c)}+O((v-r_*)^{3/2})$, by expanding the two local inverse branches in powers of $\pm\sqrt{v-r_*}$. At $v=1.25r_*$ the actual width is $0.03289097976913704\ldots$.

## Application at the Dottie height

Use the same positive normalization $h$ of the untwisted Gaussian completion as in the [loop calculation](gaussian-strip-image.md). For either real target $v=\pm6\times10^{-16}$, there are exactly two preimages in $-1<\Re w<2,\ |\Im w-T_D|<1/16$. The central closed region $-1/8\le\Re w\le9/8$ has $|h|<5.734\times10^{-16}$. Reflection exchanges the two preimages, so one lies strictly to the left of $-1/8$ and the other strictly to the right of $9/8$, at equal height. In particular $G(v)>25/16$ at both targets. These preimages solve $h(w)=v$. [Multiplicity record](gaussian-preimage-counts.json) · [Uniform bound](gaussian-strip-image.json)

For real $v$ varying in a connected interval disjoint from $h(\partial D)$, the count stays constant and its contour moments are continuous, even at an interior double root. If it stays two, a horizontal-to-vertical transition forces $G(v)=0$, hence $h'(w)=0$ and $h(w)=v$. If a root passes through the boundary the count needs to be re-established. Indeed, at the two boundary inputs $1/2+i(T_D\pm1/16)$, the completion takes real values, both of modulus below $2.914\times10^{-17}$. A sweep of real targets from the negative test target to the positive one must therefore meet boundary values in that inner interval; this does not itself decide whether the count changes there. The current enclosures do not determine $G(0)$ or the Gaussian zero count in this rectangle. The quartic computation tests the diagnostic independently of the unknown Gaussian result.
