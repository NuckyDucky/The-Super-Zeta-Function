# Two detours to two zeros of the full Gaussian Hecke factor

For the archived quartic's real Gaussian Hecke character, put
$\Lambda(s)=B^s\Gamma(s)L_{\mathbb Q(i)}(s,\eta)$, where
$B=\sqrt{4\cdot41\cdot457\cdot1414835497}/(2\pi)$. Start at the **same exact source**
$s_0=51/100$ on both paths. Set $c=\Lambda(1/2)$ and
$\rho=\Lambda(s_0)-c$. The two target paths are

$$
c+\rho e^{+i\theta}\quad\text{and}\quad c+\rho e^{-i\theta},
\qquad 0\le\theta\le\pi,
$$

followed by the same straight segment from $c-\rho$ to $0$.
Counterclockwise reaches $1/2+it_0$. Clockwise reaches $1/2-it_0$.
The certificate brackets $0.25835<t_0<0.25838$ and proves both zeros simple.
A complete target lap in either direction exchanges the two local inverse sheets.

The launch also stays fixed when the detour shrinks. For any $0<r<\rho$, first follow the positive real output from $c+\rho$ to $c+r$. The inverse on this part has $s>1/2$. Now take either semicircle to $c-r$ and continue along the real output to zero. The same inverse disk covers every such radius, and strict monotonicity on the outgoing critical-line segments gives the same two terminal roots for all of them.

This experiment uses height zero for its critical point. The critical point and terminal zeros in the previously studied window around $T_D$ remain unestablished by this calculation. Rescaling the completion by a fixed positive constant rescales the entire target path.

## The two radii at the pinch

In the quadratic experiment I prescribe an output $U=1-z^2$. I measure the output radius $r=|U-1|$ from the critical value $1$ and the input radius $R=|z|$ from the critical point $0$. Then $r=R^2$. At a common target the inputs are $z$ and $-z$, so their separation is $2R=2\sqrt r$. The diameter of the output circle is $2r=2R^2$. At $r=0.01$ the input separation is $0.2$ and the output diameter is $0.02$. The formulas match radius to radius across the two planes.

To see why the two exits differ, follow one input as the output turns through $\theta$ radians. Multiplying the input by $e^{i\theta/2}$ multiplies $U-1$ by $e^{i\theta}$. The clockwise and counterclockwise arcs between the same entry and exit differ by $2\pi$ radians. Their lifted angles differ by $\pi$, so the exits are negatives of each other. This holds at every positive detour radius for which the paths share the specified entry and exit.

For my Gaussian factor, write $f(h)=\Lambda(1/2+h)$, $c=f(0)$ and $a=f''(0)/2$. The directed calculation below gives $3363500<f''(0)<3565602$. Evenness and analyticity give

$$
f(h)-c=a h^2+O(|h|^4),\qquad
\lim_{h\to0}\frac{f(h/2)-c}{f(h)-c}=\frac14 .
$$

At the target reached by $h$ and $-h$, put $r=|f(h)-c|$. The two inputs are exactly $2|h|$ apart, and their separation divided by $\sqrt r$ tends to $2/\sqrt a$ in every direction. There is also an exact local coordinate: take $q(h)=h\sqrt{(f(h)-c)/h^2}$, filling in the quotient at zero with $a$ and choosing the analytic square root that equals $\sqrt a$ there. Then $f(h)=c+q(h)^2$, $q'(0)=\sqrt a$, and the two inputs have $q$-coordinates separated by $2\sqrt r$.

The original coordinates show a measurable distinction. For real $t>0$, the positive kernel below gives

$$
f(t)-c>a t^2,\qquad 0<c-f(it)<a t^2 .
$$

The first inequality follows by integrating $\cosh(tx)-1>(tx)^2/2$ for $x>0$. The second follows by integrating $1-\cos(tx)\le (tx)^2/2$, strictly below that upper bound for $x>0$ and positive on an interval. At a small common output radius $r$, the real entry lies closer to the center than $\sqrt{r/a}$ and the imaginary exit lies farther away. This explains how the Gaussian inverse has the same square-root limit while its two arms already have different lengths at finite radius.

[Lean proofs of the radius, half-angle, Taylor expansion and limits](../../lean/SuperZeta/PinchRadius.lean) cover the quadratic without assumptions and derive the Gaussian radius limit for a centered half-Mellin integral from analyticity and nonzero second derivative. The field identification, positivity of its kernel, inverse continuation, and certified zero bracket are supplied by the mathematical argument and interval replay below.

## The actual arithmetic kernel is positive on the half integral

Write $a_n$ for the sum of the quartic's ideal character at norm $n$,
$A_n=\sum_{m\le n}a_m$ and $\Theta(u)=\sum_{n\ge1}a_n e^{-nu}$.
The Mellin transform of $\Theta(t/B)$ is $\Lambda(s)$ for $\Re s>1$.
The Hecke theorem for a nontrivial primitive character gives entireness. The quotient of the two completed Dedekind functions has root number $+1$. On fixed vertical strips the Gamma factor gives exponential decay against the polynomial growth of the Hecke function. The functional equation then gives $\Theta(t/B)=t^{-1}\Theta(1/(Bt))$ by Mellin inversion and contour shift.
Splitting the integral at $t=1$ therefore gives

$$
\Lambda(1/2+z)=2\int_0^\infty K(x)\cosh(zx)\,dx,\qquad
K(x)=e^{x/2}\Theta(e^x/B).
$$

I used the conductor and the signs from the [quartic field calculation](../2026-11-20-dedekind-phase-v001/README.md) and the [Gaussian completion and functional equation](../2026-11-20-gaussian-endpoint-parity-v001/gaussian-hardy-endpoints.md).

The integer enumeration gives $\min_{1\le n\le N}A_n=1$ and $A_N=17505$ for $N=2^{25}$.
Writing $r=e^{-u}$ and summing by parts gives
$\Theta_N=(1-r)\sum_{n=1}^{N-1}A_nr^n+A_Nr^N\ge r$.
The number of Gaussian ideals through norm $n$ is at most $2n$, since a unique representative has integer $a>0,b\ge0$ and $a^2+b^2\le n$.
Abel summation of this unsigned bound beyond $N$ gives

$$
|\Theta-\Theta_N|\le 2r^{N+1}(N+1+1/(e^u-1)).
$$

For $u\ge1/B$, the error divided by $r$ is below
$2(N+1+B)e^{-N/B}<0.090338$. Hence $K>0$ on the full integration range.
The second derivative at $s=1/2$ is $\int 2Kx^2dx>0$, while evenness gives the first derivative exactly zero.

## The common source and how the path picks an arm

Write $\Lambda(1/2+z)=c+g(z^2)$ and $a=g'(0)>0$.
Positivity of $K$ bounds $|g'(\zeta)-a|/a$ on $|\zeta|\le0.02^2$ by the average of
$\sinh(0.02x)/(0.02x)-1$ with positive weight $2Kx^2$.
Through $x=18$ this is at most $\sinh(0.36)/0.36-1$.
The integrable tail bound below gives a total below $0.021741$.
In particular $\Re g'>0$ throughout this disk. Integrating the derivative along straight segments gives injectivity and $|g(\zeta)-a\zeta|<0.023a|\zeta|$ away from the origin.
Since $\rho=g(0.01^2)<1.03a\,0.01^2$ and $0.97a\,0.02^2>\rho$,
Rouché's theorem gives a unique inverse $\zeta$ in the disk for every target $|w-c|\le\rho$.

The inverse is real on the diameter. It preserves the upper and lower halves because $g$ commutes with conjugation and $\Re g'>0$.
Starting at $z=+0.01$, a counterclockwise half-turn takes the continuous square root to a positive imaginary $z$ at $c-\rho$. The clockwise half-turn takes it to the negative imaginary $z$ at the very same target. A whole target turn makes the corresponding nonzero $\zeta$ wind once around zero, exchanging the two square roots in either orientation.

## Continuing both arms to target zero

Put $h(t)=\Lambda(1/2+it)$. The integral makes $h$ real and even. It gives

$$
-h'(t)/t=\int_0^\infty 2K(x)x^2\operatorname{sinc}(tx)\,dx .
$$

The interval replay certifies this quotient above $519994$ for every $0\le t\le0.27$, using its continuous value at $t=0$. It also gives $h(0.25)>345$ and $h(0.27)<-666$.
Thus the positive-height branch descends monotonically to its first simple zero. Evenness gives the other arm and its reflected simple zero. The derivative stays nonzero along both lifted descents.

For the numerical enclosures, the verifier groups the positive integers $A_n$ in short intervals and sums each group exactly. The two end norms enclose the exponential weight across that group. Monotonicity in $u$ bounds the entire Abel sum on each of 1,152 closed $x$ intervals from $0$ to $18$. The derivative test covers the height interval with 54 closed subintervals.
Beyond $x=18$, $u=e^x/B>40$ and $|\Theta(u)|\le2e^{-u}/(1-e^{-u})^2<3e^{-u}$. For $x=18+y$, use $e^y\ge1+y$ and $(18+y)^2\le18^2e^{2y/18}$. The resulting upper bound for the integral of $2e^{x/2}|\Theta|x^2e^{0.02x}$ over this tail is below $2.284\times10^{-12}$. This bounds every infinite integral remainder used in the certificate.

Two extra point enclosures sharpen the root bracket. They give
$2.229<h(0.25835)<3.867$ and $-3.091<h(0.25838)<-1.453$.
For a group of norms $\ell\le n\le b$ take $m=\lfloor(\ell+b)/2\rfloor$, $W=\sum A_n$ and $D=\sum(n-m)A_n$, all exact integers. The first-order Taylor approximation to $\sum A_n e^{-nu}$ is $e^{-mu}(W-uD)$. Its positive remainder is bounded above by $W e^{-\ell u}u^2\lceil(b-\ell)/2\rceil^2/2$.

The verifier integrates these enclosures on $[0,18]$ with 14-point Gauss–Legendre quadrature on 72 panels of width $1/4$. On the complex unit disk about every panel center one has $\Re(e^x/B)\ge d=e^{-1}\cos(1)/B>0$. The integrand there is bounded by $M=4e^{19/2}\cosh(0.27)/(1-e^{-d})^2$ by the ideal count. Cauchy's estimate bounds the remainder after Taylor degree 27 across a panel by $M(1/8)^{28}/(1-1/8)$. The quadrature integrates that polynomial exactly, and positive weights have total equal to the panel width. The total quadrature error is thus at most $36M(1/8)^{28}/(1-1/8)<8.012\times10^{-6}$. Both the arithmetic and integral tails are included in each endpoint enclosure.

## Replay

From the repository root, with Python 3.12, NumPy 2.5.5 and python-flint 0.9.0, run

~~~sh
python -B archive/2026-11-21-gaussian-pinch-v001/central_detours.py
~~~

This recomputes the signed norm coefficients through $2^{25}$, uses 96-bit Arb interval arithmetic, and compares every field against the [archived certificate](central-detours.json). The normalization is the $B^s$ completion given at the top of this note. The coordinate $h$ is the displacement from $1/2$ before any display rescaling.
