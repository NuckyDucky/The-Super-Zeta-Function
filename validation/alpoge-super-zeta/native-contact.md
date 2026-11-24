# The two native Dottie corrections at the same zeta zero

I keep the two rooted words of the paired return in chronological order. With $L=iy$, the $P$ origin reads $(-+)^{320}$ and the $Q$ origin reads $(+-)^{320}$. The two return multipliers at the paired cap $(p,\overline p)$ are conjugate. At the first archived crossing $y\approx0.50989298281412392858$, their native angles are $a=-\pi/6$ and $a=+\pi/6$, respectively. The second archived crossing reverses that assignment. Those angles mark the characteristic spectra used here. The argument below holds each angle fixed while varying the same spectral input $s$. [Ordered stages and lifts](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean/SuperZeta/Oriented/OrderedStages.lean#L130) · [448-bit crossing record](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/archive/2026-11-19-oriented-return-v001/data/orbit_crossing.json) · [Lean origin exchange](NativeDottieOrigin.lean)

## From the ordered return to the spectral readings

Write $F_\pm(v)$ for the two native determinants and use the archived convention $v=u^2$, $\phi=-a$, and the positive characteristic sign. If $f_\phi(u)=u-\cos(u-\phi)$, then $F_\pm(u^2)=f_\phi(u)f_\phi(-u)/\cos^2\phi$. The common reference $F_{\mathrm{ref}}$ uses the product of the two cosine terms. On $v=-x^2$, for real $x>0$, I get

$$
F_{\mathrm{ref}}(-x^2)=1+\frac43\sinh^2 x,\qquad
F_\pm(-x^2)=F_{\mathrm{ref}}(-x^2)+\frac43(x^2\pm x\sinh x).
$$

All three values are positive. $F_-<F_{\mathrm{ref}}<F_+$ on this ray. In the determinant coordinate, the exact difference is $F_-(u^2)-F_+(u^2)=\tfrac83 u\sin u$. The two native determinants have disjoint zero sets. [Original marked determinant and canonical product](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/archive/2026-11-19-oriented-return-v001/README.md#the-two-trace-inverse) · [Lean ray calculation](NativeDottieRay.lean)

For these determinants put $K_\pm(x)=\log(F_\pm(-x^2)/F_{\mathrm{ref}}(-x^2))$. The continuation of their Mellin corrections is entire and agrees on $\Re s<1$ with

$$
J_\pm(s)=\frac{2s\sin(\pi s)}{\pi}
          \int_0^\infty x^{-2s-1}K_\pm(x)\,dx .
$$

At zero, $K_\pm(x)$ has an even Taylor series starting in degree two. The degree-two coefficients are $0,8/3$, respectively. The Taylor subtraction in the continuation removes the integration singularity at $s=1$ against the sine zero there. Thus $J_-(1)=0$ and $J_+(1)=8/3$. The actual reciprocal-root sums at $s=1$ are $4/3$ and $4$. On the whole positive ray, $|K_\pm(x)|\le(128/9)e^{-x/2}$. [Lean continuation, values and tail bound](NativeDottieMellin.lean) · [First reciprocal-root values](NativeDottieOrigin.lean)

### Identification with the native root series

I take each squared zero $v_j$ once, since the native determinants have simple roots and their normalized genus-zero products are known. To justify the Mellin identity directly for the series, let $u$ be a characteristic root with $u^2=v_j$, choosing whichever sign of the square root solves $u=\cos(u-\phi)$. With $u=p+iq$,

$$
|u|^2=\cos^2(p-\phi)+\sinh^2 q .
$$

If $|q|\ge2$, then $\sinh |q|=2\sinh(|q|/2)\cosh(|q|/2)\ge \sqrt2\,|q|$. If $|q|<2$ and $|v_j|\ge8$, then $|u|^2\ge8>2q^2$. In either case $|v_j|\ge8$ implies $\Re v_j=|u|^2-2q^2\ge0$. The other roots form a finite set and avoid the closed nonpositive real axis by the ray positivity. Thus a single $d>0$ satisfies $|t+v_j|\ge d(t+|v_j|)$ for every $t\ge0$ and $j$. For example take the minimum of $1/\sqrt2$ and the finitely many $\cos(\arg v_j/2)$ for $|v_j|<8$.

The finite-disk count of the original determinants gives $2^N\le\exp(K(1+\sqrt{2r}))$ for $N$ roots with $|v_j|\le r$, by comparing on the circle of radius $2r$. Hence $N(r)=O(\sqrt r)$ and the sum of $|v_j|^{-\sigma}$ converges for $\sigma>1/2$. For $1/2<\Re s<1$, the Stieltjes formula for $v_j^{-s}$ on the principal branch can therefore be summed under the integral. In absolute value each integral is at most a constant times $|v_j|^{-\Re s}$, by the uniform lower bound just proved. The canonical product differentiates on the ray to $\sum_j 1/(t+v_j)$ because the reciprocal norms are summable and the ray has no roots. [Original zero count](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean/SuperZeta/Oriented/GrowthCount.lean#L52) · [Stieltjes sum and sector inequality](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean/SuperZeta/Ray.lean#L120)

For the reference ray,
$
F_{\mathrm{ref}}(-x^2)=\sinh(3x)/(3\sinh x)
$.
Euler's product for each hyperbolic sine shows that after division only the factors for integers $k\ge1$ with $3\nmid k$ remain, at squared values $(\pi k/3)^2$. The sums are absolutely convergent on the same strip. Subtract the reference resolvent from the native resolvent and integrate by parts in $t=x^2$. The boundary terms $t^{-s}K_\pm(\sqrt t)$ tend to zero at both ends, by the degree-two bound at zero and the exponential bound at infinity. The remaining integral is exactly $J_\pm(s)$. This gives the continuation of the actual root series, initially from $1/2<\Re s<1$, as

$$
Z_\pm(s)=R(s)+J_\pm(s),\qquad
R(s)=\pi^{-2s}(3^{2s}-1)\zeta(2s).
$$

The two thirds in the reference exchange under the origin swap. Their sum $R(s)$ stays the same. [Euler product implementation for the cosine reference](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean/SuperZeta/ReferenceProduct.lean) · [Lean thirds identity](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean/SuperZeta/Oriented/LiuConnection.lean#L97)

## What the two comparisons read

If $w_0=2s_0$ is a zeta zero of finite order $m$ with $0<\Re s_0<1/2$, Lean gives a single analytic function $U$ with $U(s_0)\ne0$ and both expansions

$$
Z_\pm(s)=J_\pm(s)+(s-s_0)^mU(s).
$$

Subtracting the raw readings keeps $J_+-J_-$ and erases the whole common germ, including its order. The corrected readings $Z_\pm-J_\pm$ are equal pointwise. Their log derivatives agree, so subtracting them erases the pole for the shared zero order as well. If both $J_\pm(s_0)\ne0$, the raw log derivatives are regular there. [Lean same-input expansion and slope checks](NativeDottieContact.lean)

To keep the shared term I compare each word against its own correction. The cross-product is

$$
J_-(s)Z_+(s)-J_+(s)Z_-(s)=(J_-(s)-J_+(s))R(s).
$$

If the corrections differ at $s_0$, the right-hand coefficient is an analytic unit there and the cross-product preserves the full order $m$. Where the denominators are nonzero this is the difference $Z_+/Z_--J_+/J_-$, up to division by $Z_-J_-$. The cross-product uses the actual native correction functions as readouts. The earlier comparison uses the two rooted stage values as weights on an ordinary and a character logarithmic slope. [Lean cross-product and zero order](NativeDottieContact.lean) · [Earlier ordered slope recovery](ordered-contact.md)

## First-zero readings

I evaluate the two complex columns at the same input $s_0=\tfrac14+7.067362570867346895\ldots i$. The values below are rounded. The saved output keeps complex interval radii for the values, slopes and differences. Derivatives are with respect to $s$.

| Native angle | $J_\pm(1)$ | $Z_\pm(s_0)=J_\pm(s_0)$ | $J_\pm'(s_0)$ |
| --- | ---: | ---: | ---: |
| $-\pi/6$ | $0$ | $11626.09571546-6163.88746659i$ | $-29495.50187621-5182.04602983i$ |
| $+\pi/6$ | $8/3$ | $1848.18105415+355.87188126i$ | $-4536.47773607-2945.63068778i$ |

The common slope is $R'(s_0)\approx2.21589777727-1.01193660889i$. The raw contrast at the zero is about $-9777.91466131+6519.75934786i$. The ratio $J_+(s_0)/J_-(s_0)$ is about $0.11142076131+0.08968246443i$, and the derivative of the ratio gap is about $0.00016518922019-0.00000685572122i$. The 256-bit Arb run excludes zero from the contrast and the ratio-gap derivative. The interval calculation uses the first zeta zero from Arb and integrates the native determinant kernels, including analytic bounds on both tails. [Interval output](native-zero-output.txt) · [Replay with python-flint 0.9.0](check_native_dottie_zero.py)

The Lean replay checks the ray and determinant identities, the Mellin continuation from the actual kernels, the first root-sum values, and the same-input and cross-product expansions. The root-series identification on the open convergence strip is the written Stieltjes argument above. The cap crossing and the quoted first-zero enclosures have their own interval records. [Lean build and axiom audit](native-lean-audit.txt) · [Replay instructions](replay-native.ps1)

From the repository's `lean` directory, build the imports and run the packet with the toolchain pinned in `lean-toolchain`.

```powershell
lake exe cache get
lake build +SuperZeta.Oriented.SpectralInverse:olean +SuperZeta.Oriented.FirstCorrection:olean +SuperZeta.Oriented.LiuConnection:olean +SuperZeta.MellinContinuation:olean +SuperZeta.Multiplicity:olean
$lean419 = (elan which lean).Trim()
& ../validation/alpoge-super-zeta/replay-native.ps1 -LeanExecutable $lean419 -SuperZetaLibrary .lake/build/lib/lean -MathlibPackages .lake/packages
```

Run `python check_native_dottie_zero.py` from the packet with `python-flint==0.9.0` to reproduce the interval record.
