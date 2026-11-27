# The native Dottie correction gap on higher disks

Let $W(s)=J_-(s)-J_+(s)$ for the native angles $-\pi/6$ and $+\pi/6$. The corresponding ordinary input is always $w=2s$. The first closed spectral disk, centered at $1/4+7.067363i$ with radius $1/4096$, has the Lean bound $|W(s)|>11600$. The higher bounds below use a written analytic proof with directed Arb numerical enclosures. [Native correction definitions](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/c3cba864dadd284d3bc3d33a3b9fae13d065e6d7/validation/alpoge-super-zeta/native-contact.md) · [First-disk Lean theorem](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/c3cba864dadd284d3bc3d33a3b9fae13d065e6d7/validation/alpoge-super-zeta/FirstDottieCrossCertificate.lean) · [First-disk audit](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/c3cba864dadd284d3bc3d33a3b9fae13d065e6d7/validation/alpoge-super-zeta/native-dottie-cross-audit.txt)

| Landing | Exact spectral center | Gap lower bound at spectral radius $5\cdot10^{-9}$ | Gap lower bound at spectral radius $1/4096$ |
| --- | --- | ---: | ---: |
| [Second ordinary zero](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/c3cba864dadd284d3bc3d33a3b9fae13d065e6d7/archive/2026-11-19-zero-transport-v001/Dottie-Second-Zero/dyadic_identification.json) | $1/4+10.511019819385777495i$ | $1{,}702{,}200$ | $1{,}699{,}800$ |
| [Third ordinary zero](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/c3cba864dadd284d3bc3d33a3b9fae13d065e6d7/archive/2026-11-19-zero-transport-v001/Dottie-Third-Zero/identification_1.json) | $1/4+12.5054287900728444i$ | $28{,}273{,}600$ | $28{,}233{,}500$ |

All lower bounds are strict on the closed disks. The first radius is the archived ordinary radius $10^{-8}$ divided by two. The second radius copies the spectral radius of the first native gap certificate, with centers at the archived rounded heights. The replay verifies that each disk contains its corresponding zeta zero under $w=2s$.

The rotated ray gives
$$
  |W(w/2)|>\frac{e^{7\Im(w)/10}}{12}
  \qquad (0\le\Re w\le1,\quad \Im w\ge 100).
$$
On the entire ordinary disk centered at $3/4+100000001i$ with radius $31/128$, this gives $|W|>e^{70000000}/12$. The spectral center is $3/8+50000000.5i$ and the spectral radius is $31/256$. The ordinary disk lies in $65/128\le\Re w\le127/128$ and $\Im w\ge100000000+97/128$. [Archived ordinary disk](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/c3cba864dadd284d3bc3d33a3b9fae13d065e6d7/validation/dottie-score/dedekind-mixed-theta/weighted-cayley-circle.md)

On these disks the cross-product $J_-Z_+-J_+Z_-$ has the same zeros, with the same orders, as $\zeta(w)$. Its multiplier $W(w/2)\pi^{-w}(3^w-1)$ is nonzero there by the gap bound and $\Re w>0$. [Same-input cross-product and order transfer](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/c3cba864dadd284d3bc3d33a3b9fae13d065e6d7/validation/alpoge-super-zeta/NativeDottieContact.lean)

## Native gap and moderate heights

The determinants on the ray, with a common factor three, and their log ratio are
$$
  D_\pm(x)=3+4(\sinh^2 x+x^2)\pm4x\sinh x,\qquad
  L(x)=\log\frac{D_-(x)}{D_+(x)}.
$$
Here the minus sign labels the angle $-\pi/6$. For $\Re w<2$, the Mellin identity gives
$$
  W(w/2)=\frac{w\sin(\pi w/2)}{\pi}M(w),\qquad
  M(w)=\int_{-\infty}^{\infty}e^{-wu}L(e^u)\,du.
$$
The Lean bounds for each kernel give $|L(e^u)|\le (32/3)e^{2u}$ for $u\le0$ and $|L(e^u)|\le (256/9)e^{-e^u/2}$ for $u\ge0$. [Lean small and large kernel bounds](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/c3cba864dadd284d3bc3d33a3b9fae13d065e6d7/validation/alpoge-super-zeta/NativeDottieMellin.lean)

The moderate-height replay encloses the six coefficients
$$
  m_k=\frac1{k!}\int_{\mathbb R}(-u)^k e^{-wu}L(e^u)\,du,
  \qquad 0\le k<6 .
$$
On $[-45,6]$ it integrates analytic balls on panels of width three, with the logarithm's branch test enabled on complex neighborhoods. It rewrites the same ratio as $(A-B)/(A+B)$, using $b=e^{-x}$, $A=1+(1+4x^2)b^2+b^4$ and $B=2x(b-b^3)$.

For $\sigma=\Re w$, put $\alpha=2-\sigma$. The negative omitted tail of $m_k$ is bounded by
$$
  \frac{32}{3}e^{-45\alpha}
  \sum_{j=0}^{k}\frac{45^j}{j!\alpha^{k+1-j}}.
$$
For $u\ge6$, $e^u/2\ge e^6/4+u$. Integrating the resulting positive tail majorant, extended to $u\ge0$ after removing the factor $e^{-e^6/4}$, gives the bound $(256/9)e^{-e^6/4}/(1+\sigma)^{k+1}$.

For an ordinary disk $|h|\le r$ about the evaluation center $w$, the pointwise exponential remainder after $n$ terms is at most $e^{r|u|}(r|u|)^n/n!$. On $u\ge0$, the bound $e^u/2\ge u$ follows from $e^u\ge1+u+u^2/2$. The difference between $M(w+h)$ and $\sum_{k=0}^{n-1}h^km_k$ therefore has modulus at most
$$
  r^n\left(\frac{32}{3(2-\sigma-r)^{n+1}}
       +\frac{256}{9(1+\sigma-r)^{n+1}}\right).
$$
The reverse triangle inequality gives a positive lower bound for $|M(w+h)|$. The prefactor has modulus at least $T\sinh(\pi T/2)/\pi$, where $T=\Im w-r>0$. This proves the table using $n=6$.

## The pole between two rays

Define
$$
  G(x)=D_-'(x)/D_-(x)-D_+'(x)/D_+(x),\qquad
  Q(w)=\int_0^\infty x^{-w}G(x)\,dx .
$$
Since $L'=G$ on the real ray, integration by parts with the two kernel bounds gives $M(w)=Q(w)/w$ for the inputs here. In particular $W(w/2)=\sin(\pi w/2)Q(w)/\pi$.

Write $a=\pi/6$. With $u=ix$, $D_-$ and $D_+$ are proportional to $f_\phi(u)f_\phi(-u)$ for $\phi=a$ and $\phi=-a$, respectively, where $f_\phi(u)=u-\cos(u-\phi)$. The fourth quadrant in $x$ gives $u=p+iq$ with $p,q>0$. A zero of either factor satisfies $u=\epsilon\cos(u-\epsilon\phi)$ for one of $\epsilon=1,-1$. Its real and imaginary equations give
$$
  p=\epsilon\cos(p-\epsilon\phi)\cosh q,\qquad
  q=-\epsilon\sin(p-\epsilon\phi)\sinh q.
$$
Set
$$
  \beta(q)=\arcsin(q/\sinh q),\qquad
  X(q)=\cosh q\cos\beta(q),\qquad h(q)=X(q)+\beta(q).
$$
Thus $p=X(q)$. For $\epsilon=1$ the phase $p-\phi$ equals $-\beta+2\pi k$, so $h(q)=\phi+2\pi k$. For $\epsilon=-1$ the phase $p+\phi$ equals $\pi-\beta+2\pi k$, so $h(q)=\pi-\phi+2\pi k$.

The function $\beta$ decreases because $q/\sinh q$ decreases. Also $\cosh q\sin\beta=q\coth q>1$. Consequently
$$
  h'(q)=\sinh q\cos\beta+(1-\cosh q\sin\beta)\beta'(q)>0 .
$$
Its limits are $\pi/2$ at zero and $+\infty$ at infinity. The least two phase targets above $\pi/2$ are $5\pi/6$ for $D_-$ and $7\pi/6$ for $D_+$. The angle below the real ray, $\arctan(X(q)/q)$, is strictly increasing in $q$. Indeed
$$
  \frac{X(q)}q
  =(q\coth q)\frac{\sqrt{\sinh^2q-q^2}}{q^2}.
$$
The derivative of $q\coth q$ is positive by $\sinh(2q)>2q$. The square of the second factor is a power series with positive coefficients, including strictly positive coefficients at positive powers of $q^2$. These facts order all fourth-quadrant determinant poles by phase target. The derivative $1+\epsilon\sin(u-\epsilon\phi)$ of the corresponding characteristic factor has imaginary part $p\tanh q>0$, so each is a simple zero. The phase targets for the different factors are disjoint.

Arb brackets the first two solutions to $h(q)=5\pi/6,7\pi/6$ in $(1.58722,1.58723)$ and $(1.98299,1.98300)$, respectively. The first zero $x_0$ has $\delta=-\arg x_0$ in $(0.86797,0.86798)$, the next angle exceeds $0.99803$, and the ray
$$
  x=(1-4i/3)y,\qquad y>0,\qquad
  \theta=\arctan(4/3)
$$
has angle $-\theta$ between them. The arithmetic also gives $|x_0|<3$, $\theta-\delta>1/20$, and $\pi/2-\delta>7/10$. The first pole of $G$ consequently has residue $+1$, and the clockwise rotation crosses precisely this pole.

## Uniform error on the rotated ray

On $x=(1-4i/3)y$ the modulus of $x^{-w}\,dx$ is
$$
   (5/3)^{1-\sigma} y^{-\sigma} e^{-\theta t}\,dy,
   \qquad \sigma=\Re w,\quad t=\Im w.
$$
The constant in front of $y^{-\sigma}e^{-\theta t}$ is at most $5/3$ for $0\le\sigma\le1$.

For $0\le y\le1/8$ we have $|x|\le1/4$. The power series give $|\sinh x|\le2|x|$ and $|\cosh x|\le2$ there. Hence $|D_\pm-3|\le28|x|^2$, $|D_\pm'|\le56|x|$, and $|G|\le112|x|$. Since $|x|=(5/3)y$ and $y^{1-\sigma}\le1$, the contribution to $\int y^{-\sigma}|G|\,dy$ is at most $70/3$.

For $y\ge16$, use the scaled determinants $P_\pm=e^{-2x}D_\pm=A\pm B$, with $A,B$ as above, and $|x|\le2y$, $|b|=e^{-y}$. The expansion gives
$$
  |P_\pm-1|\le (16y^2+8y+2)e^{-y}<1/2,\qquad
  |P_\pm'|\le(32y^2+32y+10)e^{-y}.
$$
The first polynomial times $e^{-y}$ is decreasing on this range and its value at $16$ is less than $1/2$ using $e>2$. The log derivatives of $P_\pm$ differ by $G$, so
$$
  \int_{16}^\infty y^{-\sigma}|G|\,dy
  \le4(32(16^2+2\cdot16+2)+32(16+1)+10)e^{-16}<1 .
$$
The small bound also applies uniformly on the inner circular arc in the sector. The large bound applies on the outer arc, since there $|x|\le(5/3)\Re x$ and $\Re x$ grows uniformly with the radius. The arc integrals therefore vanish in the limits at zero and infinity.

The medium part $1/8\le y\le16$ uses 2,032 closed intervals of width $1/128$. The replay encloses both $P_\pm$ and their complex derivatives on the image of every interval, verifies both denominators are separated from zero, and bounds $|G|$. The weight $y^{-\sigma}$ is bounded by $1/y$ below one and by one above one. The final interval upper bound for this part is about $14.02865$. Adding the end bounds and the $5/3$ factor gives a checked bound under $64$ for the entire ray constant.

The residue theorem using the principal power in the sector now gives
$$
  Q(w)=-2\pi i\,x_0^{-w}+E(w),\qquad |E(w)|<64e^{-\theta t}.
$$
For $t\ge100$, $e^{(\theta-\delta)t}>e^5>64$, so $|E(w)|<e^{-\delta t}$. The pole has magnitude $2\pi |x_0|^{-\sigma}e^{-\delta t}>(2\pi/3)e^{-\delta t}$. The reverse triangle inequality gives $|Q(w)|>(\pi/3)e^{-\delta t}$. Finally, $|\sin(\pi w/2)|\ge\sinh(\pi t/2)>e^{\pi t/2}/4$, which proves the stated bound for $|W(w/2)|$.

## Replay

Run the two Python files with python-flint 0.9.0 and assertions enabled. Each uses one worker. The moderate check uses 192 bits and the rotated-ray check uses 128 bits. The saved runs are in the [interval output](interval-output.txt).

~~~text
python -B check_moderate_disks.py
python -B check_rotated_ray.py
~~~
