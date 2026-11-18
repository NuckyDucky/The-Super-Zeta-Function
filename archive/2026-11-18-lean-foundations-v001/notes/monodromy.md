# Quantified branch transport and recovery of the ordered fixed-pair germ

This continuation adds two explicit complex continuation domains to the 2024 inverse-function framework and transports Nick's actual ordered phases and affine-normalized germs around them. It also extends the parabolic coefficient-field recovery to every fixed-point germ with a nonzero quadratic coefficient.

The principal result is a pair of certified two-sheet neighborhoods: an \(L\)-disk of radius \(10^{-7}\) at Dottie and an eccentricity disk of radius \(10^{-8}\) at the Laplace point. The two loops have distinct observable actions. The Dottie loop exchanges the attracting and repelling fixed pairs at one parameter. The Laplace loop exchanges two different real parameters realizing the same multiplier, and the cubic/quartic germ coefficients distinguish those branches.

## 1. Coordinates and constants

Retain the global reciprocal fixed-pair coordinate

\[
\varepsilon(u)=u\sec u,\quad a(u)=u\tan u,\quad
L(u)=i\varepsilon(u)e^{-a(u)},
\]
\[
P(u)=e^{a(u)+iu},\quad Q(u)=e^{a(u)-iu},\quad
U=LQ=a+iu,\quad V=-LP=a-iu,\quad
\mu=UV=\varepsilon^2.
\tag{1}
\]

The ordered pair satisfies \(P=e^{LQ},Q=e^{-LP}\). Its scalar return is \(g_L(z)=\exp(Le^{-Lz})\), fixed at \(P\), with multiplier \(\mu\).

Let \(d=\cos d\), \(0<d<1\), \(s=\sin d\), and

\[
L_D=ie^{-s},\qquad u_D=d.
\]

Let \(v_*>0\) solve \(v_*\tanh v_*=1\), and put

\[
R=\frac{v_*}{\cosh v_*},\qquad
u_K=iv_*,\qquad \varepsilon_K=iR,\qquad L_K=-eR.
\]

We use a large holomorphic radius \(R_0=1/5\) and an isolating radius \(r=1/2000\) in the \(u\)-coordinate.

## 2. The quantified two-sheet theorem

**Theorem 1.** The following two local maps are proper branched covers of degree two over the stated parameter disks, with exactly one simple critical point in their selected \(u\)-neighborhoods:

| Projection | Center in \(u\) | Parameter center | Parameter radius |
|---|---|---|---:|
| \(u\mapsto L(u)\) | \(d\) | \(L_D\) | \(10^{-7}\) |
| \(u\mapsto\varepsilon(u)\) | \(iv_*\) | \(iR\) | \(10^{-8}\) |

In each row, select the preimage contained in \(|u-u_0|<r\). Every parameter value in the disk has exactly two preimages counted with multiplicity; only the center is a critical value. The strict margins below give an open extension beyond the **closed** disks of the stated radii, so the circular loops drawn on their boundaries are inside the certified continuation domain. A continuation loop in the punctured parameter disk with winding number one exchanges the two roots. Winding number two returns each root and every single-valued function of \(u\) to its initial value.

### Proof: explicit majorants

Arb verifies the real root brackets

\[
0.73908<d<0.73909,\qquad 1.199<v_*<1.200.
\]

Uniqueness follows from the monotonicity of \(\cos x-x\) on \((0,1)\), and of \(v\tanh v\) on \((0,\infty)\). These brackets imply

\[
0.673<s<0.674,\qquad e^{-0.674}>0.509,
\quad e^{-0.673}<0.511.
\]

For \(|h|\le R_0\), the Taylor coefficients of sine and cosine at real \(d\) have absolute values at most one. Hence their variation is at most \(e^{R_0}-1<0.222\). On the large Dottie disk,

\[
|u|<0.940,\quad |\cos u|>0.517,\quad |\sin u|<0.896.
\]

Consequently

\[
|\varepsilon|<11/6,\qquad |a|<5/3,\qquad |L|<10.
\tag{2}
\]

For the large disk about \(iv_*\), the same Taylor estimate uses the bound \(\cosh(1.2)<2\) on the sine/cosine derivatives at its center. It gives

\[
|u|<1.4,\quad |\cos u|>1.356,\quad |\sin u|<1.954,
\]

and thus

\[
|\varepsilon|<11/10,\qquad |a|<21/10,\qquad |L|<10.
\tag{3}
\]

Both large disks are holomorphic domains for all functions in (1).

At Dottie,

\[
L'(d)=0,\qquad
c_D=\frac{L''(d)}2=-L_D\frac{1+s}{d^2},\qquad
\frac32<|c_D|<\frac85.
\]

At the Laplace point,

\[
\varepsilon'(iv_*)=0,\qquad
c_K=\frac{\varepsilon''(iv_*)}2=\frac{iR}{2},\qquad |c_K|>\frac3{10}.
\]

For either map \(F\), write \(F(u_0+h)-F(u_0)=ch^2+T(h)\), and let \(M\) bound \(|F|\) on the large disk. With \(q=r/R_0=1/400\), Cauchy's inequality yields

\[
|T(h)|\le \frac{Mq^3}{1-q},\qquad
|T'(h)|\le\frac{M}{R_0}\frac{q^2(3-2q)}{(1-q)^2}
\quad(|h|\le r).
\tag{4}
\]

The exact rational root-count margins
\(|c|_{\rm lower}r^2-|T|-\rho\), with the chosen parameter radius \(\rho\), are respectively

\[
\frac{1889}{15960000000}>0,
\qquad \frac{953}{19950000000}>0.
\]

The exact derivative margins \(2|c|_{\rm lower}r-|T'|\) are

\[
\frac{178103}{318402000}>0,
\qquad \frac{156439}{796005000}>0.
\]

Rouché's theorem therefore counts two roots of \(F(u)-w\) and one root of \(F'(u)\) in each isolating disk, for every parameter \(w\) in its stated closed disk. If the positive root-count margin is \(m\), the same conclusion holds in the open parameter disk of radius \(\rho+m/2\). The known central critical point is simple and is the unique one. The same strict boundary margins make the restricted map proper. Its central fiber consists of the double root \(u_0\), so its preimage component has degree two. Its local square-root monodromy is the transposition, and the unique-critical-value property transports that monodromy throughout the punctured parameter disk. ∎

The root counts and critical-point isolation use exact rational inequalities. Arb is used for the elementary exponential/trigonometric bracket decisions; their precision is 512 bits.

## 3. The ordered phases and lifted logarithms stay in explicit analytic domains

The same Cauchy bounds give, throughout the small \(u\)-disks,

\[
|U-U_D|,|V-V_D|<\frac1{200}
\quad\text{at Dottie},
\]

\[
|U-U_K|,|V-V_K|<\frac3{500}
\quad\text{at Laplace}.
\tag{5}
\]

Here \((U_D,V_D)=(s+id,s-id)\), while \((U_K,V_K)=(-1-v_*,-1+v_*)\). Also

\[
|\mu-\mu_D|<1/100,\qquad
|\mu-\mu_K|<1/100,
\quad \mu_D=1,\quad\mu_K=-R^2.
\tag{6}
\]

For example, the exact Dottie logarithm deviation bound is \(11197/2394000<1/200\); the Laplace bound is \(219/38000<3/500\). Relative phase deviations are bounded by \(e^{1/200}-1\) and \(e^{3/500}-1\), respectively, because \(P/P_0=e^{U-U_0}\) and \(Q/Q_0=e^{V-V_0}\).

These bounds keep \(U,V,\mu,L\) nonzero and keep \(U+1\) nonzero. Consequently the actual lifted logarithms and the prescribed affine germ normalization continue holomorphically throughout both selected covers.

## 4. Generic coefficient recovery and its transport

**Theorem 2.** Let \(L\ne0\), let \((P,Q)\) be a reciprocal fixed pair, and suppose \(U=LQ\ne-1\). Set \(V=-LP\), \(\mu=UV\). Define

\[
b=\frac{g_L''(P)}2=-\frac{\mu L(1+U)}2,
\qquad
G(x)=b\left[g_L\left(P+\frac xb\right)-P\right].
\]

Then the affine-normalized germ has

\[
\boxed{G(x)=\mu x+x^2+\sum_{n\ge3}c_nx^n,\qquad
c_n=\mu^{2-n}h_n(U),}
\tag{7}
\]

where

\[
h_n(U)=\frac{2^{n-1}T_n(U)}{n!U(1+U)^{n-1}}
\]

and \(T_n\) is the Touchard polynomial. The first, cubic and quartic coefficients recover both actual lifted logarithms rationally:

\[
\boxed{\mathbb Q(\mu,c_3,c_4)=\mathbb Q(U,V).}
\tag{8}
\]

For fixed known \(L\), they also recover the ordered phases rationally:

\[
\boxed{\mathbb Q(L,\mu,c_3,c_4)=\mathbb Q(L,P,Q).}
\tag{9}
\]

**Proof.** The exact translated return is

\[
g_L(P+h)-P=P\left[e^{U(e^{-Lh}-1)}-1\right].
\]

Its \(n\)-th coefficient is \(P(-L)^nT_n(U)/n!\). Substitution of \(b=-\mu L(1+U)/2\), using \(PLU=-\mu\), gives (7). In particular \(h_3=\mu c_3\), \(h_4=\mu^2c_4\).

Write

\[
\varrho=1-\mu c_3,\qquad
w=\frac{24\mu^2c_4-22+42\varrho}{6\varrho-2}.
\]

The rational identities already available for the normalized Touchard germ give

\[
\boxed{U=\frac{1+w}{1-w},\qquad V=\frac\mu U.}
\tag{10}
\]

Their denominators are nonzero since \(6\varrho-2=-4U/(1+U)^2\), \(1-w=2/(1+U)\), and \(U\ne0,-1\). Every \(c_n\) is rational in \(U,V\), proving (8). Finally \(Q=U/L\), \(P=-V/L\), giving (9). ∎

At \(\mu=1\), this specializes to the parabolic coefficient-field recovery. Equation (7) extends that recovery to the generic affine-normalized fixed-point germ and makes its whole coefficient sequence transportable along the certified loops. These coefficients refer to the displayed affine normalization.

**Corollary (entire-map and finite-orbit reconstruction).** The fourth-order Taylor jet \((\mu,1,c_3,c_4)\) determines the entire affine-normalized return through

\[
\boxed{G(x)=\frac{\mu^2(1+U)}{2U}
\left[\exp\!\left(U\left(e^{2x/[\mu(1+U)]}-1\right)\right)-1\right],}
\tag{11}
\]

where \(U\) is recovered rationally by (10). Thus it determines every finite normalized iterate and orbit in this prescribed coordinate. Explicitly, for every integer \(n\ge0\),

\[
\boxed{G^{\circ n}(x)=b\left[g_L^{\circ n}\left(P+\frac xb\right)-P\right].}
\tag{12}
\]

**Proof.** Substitute \(b=-\mu L(1+U)/2\) into the exact translated return and use \(bP=\mu^2(1+U)/(2U)\). This gives (11) as an identity of entire functions. Equation (12) follows by induction from the affine conjugacy. ∎

The full original fixed triple is recovered analytically through \(V=\mu/U\), \(L=Ue^{-V}\), \(P=e^U\), \(Q=e^V\). The rational field equalities remain exactly (8)–(9). This makes the coefficient data an explicit route from a finite local jet to the selected finite-orbit problem.

## 5. Two explicit loops and their dynamical actions

### Dottie: same parameter, attracting/repelling exchange

Start at

\[
L_0=L_D-i10^{-7}
\]

and follow the counterclockwise loop

\[
L(\theta)=L_D-i10^{-7}e^{i\theta},\qquad0\le\theta\le2\pi.
\]

The two preimages at \(\theta=0\) are real, one on each side of \(d\). Indeed \(\varepsilon(u)\) is strictly increasing there, and \(Y(u)=L(u)/i\) increases to its strict maximum at \(d\) and decreases afterward. The boundary estimate in Theorem 1 places one real solution on each side, exhausting the two-root count. Their multipliers satisfy

\[
\mu_-<1<\mu_+.
\]

One loop sends the ordered fixed pair \((P_-,Q_-)\) to \((P_+,Q_+)\), its actual \((U_-,V_-)\) to \((U_+,V_+)\), and every affine-normalized coefficient \(c_{n,-}\) to \(c_{n,+}\). Two loops return the complete data. Thus a certified continuation exchanges the attracting and repelling branches at the same centerline parameter.

Numerically, the two starting roots and multipliers are

\[
u_-\approx0.73883210237635181927,\quad
u_+\approx0.73933812515803262541,
\]
\[
\mu_-\approx0.99885471130196334387,\quad
\mu_+\approx1.00114642553140137389.
\]

### Laplace: same multiplier, exchange across its sharp real maximum

Start at \(\varepsilon_0=i(R-10^{-8})\), and follow

\[
\varepsilon(\theta)=iR-i10^{-8}e^{i\theta},\qquad0\le\theta\le2\pi.
\]

Its two initial preimages are imaginary, \(u_\pm=iv_\pm\), with \(v_-<v_*<v_+\). They give two distinct negative real parameters, since

\[
|L|=\frac v{\cosh v}e^{v\tanh v}
\]

is strictly increasing with \(v>0\). Hence

\[
|L_-|<eR<|L_+|,
\qquad\mu_- =\mu_+=-(R-10^{-8})^2.
\]

One loop exchanges these two parameter–fixed-pair data at the same eccentricity and multiplier. Their joint cubic/quartic germ data are distinct: equality of both coefficients at the common \(\mu\) would recover the same \(U,V\) by (10), hence the same \(u\), contrary to the two distinct roots.

Numerically,

\[
L_-\approx-1.80114797812161606289,\qquad
L_+\approx-1.80189886949648344900,
\]

with common multiplier \(-0.43922882663577686379\ldots\). The cubic coefficients are approximately \(0.8030460930769559\) and \(0.8008964762004116\), respectively.

## 6. Verification and source position

The script `verify_monodromy.py` writes `monodromy-results.json`. It performs:

- 512-bit Arb checks of the real brackets and elementary majorants.
- Exact rational Rouché root and derivative margins for both covers.
- Symbolic rational recovery of \(U\) from \(\mu,c_3,c_4\).
- Two complete counterclockwise turns for each loop, with 128 continuation steps per turn, at 110 and 190 decimal digits.
- Independent fixed-pair identities, multiplier identities, affine germ derivatives through order four, coefficient recovery, one-loop exchange and two-loop return checks.
- Exact symbolic verification of the reconstructed entire function, followed by six finite iterates from \(x_0=0.001+0.0007i\), compared against direct original-map iteration and affine conversion on both branches of both selected fibers.

The recorded states agree to 80 decimal places across the two precisions. The numerical loops illustrate the analytical covering theorem; its explicit root/critical-point counts supply the continuation certificate. Full trajectories sampled every eight steps are saved for plotting.

The standalone `verify_marked_cap.py` applies the entire-map reconstruction to the actual marked cap \(z_0=1\) at Nick's canonical Dottie-spire `tab:windows` midpoints: the exact printed rationals \(y=0.5098930698771419799831,\ 0.5098929835386691077069,\ 0.5098928862668716592052\), with source paired periods \(639,640,641\) and scalar periods \(639,320,641\). For each \(L=iy\), on both computed local fixed-point sheets, it computes the normalized cubic/quartic coefficients from derivatives of the original map, recovers \(U\) rationally by (10), and iterates (11) from \(x_0=b(1-P)\). Every iterate through the stated scalar period is compared with \(b[g_L^{\circ n}(1)-P]\), using 180 and 280 decimal digits. All 3,200 normalized iterates per precision pass the \(10^{-100}\) absolute-error threshold. The largest transport errors are \(9.545\times10^{-174}\) at 180 digits and \(1.147\times10^{-273}\) at 280 digits; the 1,600 original cap iterates agree across precisions within \(2.359\times10^{-172}\). `marked-cap-results.json` records the two sheets, endpoints, derivative/jet recovery residuals and every-iterate error maxima. These are high-precision point calculations at the three exact rational midpoints; the canonical source supplies the interval capture certificates and period data.

Stoutemyer's [2024 inverse-spherical-Bessel paper](https://mapletransactions.org/index.php/maple/article/download/16787/16573/55313) supplies the published inverse-family and branch-extremum framework. Nick's existing work supplies (1), the Dottie fold and the normalized Touchard germ. The continuation here supplies the two explicit complex isolating covers, the all-order generic germ transport, and the rational recovery of the complete ordered lifted pair from its affine-normalized coefficients. Borghi's [2024 Kepler paper](https://www.mdpi.com/2227-7390/12/1/154) supplies the computational inverse-function context used by the companion approximation branch of this research.
