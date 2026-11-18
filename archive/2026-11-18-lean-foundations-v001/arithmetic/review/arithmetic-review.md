# Independent arithmetic audit: PARI rank, Selmer and two-primary Sha interpretation

**16 November 2026.** I inspected the exact curve, GP commands, retained cover basis, point arithmetic and report; read the official GP specifications; and replayed the arithmetic verification headlessly. The replay passed in approximately 0.090 seconds. The mathematical interpretation below agrees with the retained PARI output.

## Inputs and replay

The curve is

\[
E:y^2=x^3+5028677x^2-305545084240x.
\]

The exact supplied point is

\[
P=\left(\frac{93082857946624000}{911427267969},
\frac{129969110503209045907820800}{870127764175520703}\right).
\]

The independent Python Fraction identity verifies this point on E exactly. Direct finite-field enumeration gives good-reduction counts 4 at 7 and 18 at 17, so rational torsion has order at most two; (0,0) supplies order two. Thus P has infinite order, supplying rank at least one independently of the full descent.

The bounded hidden GP replay returns

```text
ellrank(E,0,[P]) = [1,1,2,[P]]
#ell2cover(E) = 4
elltors(E) = [2,[2],[[0,0]]]
```

The retained GP version is `[2,20,0,31374,"af459b2ae5"]`. The script and output are [arithmetic.gp](../computation/arithmetic.gp), [verify_arithmetic.py](../computation/verify_arithmetic.py), [pari-replay.txt](../computation/pari-replay.txt) and [arithmetic-results.json](../computation/arithmetic-results.json). The exact elementary checks include all local witnesses/obstructions and both j-parameter identities. The full 2-descent and Cassels-pairing calculation uses PARI's implementation.

## Official output semantics

The [official ellrank specification](https://pari.math.u-bordeaux.fr/dochtml/html/Elliptic_curves.html#ellrank) identifies the first two entries as rigorous lower and upper Mordell–Weil rank bounds. Its third entry is the dimension

\[
s=\dim_{\mathbf F_2}(G[2]/2G[4]),\qquad G=\Sha(E/\mathbf Q).
\]

Its algorithm computes the finite 2-Selmer dimension C, rational 2-torsion dimension T and this quotient dimension s, with upper rank bound C−T−s. The [ell2cover specification](https://pari.math.u-bordeaux.fr/dochtml/html/Elliptic_curves.html#ell2cover) returns a **basis** of locally soluble 2-coverings. Accordingly four returned basis elements mean dimension four, hence 16 elements in the finite 2-Selmer group.

For this output the quantities are

\[
r=1,\quad C=4,\quad T=1,\quad s=2.
\]

These also satisfy the consistency identity C−T−s=1.

## Exact deduction of the whole two-primary group

The finite Kummer sequence is

\[
0\longrightarrow E(\mathbf Q)/2E(\mathbf Q)
\longrightarrow\operatorname{Sel}_2(E/\mathbf Q)
\longrightarrow\Sha(E/\mathbf Q)[2]\longrightarrow0.
\]

Its first term has dimension r+T=2, giving

\[
\dim\Sha(E)[2]=4-2=2.
\]

The GP quotient \(\Sha[2]/2\Sha[4]\) already has dimension two, so its denominator is zero:

\[
2\Sha(E)[4]=0.
\]

Any element of order four would have a nonzero double in that denominator. Any element of order \(2^n\), \(n>2\), would have an order-four multiple. Therefore every two-primary element has order at most two, and

\[
\boxed{\Sha(E/\mathbf Q)[2^\infty]
=\Sha(E/\mathbf Q)[2]
\cong(\mathbf Z/2\mathbf Z)^2.}
\]

This deduction uses only the two finite computed dimensions. It needs no prior finiteness assumption for the rest of Sha. The resulting abstract Mordell–Weil structure is

\[
\boxed{E(\mathbf Q)\cong\mathbf Z\oplus\mathbf Z/2\mathbf Z.}
\]

The displayed P is an explicit infinite-order point. Its saturation index is a separate computation if a specific generator is needed.

## The corank used by the repository theorems

The direct-limit Kummer sequence is

\[
0\longrightarrow E(\mathbf Q)\otimes\mathbf Q_2/\mathbf Z_2
\longrightarrow\operatorname{Sel}_{2^\infty}(E/\mathbf Q)
\longrightarrow\Sha(E/\mathbf Q)[2^\infty]\longrightarrow0.
\]

The first term has corank one and the last term is the four-element group computed above. Thus

\[
\boxed{\operatorname{corank}_{\mathbf Z_2}
\operatorname{Sel}_{2^\infty}(E/\mathbf Q)=1.}
\]

Keep the notation distinct: the finite group \(\operatorname{Sel}_2\) has dimension **four**; the two-power group \(\operatorname{Sel}_{2^\infty}\) has corank **one**. It is the latter quantity that enters the cited low-corank theorems. As abstract abelian groups the sequence even splits, since the divisible subgroup is injective, giving a noncanonical decomposition \(\mathbf Q_2/\mathbf Z_2\oplus(\mathbf Z/2\mathbf Z)^2\).

## Review disposition

The exact point, torsion calculation, GP rank interpretation, conversion of the cover-basis length into finite Selmer dimension, elementary exponent-two argument for the full two-primary Sha group, and corank-one conclusion are consistent and correctly derived. The arithmetic report correctly separates the fresh computational descent from the later use of the repository's stated analytic-rank and BSD results. The two-primary conclusion can be carried into the main handoff as a reproducible computational descent result, with the exact GP version and commands retained.
