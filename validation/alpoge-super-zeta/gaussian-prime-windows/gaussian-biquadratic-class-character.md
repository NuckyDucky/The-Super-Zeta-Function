# The Gaussian factor as an unramified ideal class character

The Gaussian factor $G$ of the original quartic also comes from an
order-four ideal class character of the imaginary quadratic field
$B=\mathbb Q(\sqrt{-D})$. Its square comes from an unramified quadratic
character of the CM field $A=\mathbb Q(i,\sqrt D)$. The count over $A$ has
the same upper-bound criterion as the count over $\mathbb Q(i)$. Here
$D=26509772707289$ throughout. [Original field and signed prime weights](gaussian-prime-classes.md)

## The conductor residue and the norm

I use $k=\mathbb Q(i)$, $\delta=-5045155+1027708i$ and
$K=k(\sqrt\delta)$. The same root $r=11825711960877$ from the Fourier
proof gives the map

$$
\rho(m+ni)=m+nr\pmod D,\qquad
\mathbb Z[i]/(\delta)\ \simeq\ \mathbb Z/D\mathbb Z.
$$

Lean checks the kernel and the quotient isomorphism. To prove the kernel
I use the earlier dual lattice identity, which says that
$D\mid n-rm$ exactly when $m+ni$ is a multiple of $\delta$.
Multiplication by $-r$ sends $m+nr$ to $n-rm$, since $r^2=-1\pmod D$.
The sign of a Gaussian prime ideal $(z)$ is the Jacobi symbol of $\rho(z)$
modulo $D$, independently of the choice of generator. The two conjugate
residues satisfy $\rho(z)\rho(\bar z)=N(z)\pmod D$. [Original dual lattice](../../../lean-ideal73/QuarticDualArithmetic.lean) · [Lean residue and ideal character](GaussianConductorResidue.lean)

| Generator above $73$ | Conductor residue | Sign |
| --- | ---: | ---: |
| $3+8i$ | $15076377565152$ | $-1$ |
| $3-8i$ | $11433395142143$ | $+1$ |

For a rational prime $p$, Lean checks that twice the degree-one inert
count is the sum of $1-\eta(\mathfrak p)$ over the unramified degree-one
Gaussian primes above $p$. In a norm cutoff both ideals use the same
size $p$. Their individual conductor residues supply their signs.
[Example and cutoff weight](GaussianConductorResidue.lean)

## Divisibility at a negative Gaussian prime

If an odd rational prime $p$ splits in $k$, choose the root of $-1$ in
$\mathbb F_p$ that specifies $\mathfrak p$ above $p$. Lean applies
Euler's criterion to the reduction of $\delta$ at that root and proves

$$
\delta^{(p-1)/2}+1\in\mathfrak p
\quad\Longleftrightarrow\quad
\eta(\mathfrak p)=-1.
$$

At $p=73$, let $C=\delta^{36}+1$. Then $3+8i$ divides $C$ and $3-8i$
does not. The kernel computes $N(C)\equiv2409=33\cdot73\pmod{73^2}$,
so $73$ divides $N(C)$ exactly once. This check uses a different
expression for each $p$. To bound the count, I still need to combine
the gains for many primes in one expression with an upper bound on its
size. [Lean divisibility and exact norm remainder](GaussianConductorResidue.lean)

## The cyclic quartic extension over $B$

Write $L=k(\alpha,\beta)$ with $\alpha^2=\delta$ and $\beta=\bar\alpha$.
Let $\sigma$ and $\tau$ flip $\alpha$ and $\beta$ respectively, let
$z=\sigma\tau$, and let $c$ be complex conjugation. The normal closure
is dihedral of order eight. The element $\gamma=c\sigma$ has order four
and $\gamma^2=z$. It fixes $i\alpha\beta=\sqrt{-D}$. Thus
$\operatorname{Gal}(L/B)=\langle\gamma\rangle$ and
$\operatorname{Gal}(L/A)=\langle z\rangle$. [Normal closure and degree](gaussian-prime-classes.md)

For any finite place of $A$ of odd residue characteristic, one of
$\delta,\bar\delta$ is a unit. Lean checks their coprimality using
the two Gaussian Bézout coefficients
$-1779499-4161725i$ and $3265656+3134017i$.
Since $\delta\bar\delta=D$ is already a square in $A$, I can use the unit
of this pair to generate $L/A$ at that place. Adjoining its square root
is unramified, since the polynomial of a unit square root has unit
discriminant in odd residue characteristic. At a dyadic place the
polynomial

$$
X^2-X+(1-\delta)/4
$$

has integral coefficients and derivative reducing to $-1$. Its roots
generate the same extension and give a finite étale algebra over the
completed integer ring. This proves that $L/A$ is unramified at every
finite place. [Lean Bézout certificate](GaussianBiquadraticInertWeights.lean) · [Original relative discriminant](../../../lean-ideal73/RelativeQuartic.lean#L81)

At an odd prime dividing $D$, Lean checks $p\equiv1\pmod 4$, so $i$ is
already in $\mathbb Q_p$ by Hensel's lemma and $A/B$ splits there.
At $2$, the checked congruence $D\equiv1\pmod8$ gives $\sqrt D\in\mathbb
Q_2$ by Hensel's lemma applied at $1$, so $A/B$ splits there too. At the
remaining primes the two quadratic extensions defining $A$ are
unramified over $\mathbb Q_p$. This proves that the cyclic quartic
extension $L/B$ is everywhere unramified. Its character $\psi$ with
$\psi(\gamma)=i$ is therefore an ordinary ideal class character of $B$
by Artin reciprocity. This is an instance of the classical unramified
cyclic quartic construction. [Checked congruences](GaussianBiquadraticInertWeights.lean) · [Rédei extensions and Artin symbols](https://doi.org/10.1017/S0305004121000335)

## The same Gaussian factor

Let $\eta$ be the relative character of $K/k$, and let $\eta_A$ be the
character of $L/A$ with $\eta_A(z)=-1$. The induced representation of
$\eta$ from $\operatorname{Gal}(L/k)$ to $\operatorname{Gal}(L/\mathbb Q)$
has trace $2$ at $1$, trace $-2$ at $z$, and trace zero elsewhere.
Inducing $\psi$ from $\langle\gamma\rangle$ gives that same trace.
Inducing $\eta_A$ from $\langle z\rangle$ gives twice that trace.
Artin induction consequently identifies the full factors, including at
the ramified rational primes.

$$
G(w)=L_B(w,\psi),\qquad
L_A(w,\eta_A)=G(w)^2,\qquad
\zeta_L(w)=\zeta_A(w)G(w)^2.
$$

The imaginary quadratic discriminant of $B$ is $-4D$, so the completion
scale $\sqrt{|\operatorname{disc}(B)|}/(2\pi)$ is the original
$\sqrt D/\pi$. [Artin induction and Euler factors](https://doi.org/10.1007/BF02941010) · [Archived Mellin normalization](../../../lean-ideal73/ArchivedGaussianMellin.lean)

The real subfield of $A$ is $F=\mathbb Q(\sqrt D)$. The character
$\eta_A$ is invariant under conjugation and has order two. More
explicitly, $L$ is the compositum of $A$ and
$M=F(\alpha+\beta)$, where $(\alpha+\beta)^2=2(-5045155+\sqrt D)$.
The quadratic character of $M/F$ pulls back along $N_{A/F}$ to $\eta_A$.
On ideles from $F$, that norm squares the idele, so $\eta_A$ is trivial
there. This gives an unramified conjugate-self-dual quadratic character
on the explicit CM field $A$. [Standard reciprocity and norm compatibility](https://link.springer.com/book/10.1007/978-1-4612-0853-2)

## The count to bound after lifting

Let $I_A(p)$ count the degree-one primes of $A$ above $p$ with
$\eta_A=-1$. Keep the original $I(p)$ over $k$ and exclude $p\mid2D$.
Write $e=\chi_{-4}(p)$ and $d=\chi_D(p)$. If $e=d=1$, the prime splits
completely in $A$ and each Gaussian prime has two lifts with the same
sign. If $e=1$ and $d=-1$, its Gaussian signs are opposite and the
primes of $A$ above $p$ have degree two. If $e=-1$, neither base has a
degree-one prime above $p$. These cases give

$$
I_A(p)=2I(p)-\frac{(1+e)(1-d)}2
      =\begin{cases}
        4,&a(p)=-2,\\
        0,&a(p)\ne-2.
      \end{cases}
$$

Lean checks the weight identity and its weighted finite sum. At
$p=5,13,73$ the three $I_A$ values are $0,4,0$. The $73$ contribution
to the original count moves into the known mixed-character term.
[Lean transfer and concrete examples](GaussianBiquadraticInertWeights.lean)

For $B$, the sum of $1-\Re\psi(\mathfrak p)$ over its degree-one
primes above $p$ is $1+ed-a(p)$. A split prime of $B$ with $e=d=-1$
has conjugate values $i,-i$, giving an extra weight of two. The weight
over $B$ therefore equals $I_A(p)+(1-e)(1-d)/2$. Lean checks that last
identity from the original prime coefficients. [Lean class character weight](GaussianBiquadraticInertWeights.lean)

Both correction weights are linear combinations of $1,\chi_{-4},\chi_D$
and $\chi_{-4}\chi_D$. If I apply the rational Dirichlet result, their
log-weighted partial sums are $t/2+O(\sqrt t\log^2t)$.
Centering the smoothed cutoff and using partial summation as before gives

$$
R_{I,A}(x)=2R_I(x)+O(x^{-1/2}\log^2x).
$$

The centered $B$ weight differs from $R_{I,A}$ by another error of that
order. Degree-two primes also fit within it. It follows that an upper
bound at exponent $\theta-1$ for any of the three centered counts gives
the same upper bound for the other two for every $1/2<\theta<1$.
The window widths and the cofinal starts transfer, with a change of the
constant. [Centering conventions](gaussian-inert-windows.md) · [Chebotarev estimates](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf#page=3)

## Where the local divisibility has to enter

Sernau's local formula uses the action of an inert rational prime on a
place of the CM host. The formula relates odd powers of Frobenius to
complex conjugation and feeds the local theta divisibility estimate.
The relative character here is already unramified and can be supplied
as an ideal class character. The step to establish is the corresponding
local gain at a prime with $\eta_A=-1$, together with the resulting
summed upper bound. At $p=13$, all four primes of $A$ have that sign.
[Frobenius and conjugation in the published proof](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/WeilDataOfE.lean#L119) · [Local theta divisibility](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/JetDivisibility.lean#L5)

Lean checks the conductor map, the arithmetic inputs for unramifiedness
and the prime weight identities. The field extension, Artin induction
and centered asymptotics above are written classical arguments.
[Lean build and axiom audit](conductor-residue-replay-audit.txt)
