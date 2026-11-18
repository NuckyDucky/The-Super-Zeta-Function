# The coefficient curve reaches explicit 2-descent, X0(2), and a four-element arithmetic obstruction

The strongest arithmetic connection found in the OpenAI catalogue is through families **002** and **006**, the low-Selmer-corank BSD and Goldfeld manuscripts. It becomes concrete after the norm-quartic calculation in [elliptic-bridge.md](elliptic-bridge.md): Nick's six coefficients determine a rational 2-isogeny, whose actual Mordell–Weil group and two-primary Tate–Shafarevich group are now computable.

All repository citations below use commit `4eaee87548250b2682affda7d05d947c05554bae`, fetched 16 November 2026. The structural identities and elementary exact checks are derived here. The rank and Cassels-pairing statements are reproducible PARI/GP results. Applications of the new OpenAI theorems are identified at the formula where they enter.

## 1. The actual elliptic curve and its rational points

For the original coefficient pair

\[
N=465x^2-183x-659,\qquad D=155x^2+396x-936,
\]

the square-completion quartic is

\[
f=(N-D)^2+4N^2
=961000x^4-1039740x^3-1810543x^2+644010x+1813853.
\]

Write `q=5028677`, `R=19096567765`. The Jacobian can be presented over Q as

\[
E:\quad y^2=x^3+5028677x^2-305545084240x,
\tag{1}
\]

and its degree-two quotient as

\[
E':\quad y^2=x^3-10057354x^2+26509772707289x.
\tag{2}
\]

The generic proof and explicit quotient of the original genus-one curve are in the companion note. This section adds the arithmetic of (1).

An exact rational point is

\[
P=\left(
\frac{93082857946624000}{911427267969},
\frac{129969110503209045907820800}{870127764175520703}
\right).
\tag{3}
\]

Direct Fraction arithmetic verifies (1) exactly. Good reduction gives

\[
\#E(\mathbf F_7)=4,\qquad \#E(\mathbf F_{17})=18.
\]

Rational torsion injects into both reductions, so its order divides `gcd(4,18)=2`. The point `(0,0)` has order two. Consequently

\[
E(\mathbf Q)_{\rm tors}\cong\mathbf Z/2\mathbf Z,
\]

and (3) has infinite order. This independently establishes the lower rank bound one.

## 2. Exact local descent: 144 coverings collapse to 18

For `E:y²=x³+A x²+B x`, the rational 2-isogeny has quotient coefficients `A'=-2A`, `B'=A²-4B`. The classical isogeny descent uses squareclasses represented by squarefree signed divisors `d` of `B` and the quartics

\[
w^2=d u^4+A u^2v^2+(B/d)v^4.
\tag{4}
\]

For (1),

\[
B=-2^4\cdot5\cdot11\cdot23\cdot31\cdot486971,
\]
\[
A^2-4B=41\cdot457\cdot1414835497.
\]

There are 128 signed squareclasses on the first side and 16 on the dual side. The script exhausts the primitive projective residue tests at prime powers and retains exact local-square witnesses at every bad prime:

\[
2,5,11,23,31,41,457,486971,1414835497.
\]

Its complete results are:

\[
\begin{aligned}
S_E=\{&\pm1,\pm115,\pm155,\pm713,\pm26783405,\\
&\pm123203663,\pm166057111,\pm19096567765\},
\end{aligned}
\]

\[
S_{E'}=\{1,26509772707289\}.
\]

The first group has 16 elements, the second two. Every excluded class has an explicit modulus for which (4) has no primitive solution. Every retained class has an integer pair `(u,v)` whose quartic value has trivial squareclass in each relevant Qp. At good odd primes the smooth genus-one reduction has a point by Hasse's bound, and it lifts. The real places are also soluble. Thus these are full local isogeny-Selmer sets; no local decision remains pending.

The standard isogeny rank formula gives the upper bound

\[
2^{r+2}\le |S_E|\,|S_{E'}|=32,
\qquad r\le3.
\]

These local sets and all their certificates are in [E-local-descent.json](../computation/E-local-descent.json) and [dual-local-descent.json](../computation/dual-local-descent.json).

## 3. Full descent resolves the rank and the two-primary obstruction

The bounded PARI/GP calculation returns

```text
ellrank(E,0,[P]) = [1,1,2,[P]]
#ell2cover(E) = 4
elltors(E) = [2,[2],[[0,0]]]
```

The documented output of `ellrank` is `[r1,r2,s,L]`, where `r1≤rank≤r2` and

\[
s=\dim_{\mathbf F_2}\bigl(\Sha(E)[2]/2\Sha(E)[4]\bigr).
\]

The four `ell2cover` basis elements give `dim Sel2(E)=4`; rational two-torsion has dimension one. Hence the Kummer exact sequence gives

\[
\dim\Sha(E)[2]=4-1-1=2.
\]

Since the displayed quotient already has dimension two, `2 Sha(E)[4]=0`. An element of order at least four would produce nonzero order-four torsion, so the entire two-primary group has exponent two. We obtain

\[
\boxed{E(\mathbf Q)\cong\mathbf Z\oplus\mathbf Z/2\mathbf Z,
\qquad \Sha(E/\mathbf Q)[2^\infty]\cong(\mathbf Z/2\mathbf Z)^2.}
\tag{5}
\]

The point (3) is an explicit infinite-order point; the calculation recorded here does not identify it as a saturated generator.

PARI's documented algorithm computes 2-descent and the 2-part of Cassels pairings. Its rank/Sha quantities above are unconditional computational outputs. The elementary Python checks independently verify the point, torsion, local squareclasses and modular parameter. The rank-one upper bound and the nondegenerate two-dimensional Sha quotient use PARI's implementation. See [PARI's official ellrank specification](https://pari.math.u-bordeaux.fr/dochtml/html/Elliptic_curves.html#ellrank), especially the definitions of `C,T,s` and `r2=C-T-s`.

The portable executable came from the [official PARI/GP distribution](https://pari.math.u-bordeaux.fr/download.html), with version `[2,20,0,31374,"af459b2ae5"]`; SHA256 is `f38f49c6c65d795ccc60dee0564485df8e9a14db7cadda95d98adeff62ec581e`. Both independent calls and the final deterministic replay completed in under one second each. Exact results are in [arithmetic-results.json](../computation/arithmetic-results.json), [pari-replay.txt](../computation/pari-replay.txt), and [arithmetic.gp](../computation/arithmetic.gp).

## 4. Exact input to the OpenAI BSD manuscripts

From (5), the two-primary Tate–Shafarevich group has corank zero and order four. The usual Kummer sequence therefore gives

\[
\operatorname{corank}_{\mathbf Z_2}\operatorname{Sel}_{2^\infty}(E)=1.
\tag{6}
\]

This is the precise hypothesis of OpenAI family 006's **2-converse theorem**, and family 002's **two-primary BSD theorem**. The relevant input is (6); the finite 2-Selmer dimension is four, and the Cassels pairing is what resolves its two extra dimensions.

The exact source statements are:

* [Goldfeld manuscript, introduction, Theorem `thm:main-converse`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Goldfelds-analytic-density-conjecture-and-the-2-converse-for-elliptic-curves-October-7-2026/build/sections/00-introduction.tex): full two-power Selmer corank zero or one implies equality of analytic rank, Mordell–Weil rank and that corank, with whole-Sha finiteness. Its conclusion proof dispatches the rational-two-torsion case through `thm:rational-converse` and uses the classical analytic low-rank theorem.
* [Two-primary BSD manuscript, introduction, Theorem `thm:main`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-two-primary-Birch-Swinnerton-Dyer-formula-in-Selmer-corank-at-most-one-October-6-2026/build/sections/01-introduction.tex): for full two-power Selmer corank at most one,

\[
Q_E=\frac{L^{(r)}(E,1)\,\#E(\mathbf Q)_{\rm tors}^{2}}
{r!\,\Omega_E\operatorname{Reg}_E\prod_\ell c_\ell(E)}\in\mathbf Q_{>0},
\qquad v_2(Q_E)=v_2(\#\Sha(E)).
\tag{7}
\]

Applying those stated source theorems to (6) yields analytic rank one, finiteness of the entire Tate–Shafarevich group, and the explicit valuation prediction

\[
\boxed{v_2(Q_E)=2.}
\tag{8}
\]

The normalizations matter: `Omega_E` integrates the minimal Néron differential over **both real components**; the regulator uses the **full Mordell–Weil lattice** and the paper's canonical-height pairing attached to `2[O]`; finite Tamagawa numbers are all included; torsion contributes `2²=4`. The globally minimal model returned by PARI is

\[
y^2+xy=x^3+x^2-545921408813x+155181865191498992.
\]

Equation (8) is a deduction using the repository's stated theorem. Its long Iwasawa-theoretic proof was read at the statement, structural-comparison and conclusion level here; a complete re-verification of its integral comparison lemmas is a separate proof audit. The computational certificate (5) and the exact bridge to the hypothesis (6) stand independently of that imported theorem. No numerical L-value or BSD leading-term ratio is reported.

## The original quartic itself enters the four-element Sha group

The exact discriminant of the original quartic is

\[
\operatorname{disc}(f)=2^8\cdot5^2\cdot11^2\cdot23^2\cdot31^2
\cdot41\cdot457\cdot1414835497\cdot486971^2.
\]

At its bad primes, the following primitive projective pairs give a quartic value that is a square in \(\mathbf Q_p\):

| Prime | \((u,v)\) | \(f_h(u,v)\) |
|---|---|---|
| 2 | (1,1) | 568580 |
| 5 | (1,5) | 1164658100 |
| 11 | (1,1) | 568580 |
| 23 | (0,1) | 1813853 |
| 31 | (1,0) | 961000 |
| 41 | (1,0) | 961000 |
| 457 | (1,1) | 568580 |
| 486971 | (1,1) | 568580 |
| 1414835497 | (2,1) | 2917781 |

For odd \(p\), the script checks even p-adic valuation and a square residue unit. At \(p=2\), it checks even valuation and unit \(1\bmod8\); for example \(568580=4\cdot142145\) with \(142145=1\bmod8\). At all other finite primes, smooth genus-one reduction and Hasse's bound supply a finite-field point and Hensel lifting. The real points were already explicit in the positive norm-quartic geometry.

Therefore the original curve \(C:Y^2=f(x)\) is everywhere locally soluble. Its degree-two x-projection supplies a rational divisor of degree two. Its torsor class consequently satisfies

\[
\boxed{[C]\in\Sha(E/\mathbf Q)[2]
\cong(\mathbf Z/2\mathbf Z)^2.}
\]

The class is **nonzero**. An explicit rational covering map sends a hypothetical rational point of \(C\) to a point of \(E\) whose x-coordinate has squareclass \(-1\). Exact rank-one descent gives the complete rational x-squareclass image
\[
\{[1],[115],[-19096567765],[-166057111]\},
\]
which excludes \([-1]\). Hence \(C(\mathbf Q)=\varnothing\): the original coefficient quartic is an explicit counterexample to the Hasse principle. The full polynomial identity, covering map and squareclass argument are proved in [hasse-obstruction.md](hasse-obstruction.md) and checked by the same arithmetic script.

## 5. The coefficient construction lands explicitly on X0(2)

There is a second structural consequence, independent of the new BSD claims. For any curve `y²=x³+A x²+B x`, define

\[
h=\frac{16(A^2-4B)}B.
\]

The ordinary invariant formula and its dual are

\[
j(E)=\frac{256(A^2-3B)^3}{B^2(A^2-4B)},
\qquad
j(E')=\frac{16(A^2+12B)^3}{B(A^2-4B)^2}.
\]

Substitution gives the rational parametrization

\[
\boxed{j(E)=\frac{(h+16)^3}{h},\qquad
j(E')=\frac{(h+256)^3}{h^2}.}
\tag{9}
\]

These are the two j-maps of the modular curve `X0(2)`. Our concrete value is

\[
\boxed{h=-\frac{26509772707289}{19096567765}.}
\]

Thus the norm-quartic coefficient mechanism supplies an explicit modular coordinate. The product `E×E'` is isogenous to `E²` through `id×dual-isogeny`. This gives a formula-level connection to the **elliptic-square locus** discussed in family 016's [Elliptic Squares and Zilber–Pink for Curves in A2](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Elliptic-Squares-and-Zilber-Pink-for-Curves-in-A2-September-24-2026/paper.pdf): our products run inside that special locus as the coefficients vary. The useful deduction is the explicit map (9), and the resulting rational 2-isogeny structure to preserve when searching coefficient families.

## 6. What family 017 actually contributes

The [pi irrationality-exponent manuscript](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf) was read in its introduction, separated-weight interpolation theorem, determinant arithmetic bound, analytic determinant estimate and conclusion. Its approximation variables are integers `p_i,q_i` with `|pi-p_i/q_i|≤q_i^{-nu}`, weights `w_i=ceil(log q_i)`, and centers `r_i=2i p_i/q_i` approaching the logarithmic period `2pi i`. Nick's objects instead use integer-height rational functions evaluated at `e`, with six correlated coefficients.

The most concrete transferable lemma is the manuscript's [Arithmetic lower bound](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/determinant.tex): scale columns and derivative rows by their actual denominator weights, clear logarithmic-truncation denominators with explicit least common multiples, and obtain a nonzero Gaussian-integer determinant, whose modulus is at least one. This separates the **proof of determinant nonvanishing** from its **arithmetic denominator accounting** and its **analytic smallness bound**.

That architecture is useful for a future quantitative separation theorem for the coefficient search: construct a family of correlated forms, prove a full-rank minor, record exact coefficient-height costs, and then compare the resulting integral determinant with the observed small errors. The present investigation follows the elliptic route because it produces the exact new information (5), (6) and (9) immediately. Family 017's theorem concerns rational denominators `q`; the six-coefficient search's natural height is a different parameter and its determinant problem needs its own construction.

## Reproduction

Run the elementary independent computation:

```text
python computation/verify_arithmetic.py
```

Replay the full PARI calculation through the same script:

```text
python computation/verify_arithmetic.py --gp /absolute/path/to/gp
```

The optional child is hidden on Windows, has a 20-second hard timeout, and uses no GUI, GPU, network or running lab process. Alternatively run `gp -q -f computation/arithmetic.gp` directly. The local tests retain an exact witness or an exact modular obstruction for every squareclass decision.
