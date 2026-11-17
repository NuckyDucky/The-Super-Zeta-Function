# Prime-adic reciprocal towers, analytic time, and exact period ladders

**16 November 2026. Exact propositions, complete derivations, and modular experiments.**

The reciprocal construction supports two precise non-Archimedean structures.
The principal exponential fixed-pair map gives a contracting congruence tree.
The normalized Touchard–Bell parabolic germ gives analytic fractional iteration
and invariant balls on which iteration is conjugate to the p-adic adding
machine. The latter produces an exact prime-power period ladder.

The bridge is the universal rational coefficient family already present in
NuckyDucky's work. A complex Dottie specialization and p-adic specializations retain
the same formulas for the normalized coefficients and iterative residue. The
coefficient field, completion, and evaluated phase parameter are specified below.

## 1. Principal exponential dynamics: an exact ultrametric contraction

Let K be a complete extension of Qp, with |p|=p^-1, valuation ring O_K, and
\[
r_p=p^{-1/(p-1)}.
\]
The ordinary power-series exponential is defined on |z|<r_p. On that disk,
\[
|e^z-1|=|z|,\qquad |e^z-e^w|=|z-w|.
\tag{1}
\]
Indeed v(z^n/n!)>v(z) for n>=2 follows from
v(n!)<=(n-1)/(p-1). The first term therefore dominates the remaining terms.
The convergent formal identities give e^(z+w)=e^z e^w, and logarithm supplies
the inverse on these disks. The implementation's tail bounds use the same
factorial estimate; [FLINT's primary algorithm documentation](https://flintlib.org/doc/algorithms/p-adic/exp-log.html)
records the computational exp/log setting.

**Proposition 1 (reciprocal contraction and its congruence tree).** Fix
0<|L|<r_p, and define on O_K^2
\[
\mathcal F_L(P,Q)=(e^{LQ},e^{-LP}).
\]
For the maximum metric d,
\[
\boxed{d(\mathcal F_L(x),\mathcal F_L(y))=|L|d(x,y).}
\tag{2}
\]
The map is a bijection from O_K^2 onto (1+L O_K)^2. It has one fixed pair in
O_K^2, and every orbit converges to it. Its scalar return
\[
g_L(z)=e^{Le^{-Lz}}
\]
satisfies |g_L(z)-g_L(w)|=|L|^2|z-w| on O_K.

On any product ball B(c,r) contained in O_K^2,
\[
\mathcal F_L(B(c,r))=B(\mathcal F_L(c),|L|r).
\tag{3}
\]
For Qp write s=v_p(L). The domain condition is s>=1 for odd p and s>=2 for
p=2. Reduction modulo p^N has the exact image counts
\[
\boxed{\#\mathcal F_L^n((\mathbb Z/p^N)^2)
=p^{2\max(N-ns,0)}.}
\tag{4}
\]
Every reduced orbit reaches the fixed pair after at most ceil(N/s) paired
updates, and this bound is attained. The only periodic vertex is the fixed pair.

**Proof.** Equation (1) applied to each coordinate gives (2). Given
A in 1+L O_K, log(A)/L is in O_K, so inversion of each exponential coordinate,
with the appropriate swap and sign, proves surjectivity and injectivity.
The same inverse argument on a ball proves (3). Completeness and |L|<1 give
the unique fixed pair and convergence. Two applications of (1) give the scalar
return formula. Iterating (3) gives balls of radius p^-ns. Their reductions have
p^(2 max(N-ns,0)) elements. Once ns>=N, the image is a singleton containing
the fixed pair. A starting point differing from that pair modulo p has exact
distance p^-ns after n steps, establishing the maximum capture time. ∎

For a finite extension K/Qp, let pi be a uniformizer, e its ramification index,
and q=p^f the residue-field size. If s=v_pi(L) satisfies
s/e>1/(p-1), the identical proof modulo pi^N gives
\[
\#\mathcal F_L^n((\mathcal O_K/\pi^N)^2)
=q^{2\max(N-ns,0)},\qquad
\text{maximum capture time}=\lceil N/s\rceil.
\]
This follows from |O_K/pi^a|=q^a and the ball bijection (3). Each one-coordinate
congruence ball has q children at its next uniformizer precision; a pair ball
has q^2 children. The ramification inequality states the exponential domain
in the normalized p-adic valuation.

The resulting finite graph is a rooted functional graph, with the fixed
self-loop at its root. Each update discards exactly s digits of dependence on
the input in the two-coordinate maximum metric. Increasing N refines vertices
by prime-power congruence and yields a compatible inverse system of these graphs.

At its fixed pair, the actual lifts have |U|=|V|=|L| and |mu|=|L|^2. Thus the
maximum norm already balances the two channels. This is the non-Archimedean
counterpart of the exact balanced complex metric developed previously.

## 2. The fixed pair is a signed labeled-tree generating function

The unique formal pair at L=0 has Q(L)=P(-L). Write
\[
P(L)=\sum_{n\ge0}a_n\frac{L^n}{n!}.
\]
Differentiating P=exp(LP(-L)) gives the integral recurrence
\[
\boxed{a_0=1,\qquad
a_n=\sum_{j=1}^n j\binom{n-1}{j-1}(-1)^{j-1}a_{j-1}a_{n-j}.}
\tag{5}
\]
The first coefficients are
\[
1,1,-1,-8,21,336,-1445,\ldots.
\]
All coefficients a_n are integers by (5).

There is an exact rooted-tree interpretation. Take all labeled trees on
{0,1,...,n}, root each at 0, and give a tree the sign (-1)^e, where e is the
number of nonroot vertices at even distance from the root. Then a_n is their
signed sum. Decomposing a rooted tree into the unordered family of subtrees at
its children gives the exponential generating equations
\[
P=e^{LQ},\qquad Q=e^{-LP}.
\]
An edge from a P root to a Q child contributes +L; the next level contributes
-L. This is precisely the stated depth sign. The labeled exponential formula
therefore identifies the signed counts with the formal fixed-pair coefficients.

For v_p(L)>1/(p-1),
\[
v_p(a_nL^n/n!)\ge n v_p(L)-v_p(n!)
\ge n v_p(L)-(n-1)/(p-1)\longrightarrow\infty.
\tag{6}
\]
Consequently the same integer tree coefficients produce the analytic p-adic
fixed pair throughout the principal domain. Formula (6) also supplies a
controlled truncation rule.

The reproduction independently enumerates Prüfer codes for every labeled tree
through seven vertices and matches the signed sums. It then compares the
degree-50 tree series with direct exact p-adic fixed-pair iteration modulo
p^16 for p=2,3,5,7, retaining agreement at every smaller precision.

## 3. Ordinary towers carry finite root-of-unity addresses

For odd p, any unit base a has the canonical decomposition
\[
a=\omega(a)\langle a\rangle,
\quad\omega(a)^{p-1}=1,\quad\langle a\rangle\in1+p\mathbb Z_p.
\]
Set L=log(<a>) and m=ord_p(a), the order of its residue modulo p. Retaining
an exponent residue r modulo m gives the analytic branch
\[
a^x\rightsquigarrow \omega(a)^r e^{Lx},\quad x\in\mathbb Z_p.
\tag{7}
\]
For integer x with x=r modulo m, this equals the ordinary integer power.
This residue-address construction is the exact source input in
[Holden–Robinson (2012), Proposition 2.1, Theorem 4.1 and Proposition 5.3](https://doi.org/10.1017/S1446788712000262).
They treat branchwise ordinary fixed points and same-base two-cycles.

**Proposition 2 (reciprocal branch pairs).** For each ordered label
(r,s) in (Z/m)^2, the reciprocal branch map
\[
\mathcal F^{r,s}_a(P,Q)=
\bigl(\omega(a)^r e^{LQ},\ \omega(a)^{-s}e^{-LP}\bigr)
\tag{8}
\]
has a unique fixed pair in Zp^2. The pairs for distinct labels are distinct
modulo p; there are exactly m^2 pairs. For every N>=1, the integer congruences
\[
a^Q\equiv P\pmod{p^N},\qquad
a^{-P}\equiv Q\pmod{p^N}
\tag{9}
\]
have exactly m^2 ordered solutions when P,Q are counted modulo m p^N.
There is exactly one for each Q=r, P=s modulo m.

**Proof.** Multiplication by the roots of unity has absolute value one.
The argument of Proposition 1 gives a contraction on each ordered branch
(or a constant map if L=0). Reduction modulo p is
(P,Q)=(omega(a)^r,omega(a)^(-s)), which distinguishes the labels.
At every p^N precision each fixed pair gives a unique residue pair.
Since gcd(m,p)=1, the Chinese remainder theorem adjoins exactly the required
P=s,Q=r residues modulo m. Equation (7) then identifies these fixed-point
equations with (9). Every integer solution selects one of these labels. ∎

For p=2, write an odd base a as epsilon<a>, with epsilon in {1,-1} and
<a> in 1+4Z2. Both coordinates in (9) are odd, so their exponent parity is
one and the sign phases in both channels are epsilon. The map
\[
(P,Q)\mapsto(\epsilon e^{LQ},\epsilon e^{-LP})
\]
has one fixed pair, reducing to exactly one solution of (9) modulo 2^N.
This keeps parity in the same 2-adic coordinate. The odd-prime Chinese
remainder count uses the explicit coprimality gcd(m,p)=1.

The exact experiment counts 4,16,36,100 ordered branches for bases/primes
(2,3),(2,5),(3,7),(2,11), respectively, across successive powers. At p=2,
bases 3,5,7,9 give exactly one pair at every precision 2^N, N=1,...,9.

This is a concrete two-level arithmetic address: a finite Teichmüller phase
label, followed by a compatible prime-power refinement. The ordered phases are
essential data in this representation.

## 4. The same normalized parabolic coefficient family has analytic p-adic time

NuckyDucky's normalized universal germ is
\[
f_\alpha(z)=\frac{1+\alpha}{2\alpha}
\left[\exp\!\left(\alpha(\exp(2z/(1+\alpha))-1)\right)-1\right]
=z+z^2+\sum_{n\ge3}h_n(\alpha)z^n,
\tag{10}
\]
with the removable value f_0(z)=(exp(2z)-1)/2. Its Touchard–Bell formula is
\[
h_n(\alpha)=\frac{2^{n-1}T_n(\alpha)}
{n!\,\alpha(1+\alpha)^{n-1}}.
\tag{11}
\]
Take alpha in Zp with 1+alpha a unit. The polynomial T_n(alpha)/alpha has
integer coefficients, including its value at zero. Thus
\[
v_p(h_n)\ge(n-1)v_p(2)-v_p(n!).
\]

Choose k>=1 for odd p, k>=2 for p=2, and put r=p^k. Define
\[
F(w)=r^{-1}f_\alpha(rw).
\]
Then
\[
\boxed{F\in\mathbb Z_p\langle w\rangle,
\qquad F(w)=w+r w^2 A(w),\quad A\in\mathbb Z_p\langle w\rangle,
\quad A(0)=1.}
\tag{12}
\]
For odd p, h_2=1 and v_p(n!)<=n-2 for n>=3 establish coefficient divisibility
by p^k. For p=2, n-1-v_2(n!)>=0 makes all h_n integral. The same estimates
tend to infinity after rescaling, proving membership in the Tate algebra.

Poonen's [2014 interpolation theorem](https://math.mit.edu/~poonen/papers/p-iteration.pdf)
applies to an analytic unit-polydisk map congruent to the identity modulo p^c
when c>1/(p-1). Its construction uses the difference operator
\[
\Delta h=h\circ F-h.
\]
Our coefficient estimate supplies c=k for the specific map (12).

**Proposition 3 (analytic time and an explicit error bound).** There is an
analytic action G(w,t), t in Zp, satisfying G(w,n)=F^n(w) for all nonnegative
integers n and
\[
\boxed{G(w,t)=\sum_{n\ge0}\binom tn\Delta^n w.}
\tag{13}
\]
It obeys G(G(w,s),t)=G(w,s+t). Truncating (13) after n=N has value error
divisible by p^(k(N+1)) for w,t in Zp.

To see the estimate directly, composition congruence gives
Delta(Zp<w>) subset p^k Zp<w>, so Delta^n w is in p^(kn) Zp<w>.
For t in Zp, binomial(t,n) is integral. For analyticity in t, division by n!
is controlled by v_p(n!)<=(n-1)/(p-1). The resulting positive linear valuation
slope proves convergence in both variables. At integral times the binomial
identity (I+Delta)^n gives the actual iterate. Analytic identity then gives
the additive action law.

There is a useful larger time domain. For an integer ell>=0 with
\[
k-\ell>1/(p-1),
\]
(13) is analytic for t in p^(-ell)Zp. Its omitted terms beyond N have valuation
at least
\[
\boxed{(N+1)\left(k-\ell-\frac1{p-1}\right)+\frac1{p-1}.}
\tag{14}
\]
Indeed the Gauss norm of binomial(p^(-ell)u,n) is at most
p^(ell n+v_p(n!)). The same analytic action law extends to this time disk.
This provides a 2-adic half-iterate when k>=3, and a 3-adic third-iterate when
k>=2. The action maps the unit disk to itself throughout the stated time domain.

For completeness, the enlarged-domain action law uses analytic uniqueness.
The difference G(G(w,s),t)-G(w,s+t) is analytic in both time variables on the
enlarged disk: (14) makes G-w divisible by p there, so all compositions stay
inside the unit disk. Fixing a nonnegative integer s, the difference vanishes
at every nonnegative integer t. The sequence t=p^j accumulates at zero, so
the one-variable analytic identity theorem makes it zero on the whole t-disk.
Now fix any such t and repeat in s. Thus the argument uses an accumulating
zero set in each variable; it applies throughout the specified analytic disk.

## 5. A proved prime-power period ladder and an analytic Abel coordinate

**Proposition 4 (the parabolic orbit ball is an adding machine).** Let F be
(12), and take a nonzero w in pZp. Write m=v_p(w)>=1 and delta=k+2m.
Then
\[
\boxed{v_p(G(w,t)-G(w,s))=\delta+v_p(t-s)}
\tag{15}
\]
for distinct s,t in Zp. The orbit closure is the entire ball
\[
\boxed{\overline{\{F^n(w):n\ge0\}}=w+p^\delta\mathbb Z_p.}
\tag{16}
\]

On that ball F is analytically conjugate to t->t+1. Its exact reduced period
modulo p^N is
\[
\boxed{\operatorname{per}_{p^N}(w)=p^{\max(N-\delta,0)}.}
\tag{17}
\]

**Proof.** Since A(0)=1 and w is divisible by p, (12) gives
v_p(F(w)-w)=delta. More generally the operator Delta maps
w^d Zp<w> into p^k w^(d+1) Zp<w>. By induction, Delta^n w belongs to
p^(kn) w^(n+1) Zp<w>. At the selected w its valuation is at least
delta+(n-1)(k+m). For n>=2 use
\[
\binom tn=\frac tn\binom{t-1}{n-1}.
\]
The n-th term of G(w,t)-w has valuation at least
delta+v_p(t)+(n-1)(k+m)-v_p(n), strictly larger than delta+v_p(t).
The n=1 term dominates, proving v_p(G(w,t)-w)=delta+v_p(t).

The action law and preservation of v_p(w)=m give (15) for every pair s,t.
Thus G(w,.) is a scaled isometric embedding of Zp into the ball in (16).
It is onto: modulo p^(delta+j), its p^j distinct time residues fill all p^j
residues of that ball. Compactness makes the image closed, so these compatible
surjections cover the ball. Nonnegative integers are dense in Zp, proving (16).

An integer n>0 returns modulo p^N exactly when v_p(n)+delta>=N. The smallest
such integer is the power in (17). Finally the rescaled function
(G(w,t)-w)/p^delta has a unit linear coefficient and every higher power-series
coefficient divisible by p. Explicitly, for n>=2 the coefficient valuations of
the normalized n-th Mahler summand are at least
(n-1)(k+m)-v_p(n!)>=1. The normalized time map therefore has the form
u t+p R(t), with u a unit and R restricted analytic. For every target y in
Zp, t->u^(-1)(y-p R(t)) is a strict contraction; the same iteration in the
Tate algebra Zp<y> gives a restricted analytic inverse. Its transport back
to the orbit ball gives tau_w(F(z))=tau_w(z)+1. This proves the analytic
adding-machine conjugacy. ∎

The exact inverse limit is
\[
\mathbb Z_p=\varprojlim_j\mathbb Z/p^j\mathbb Z,
\]
with the finite cycles in (17) as its reductions. The coherent phase address is
the p-adic time t. A new base-p time digit selects one of p refinements of the
previous phase residue. Here the prime-power hierarchy is a proved property of
the specified parabolic specializations of the normalized reciprocal germ.

The modular experiment checks the complete orbit ball for m=1 and 2, at
p=2,3,5,7. Each has exact successive periods p,p^2,p^3. It also verifies 120
scaled time-distance identities, including nonintegral rational p-adic times.

## 6. The analytic generator preserves the Dottie residue and coefficient field

Differentiating (13) at t=0 gives the convergent analytic generator
\[
\boxed{V(w)=\sum_{n\ge1}\frac{(-1)^{n-1}}n\Delta^n w.}
\tag{18}
\]
The action law gives partial_t G(w,t)=V(G(w,t)) and
\[
V(F(w))=F'(w)V(w).
\tag{19}
\]
Writing h_3=h_3(alpha), h_4=h_4(alpha), its first coefficients are
\[
\boxed{V(w)=r w^2+(h_3-1)r^2w^3+
\left(h_4-\frac52h_3+\frac32\right)r^3w^4+\cdots.}
\tag{20}
\]
These follow by expanding exp(V d/dw)w=F(w) through degree four. If
rho=1-h_3 is the iterative residue used in the Dottie work, then
\[
\rho(\alpha)=\frac{\alpha^2+1}{3(1+\alpha)^2},
\quad [w^3]V=-\rho(\alpha)r^2.
\tag{21}
\]
Thus the same rational residue organizing the complex Fatou expansion is the
cubic coefficient of the p-adic analytic vector field.

Let b_3=[w^3]V/r^2 and b_4=[w^4]V/r^3. The identities
h_3=b_3+1 and h_4=b_4+(5/2)b_3+1 show
\[
\boxed{\mathbb Q(b_3,b_4)=\mathbb Q(h_3,h_4)=\mathbb Q(\alpha).}
\tag{22}
\]
The last equality is the existing normalized-germ reconstruction theorem for
alpha!=0,-1; the removable alpha=0 case is Q on both sides. Every generator
coefficient belongs to the same rational coefficient field: Delta raises
formal w-order, so any fixed coefficient of (18) receives only finitely many
contributions. The first two correction coefficients retain the ordered phase.

This completes a specific two-way transfer. The complex reciprocal work supplies
the exact normalized family and phase arithmetic; non-Archimedean iteration
turns it into a controlled analytic time action, vector field and Abel coordinate.

## 7. Reproducible exact computations

Run `computations/verify_padic_dynamics.py` with Python 3.12. The program uses
only integer arithmetic, Fraction, finite sets, and factorial/binomial formulas.
It imports no lab code and uses no GUI, network, or GPU.

Its retained JSON contains:

| Check | Scope |
|---|---|
| Signed tree coefficients | All labeled trees through seven vertices; recurrence through a_50 |
| Principal fixed pairs | p=2,3,5,7 modulo p^16; independent tree series; every lower precision |
| Full principal congruence graphs | 28,683 states total across four complete graphs; exact image counts and 300 distance tests |
| Analytic fractional time | 15 points, including alpha=0; half-/third-iterate composition, semigroup, inverse, generator invariance modulo p^10 |
| Teichmüller reciprocal branches | Counts 4,16,36,100 at successive odd-prime powers, one pair per ordered label |
| Two-adic integer bases | Bases 3,5,7,9, precisions 2^1 through 2^9, one ordered solution each |
| Parabolic adding machines | Eight complete orbit balls; exact p,p^2,p^3 ladders and 120 time-isometry comparisons |

Every exponential truncation has a full-tail valuation bound; the Mahler
truncations use (14). Finite modular identities are exact. The analytical
statements are proved above. The final recorded run passed in approximately
0.4 CPU seconds.

## 8. What this contributes to the Spire program

Three exact hierarchical objects are available for future representations:

1. Principal reciprocal exponentials have nested congruence-image trees with
   explicitly counted information loss and capture depth.
2. Ordinary unit-base towers have finite root-of-unity phase addresses plus
   p-adic refinement, with the prime-two parity carried explicitly.
3. The normalized reciprocal parabolic family has invariant p-adic orbit balls
   whose iteration is the adding machine, whose reduced periods grow by p,
   and whose analytic Abel coordinate is computable with a tail bound.

For the observed complex Spire, the retained complex period windows keep their
own parameters and physical clocks. The prime-adic construction above supplies
a parallel exact specialization and a controlled model of hierarchical phase
organization. The common rational germ, iterative residue, and reconstructed
phase field are the explicit mathematical links between these representations.

## Primary references and provenance

- Bjorn Poonen, *p-adic interpolation of iterates*, Bull. London Math. Soc. 46
  (2014), 525–527. Theorem 1 and its Mahler construction are the interpolation
  input. [Author PDF](https://math.mit.edu/~poonen/papers/p-iteration.pdf).
- Joshua Holden and Margaret M. Robinson, *Counting fixed points, two-cycles,
  and collisions of the discrete exponential function using p-adic methods*,
  J. Aust. Math. Soc. 92 (2012), 163–178. Proposition 2.1, Theorem 4.1 and
  Proposition 5.3 provide branchwise exponential interpolation and fixed/cycle
  lifting. [Publisher DOI](https://doi.org/10.1017/S1446788712000262).
- Poonen's introduction credits Skolem, Mahler and Lech for interpolation of
  recurrence sequences, and Bell (2006/2008), Bell–Ghioca–Tucker (2010),
  Herman–Yoccoz (1983), and Rivera-Letelier (2003) for preceding p-adic
  iteration/linearization results. These historical relationships are recorded
  as the primary paper's own attribution.
- The normalized-germ formula, residue and coefficient reconstruction are from
  the existing `Reciprocal-Dottie-Theorem-Note` and
  `OpenAI-Math-Greater-Work/research/balanced-dynamics.md` local artifacts.

The downloaded primary PDFs and exact source URLs/hashes are retained under
`sources/padic/`. All old research artifacts and the active lab were preserved.
