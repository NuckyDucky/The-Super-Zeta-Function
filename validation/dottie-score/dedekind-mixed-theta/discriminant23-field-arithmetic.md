# Field arithmetic for the discriminant-23 Dottie reading

I use the splitting field $L$ of $X^3-X-1$ and its quadratic subfield $F=\mathbb Q(\sqrt{-23})$. Lean proves that the cyclic cubic step $L/F$ is unramified at every finite prime. If an inertia element is nonidentity, it cycles the three roots, and all three have the same residue $r$. The root sum gives $3r=0$. For two distinct roots $a,b$, their cubic equations give $a^2+ab+b^2=1$, so reduction gives $3r^2=1$. These equations contradict each other in any nontrivial residue ring. [Lean inertia and different](DedekindDiscriminant23Unramified.lean)

Put $\omega=(1+\sqrt{-23})/2$. Lean proves $\omega^2=\omega-6$. The trace matrix of $1,\omega$ has rows $(2,1)$ and $(1,-11)$, so its determinant is $-23$. The square of the lattice index divides $23$, giving the full integral basis $1,\omega$. The relative different is trivial, so the discriminant formula gives $|\operatorname{disc}(L)|=23^3=12167$. Lean also gives zero real places and three complex places. With the library's $2(2\pi)^{-w}\Gamma(w)$ convention at a complex place, the completion factor of $L$ is $8$ times the cube of the factor $23^{w/2}(2\pi)^{-w}\Gamma(w)$. [Integral basis, signature, and normalization](DedekindDiscriminant23Integers.lean)

## The two norm forms

Let $P$ be the ideal defined by $\omega\mapsto0$ modulo $2$. Lean proves $NP=2$ and that its elements are exactly $2m+n\omega$ for integers $m,n$. The two forms used in the [first disk proof](discriminant23-dottie.md) satisfy

$$
N_{F/\mathbb Q}(m+n\omega)=m^2+mn+6n^2,
\qquad
\frac{N_{F/\mathbb Q}(2m+n\omega)}{NP}=2m^2+mn+3n^2.
$$

The units are $1$ and $-1$. This fixes the multiplicity from changing the sign of a nonzero generator. [Norm forms and units](DedekindDiscriminant23NormForms.lean)

## The three classes

Minkowski's bound gives a representative of norm at most $3$ in every ideal class. At norm $p=2$ or $3$, the ideal comes from one of the two roots $0,1$ of the polynomial for $\omega$ modulo $p$. Denote the ideals by $P_{p,0}, P_{p,1}$. Lean checks the products

$$
P_{2,0}P_{2,1}=(2),\qquad
P_{2,0}P_{3,0}=(\omega),\qquad
P_{2,1}P_{3,1}=(\omega-1).
$$

Thus the class of $P=P_{2,0}$, its inverse, and the principal class exhaust the class group. The form for $N_{F/\mathbb Q}$ gives no element of norm $2$. The only elements of norm $4$ are $2$ and $-2$, and $P^2\ne(2)$ since the two norm-two primes are distinct. Lean therefore proves that the three classes are distinct and that the class number is $3$. [Small representatives](DedekindDiscriminant23ClassRepresentatives.lean) · [Class group](DedekindDiscriminant23ClassNumber.lean)

The first disk sign applies to the explicit class product. To carry it to the actual completed reading, the next Lean steps identify the class-group Artin map for $L/F$, express the zeta factors by the ideal sums, and match their continuation to the folded Mellin formula.

## Replay

Use the toolchain and pinned dependencies in the [archive README](README.md). This command checks the existing disk and the field arithmetic in one run. [Exact theorem types and axioms](discriminant23-field-replay-and-axioms.txt)

~~~powershell
pwsh ./validation/dottie-score/dedekind-mixed-theta/replay-discriminant23.ps1 `
  -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin>
~~~
