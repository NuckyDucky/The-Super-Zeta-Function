# From my ordered exponential stages to the arithmetic of the quartic

The two exponents in my fixed-pair equations give a complex basis ratio. At one such ratio, its lattice recovers the zeta function of the Eisenstein integers. At another, my original quartic assigns an arithmetic sign to every point of the Gaussian lattice. The signs at $`3+8i`$ and $`3-8i`$ are opposite even though both points have squared length 73. I give the formula for the sign and compute which facts about zeros transfer to the resulting number fields.

## 1. The ratio of the two actual logarithms

At a fixed pair of $`F_L(P,Q)=(e^{LQ},e^{-LP})`$, I write $`U=LQ`$, $`V=-LP`$, and $`\tau=U/V`$ when $`V\ne0`$. Then $`e^{V-U}=Q/P=-\tau`$. To realize any $`\tau`$ with positive imaginary part, take a logarithm $`d`$ of $`-\tau`$ and set

$$
V=\frac d{1-\tau},\qquad U=\tau V,\qquad P=e^U,\qquad Q=e^V,\qquad L=U/Q.
$$

Here $`d,V,Q`$ are nonzero. The equality $`Q/P=-\tau`$ gives $`-LP=V`$, and $`LQ=U`$ by construction. Retaining $`d`$ distinguishes the choices $`d+2\pi i k`$ that give the same basis ratio. On my fixed-pair parametrization, $`U=a+iu`$, $`V=a-iu`$, and $`a=u\tan u`$. Their ratio is $`-e^{-2iu}`$. Thus $`u=\pi/6`$ gives the Eisenstein basis $`1,e^{2\pi i/3}`$, and $`u=\pi/4`$ gives the Gaussian basis $`1,i`$. I assign the squared length $`|m+n\tau|^2`$ to each integer pair $`(m,n)`$. The resulting series samples the fixed-pair ratio. An individual finite-period orbit has different data. [Original map and lifted phases](https://github.com/NuckyDucky/The-Super-Zeta-Function/tree/main/lean/SuperZeta)

## 2. Two readings of the Eisenstein field

At $`u=\pi/6`$ the squared length is $`m^2-mn+n^2`$. The Eisenstein integers form a principal ideal domain with six units. Each nonzero ideal therefore occurs six times in the sum over generators. For $`\Re w>1`$ and $`K=\mathbb Q(\sqrt{-3})`$,

$$
\frac16\sum_{(m,n)\ne(0,0)} (m^2-mn+n^2)^{-w}
=\zeta_K(w)=\zeta(w)L(w,\chi_{-3}).
$$

The character $`\chi_{-3}`$ has values $`0,+1,-1`$ on the classes $`0,1,2`$ modulo three. The factorization on the right follows from counting splitting, inert and ramified primes in a quadratic extension. [Eisenstein field data](https://www.lmfdb.org/NumberField/2.0.3.1) · [Aycock and Kobin, Corollary 4.15](https://arxiv.org/pdf/2205.06298)

To obtain the factors from the two project readings, write $`F=\mathcal Z-J`$, $`b=1/2-a/\pi`$, and $`R(a,v)=\pi^{-v}[\zeta(v,b)+\zeta(v,1-b)]`$. My reconstruction and the Hurwitz shift derivative give

$$
F(w/2)=2\pi^{-w}(2^w-1)\zeta(w),\qquad
\partial_aR(\pi/6,w-1)=(w-1)(3/\pi)^wL(w,\chi_{-3}).
$$

In the derivative, the two Hurwitz shifts move in opposite directions. Their difference reads the two nonzero residue classes modulo three, initially by absolute convergence and then by meromorphic continuation. Dividing out the two displayed elementary factors and multiplying gives the same $`\zeta_K`$ as counting generators. This comparison chooses the fixed-pair angle $`u`$ and the Hurwitz angle $`a`$ to have the same numerical value. [My reconstruction and angular derivative](https://github.com/NuckyDucky/The-Super-Zeta-Function/tree/main/archive/2026-11-20-liu-angular-velocity-v002) · [Hurwitz shift differentiation](https://dlmf.nist.gov/25.11.E17)

### Prime weights and a bound over real cutoffs

For the earlier product $`D_7=\zeta^7L(\cdot,\chi_{-3})`$, the coefficients of $`-D_7'/(7D_7)`$ are $`\Lambda(n)(1+\chi_{-3}(n)/7)`$. The coefficients of $`-\zeta_K'/\zeta_K`$ are $`\Lambda(n)(1+\chi_{-3}(n))`$. Here $`\Lambda(p^j)=\log p`$ for $`j\ge1`$, and $`\Lambda(n)=0`$ otherwise. At the inert prime 2 the field weights at $`2,4,8`$ are $`0,2,0`$ times $`\log2`$, recording one prime ideal of norm four. At the ramified prime 3 the weight is $`\log3`$ at each power. [Alpöge's submitted Dirichlet-character argument](https://github.com/Deicyde/riemann-hypothesis/tree/ba2a065656ec7c638baa601994de3e0245ff6665)

Write $`c=L'(1,\chi_{-3})/L(1,\chi_{-3})`$ and let $`\gamma`$ denote Euler's constant. For the prime-power cutoff $`x`$, I center the smoothed sum using the pole term for this field,

$$
G_K(x)=\sum_{n\le x}\Lambda(n)(1+\chi_{-3}(n))(x/n-1)-x\log x+(1+\gamma+c)x .
$$

**Finite interval result.** I obtain $`G_K(x)<0.065597\sqrt{x}`$ for every real $`6501\le x\le4194304`$. In a gap $`[h,k]`$ between successive prime powers the prime sum is affine, so $`G_K''(x)=-1/x`$. The excess above the chord is at most $`(k-h)^2/(8h)`$. If $`M`$ is the maximum of zero and the two endpoint values of $`G_K(x)/x^\theta`$, concavity gives a bound of $`Mx^\theta`$ on the chord when $`0<\theta<1`$. The verifier adds the excess bound and uses directed rounding at 160 bits. The four overlapping windows begin at 6501, 10321, 16384 and 26007. A separate sieve checks every recovered coefficient base through $`2^{22}`$. The initial calibration window beginning at 4096 has a larger bound. The range is in the prime cutoff $`x`$, whereas the Dottie windows specify imaginary parts of zeros. [Directed enclosures](field_windows.json) · [Verifier](check_field_windows.py)

## 3. The branch field supplied by my original quadratic

In the equation I started with, let $`N=465x^2-183x-659`$, $`D=155x^2+396x-936`$ and $`A=N-D`$. Completing the square gives the double cover $`Y^2=f(x)`$, with

$$
f=A^2+4N^2=(A+2iN)(A-2iN).
$$

I choose a branch point $`r`$ on the first factor and study the number field generated by its coordinate. Its Dedekind zeta counts ideals of that field. [Original quartic derivation and curve](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/main/archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md)

**Proposition.** Put $`k=\mathbb Q(i)`$. Then $`F_r=\mathbb Q(r)=k(\sqrt\delta)`$, with

$$
\delta=(-579-366i)^2-4(310+930i)(277-1318i)=-5045155+1027708i .
$$

Indeed $`N`$ has only real roots and $`A`$ has discriminant $`-8239`$, so $`N(r)\ne0`$ and $`i=-A(r)/(2N(r))`$ belongs to $`\mathbb Q(r)`$. The quadratic formula over $`k`$ gives the displayed field. The norm $`N_{k/\mathbb Q}(\delta)=26509772707289`$ is $`2\bmod3`$, so it cannot be a rational square. A square in $`k`$ would have square norm. This proves irreducibility of the quartic. The ratio $`\bar\delta/\delta=N_{k/\mathbb Q}(\delta)/\delta^2`$ is also a nonsquare in $`k`$, since a positive rational that is a square in $`\mathbb Q(i)`$ is a rational square. The two conjugate square roots therefore generate a biquadratic extension over $`k`$. Complex conjugation interchanges the two generators of its Galois group, giving a dihedral normal closure of order eight over $`\mathbb Q`$. [Exact integer calculation](check_gaussian_branch.py)

### The conductor and the sign at every Gaussian integer

Let $`\eta_\delta`$ be the primitive quadratic Hecke character for $`F_r/k`$. Its values $`+1,-1,0`$ at prime ideals of $`\mathbb Z[i]`$ indicate splitting, inertia and ramification in the relative extension. I write $`\eta_\delta((z))`$ for the weight of the ideal generated by $`z`$.

**Theorem.** For every nonzero $`z=m+ni`$, the six original coefficients determine its arithmetic weight through three Legendre symbols, extended by zero on multiples of their prime,

$$
\eta_\delta((m+ni))=\prod_{(p,t)\in S}\left(\frac{m+nt}{p}\right),
\qquad S=\{(41,32),(457,109),(1414835497,516876951)\}.
$$

**Proof.** The discriminant satisfies $`\delta\equiv1\bmod4\mathbb Z[i]`$. Its norm is $`41\cdot457\cdot1414835497`$, with each prime checked by trial division. The element $`h=(1+\sqrt\delta)/2`$ satisfies the monic polynomial $`X^2-X+(1-\delta)/4`$. Its basis $`1,h`$ has discriminant $`\delta`$. The square of the index ideal of the generated order in the maximal order divides $`(\delta)`$. Squarefreeness of its norm forces index one. The relative field discriminant is therefore $`(\delta)`$ and the absolute field discriminant is $`16N_{k/\mathbb Q}(\delta)=424156363316624`$. The conductor–discriminant formula for the quadratic extension identifies $`(\delta)`$ as the finite conductor of its unique nontrivial character. Modulo $`(1+i)`$ the monic polynomial reduces to $`X(X-1)`$ over $`\mathbb F_2`$, so the dyadic Gaussian prime splits. [Milne, *Class Field Theory*, conductor–discriminant formula](https://www.jmilne.org/math/CourseNotes/CFT.pdf) · [Conductor calculation](conductor.json)

At each conductor prime the image of $`i`$ is the residue $`t=5045155/1027708\bmod p`$, obtained by reducing $`\delta`$ to zero. The Gaussian integers have class number one, so the ray class group is the quotient of $`(\mathbb Z[i]/(\delta))^\times`$ by the image of the four units. By the Chinese remainder theorem, the group before quotienting is the product of the three cyclic groups $`\mathbb F_p^\times`$. The character is nontrivial on each factor, since otherwise it could be defined with a smaller conductor. A cyclic group of order $`p-1`$ has a unique nontrivial character of order two, its Legendre symbol. Their product gives the formula. Each $`p\equiv1\bmod8`$, so the images of all four units are squares in each factor. [Milne, ray classes and conductors](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

**Corollary.** Multiplication by $`i`$ preserves the sign. Conjugation obeys

$$
\eta_\delta((z))\eta_\delta((\bar z))=
\prod_{(p,t)\in S}\left(\frac{m^2+n^2}{p}\right).
$$

The first statement holds because $`i`$ is a unit. For the second, multiply the two numerators of the Legendre symbols and use $`t^2=-1\bmod p`$. When the norm is prime to the conductor, it therefore tells me whether the two signs agree. The oriented lattice coordinate determines which sign belongs to which ideal.

| Gaussian generator $`z`$ | Squared length | Sign at $`z`$ | Sign at its conjugate |
|---|---:|---:|---:|
| $`2+3i`$ | 13 | $`-1`$ | $`-1`$ |
| $`1+6i`$ | 37 | $`+1`$ | $`+1`$ |
| $`3+8i`$ | 73 | $`-1`$ | $`+1`$ |

The last row rules out a sign assigned solely by a rational Dirichlet character of the norm. I compared the formula with local splitting in the quartic at 248 Gaussian prime ideals, covering all 168 rational primes through 997. For every split rational prime in that range I counted the roots of the monic polynomial modulo each prime ideal. For inert rational primes I evaluated the square character in the degree-two residue field. I also tested both Gaussian primes above the large conductor divisor. The separate original-quartic check counts roots of its two Gaussian quadratic factors at 13, 37 and 73. [Prime-ideal verifier](check_conductor.py) · [Recorded signs](conductor.json)

### Which zero counts transfer

At $`u=\pi/4`$ the ordered ratio gives the lattice coordinate $`z=m+nU/V=m+ni`$. Since each Gaussian ideal has four generators, for $`\Re w>1`$,

$$
\frac14\sum_{z\in\mathbb Z[i]\setminus\{0\}}\eta_\delta((z))|z|^{-2w}
=L_k(w,\eta_\delta),\qquad
\zeta_{F_r}(w)=\zeta(w)L(w,\chi_{-4})L_k(w,\eta_\delta).
$$

The second identity follows from the split, inert and ramified Euler factors of a quadratic extension and continues meromorphically. The same Hurwitz derivative as in §2 at $`a=\pi/4`$ reads $`(w-1)(4/\pi)^wL(w,\chi_{-4})`$. The additional factor reads the mark specified by my quartic. At any point in the open critical strip the three orders of vanishing add, since the factors are holomorphic there. A certified Riemann zero transfers to a field zero of at least that multiplicity. An exact field count in a rectangle also requires the count of both remaining factors and control on the boundary. A theorem for rational Dirichlet characters applies to the first two factors. The third has Gaussian prime-ideal coefficients and lies in the class of unitary Hecke characters treated by Liu. [Quadratic-extension factorization](https://arxiv.org/pdf/2205.06298) · [Liu, Theorem 1.1](https://hexagonmath.org/pdf/2611.00421v1#page=2) · [Project comparison with Liu](https://github.com/NuckyDucky/The-Super-Zeta-Function/tree/main/archive/2026-11-20-liu-angular-velocity-v002)

**Question about the exponential stages.** The ratio supplies the basis and the quartic supplies a mark defined on that basis. Can an observation of the two marked exponential stages recover the same arithmetic sign at Gaussian prime ideals? Such a rule would need a specific input for $`(m,n)`$. Its values must respect Gaussian unit multiplication and give opposing signs to the two generators above 73. The formula gives an independent answer for every proposed input, including primes reserved for a later test.

**A growth hypothesis in the quartic coordinates.** Let $`\Lambda_{F_r}(n)`$ be the coefficient of $`n^{-w}`$ in $`-\zeta_{F_r}'(w)/\zeta_{F_r}(w)`$. It is an explicit sum over prime ideals with prime-power norm $`n`$; the three-symbol formula gives the signs in its Gaussian factor. Write $`\gamma_{F_r}`$ for the constant term of $`\zeta_{F_r}'(1+v)/\zeta_{F_r}(1+v)+1/v`$ at $`v=0`$. Define

$$
G_{F_r}(x)=\sum_{n\le x}\Lambda_{F_r}(n)(x/n-1)-x\log x+(1+\gamma_{F_r})x .
$$

The testable global hypothesis is that for each $`\epsilon>0`$ there is a constant $`C_\epsilon`$ such that $`|G_{F_r}(x)|\le C_\epsilon x^{1/2+\epsilon}`$ for all $`x\ge2`$. To see why this would control the zeros, integrate $`G_{F_r}(x)x^{-v-2}`$ from 1 to infinity. For $`\Re v>0`$ each prime term integrates to $`n^{-1-v}/[v(v+1)]`$, and the two centering terms give $`-1/v^2+(1+\gamma_{F_r})/v`$. Hence each nontrivial zero $`\rho`$ contributes a pole at $`v=\rho-1`$ with residue $`-\mathrm{ord}_{\rho}(\zeta_{F_r})/[\rho(\rho-1)]`$. Under the growth hypothesis the integral is holomorphic throughout $`\Re v>-1/2`$ by locally uniform absolute convergence. This excludes zeros to the right of the critical line, and the field functional equation reflects the conclusion to the left. The finite bound in §2 concerns $`G_K`$ for the Eisenstein field and supplies a reproducible comparison case for this hypothesis.

## 4. A check with three ideal classes

For a primitive reduced positive form $`[A,B,C]`$ of negative fundamental discriminant $`D`$, let $`\tau=(B+\sqrt D)/(2A)`$, taking $`\Im\sqrt D>0`$. Section 1 realizes it as a fixed-pair ratio. The ideal $`I`$ generated as a lattice by $`A,(B+\sqrt D)/2`$ has norm $`A`$. Each $`\alpha=A(m+n\tau)\ne0`$ in $`I`$ gives the integral ideal $`(\alpha)I^{-1}`$ in the inverse ideal class. All integral ideals of that class occur with exactly $`|\mathcal O_K^\times|`$ generators. Their norms are $`A|m+n\tau|^2=Am^2+Bmn+Cn^2`$. Summing inverse powers of these norms and dividing by the unit count gives the partial zeta function of that ideal class for $`\Re w>1`$. Summing over the ideal classes gives the Dedekind zeta. [Zagier, equation (6)](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/BFb0065299/ModFormsZetaValues.pdf#page=3)

At $`D=-23`$ reduction gives $`[1,1,6],[2,1,3],[2,-1,3]`$, with partial zetas $`Z_0,Z_+,Z_-`$. Changing $`n`$ to $`-n`$ gives $`Z_+=Z_-`$. The quadratic field zeta is $`Z_0+2Z_+`$. The class group has order three, and either nontrivial class character gives $`Z_0-Z_+`$ since its two nontrivial values add to $`-1`$. For $`\theta^3-\theta-1=0`$ the splitting field is the Hilbert class field of $`\mathbb Q(\sqrt{-23})`$. The permutation representation on the three roots is the direct sum of the trivial representation and the induced nontrivial class character. Artin formalism then gives $`\zeta_{\mathbb Q(\theta)}=\zeta\,(Z_0-Z_+)`$, including the prime 23. At norm two the three class counts are $`(0,1,1)`$. Retaining only the principal lattice would miss both ideals. I compared every coefficient through norm 4096 against a separate computation from the character modulo 23 and from the cubic's factorization modulo rational primes. [Serre, *On a theorem of Jordan*, §1](https://www.college-de-france.fr/media/jean-pierre-serre/UPL1210350903026534135_on_a_theorem_of_Jordan.pdf) · [Integer verifier](check_phase_classes.py) · [Results](phase_classes.json)

## Evidence and provenance

This is the first number-field deposit, dated 20 November 2026. I took the two quadratics and the ordered fixed-pair equations from the [quartic derivation](../../archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md) and [tetration preprint, §5](../2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L359-L402). The field-window, Gaussian-branch and three-class scripts collect my earlier local calculations in a standalone replay. The conductor argument and the test against local splitting use those six coefficients as their input. The [marked-direction proof](../../docs/proofs/marked-gaussian-direction.md) gives the angular precision needed at bounded norm. Their formal counterparts are [the reversible lift](../../lean/SuperZeta/DedekindLift.lean) and [arithmetic weights, prime labels and analytic vanishing orders](../../lean/SuperZeta/FieldWeights.lean).

I also [checked the additional Dirichlet factors at the first positive Riemann zero](first-zero.md). Both are separated from zero throughout its input enclosure. This gives order exactly one in each quadratic field zeta at that point. The proof of the conductor, the ray class interpretation and the field factorizations are the written number-theoretic arguments above. The directed computations give the finite real-cutoff bound and the numerical zero transfer.

## Reproduce the arithmetic

Run these commands from this directory in Python 3.12. The first three use the standard library. The last uses python-flint 0.9.0. All inputs are deterministic. The last line of the window output also gives a 192-bit evaluation of the scalar $`2+\log(3/(4\pi^2))+2c`$. Only the 160-bit enclosures enter the finite inequality.

~~~sh
python check_gaussian_branch.py
python check_conductor.py
python check_phase_classes.py
python check_field_windows.py
~~~

For the multiplicity transfer, run `python -B check_first_zero.py` with python-flint 0.9.0 and compare with [the recorded complex enclosure](first-zero.json).

The all-vector sign formula uses the conductor and ray class argument above. The finite prime tests check its implementation. The coefficient and window checks address the individual fields and cutoffs stated in their respective sections.

