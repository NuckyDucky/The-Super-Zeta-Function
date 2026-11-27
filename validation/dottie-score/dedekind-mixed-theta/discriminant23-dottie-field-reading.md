# The actual discriminant-23 Dedekind reading on the first Dottie disk

I use $F=\mathbb Q(\sqrt{-23})$ and the splitting field $L$ of $X^3-X-1$. The local Euler proof identifies the actual factors of $\zeta_L$ above every prime of $F$. In $\operatorname{Re} w>1$ the two character series group into finite weighted sums of the three partial Dedekind zeta functions. [Euler product](DedekindDiscriminant23EulerProduct.lean) · [Class series](DedekindDiscriminant23ClassSeries.lean)

## The two theta forms

For every nonzero integral ideal $J$ of $F$, the angular integral reduces to a sum over $x\in J$. The exponent is $-(2\pi/\sqrt{23})tN(x)/N(J)$. Lean uses the bases $1,\omega$, $2,\omega$, and $2,1-\omega$ for the three ideal representatives. Both nonprincipal bases give the same normalized form $2m^2+mn+3n^2$. [Norm sum](DedekindDiscriminant23ClassTheta.lean) · [Three bases and theta sums](DedekindDiscriminant23ThetaForms.lean)

At $t=1$, Poisson summation equates the principal theta reading with its trace-dual reading. The principal sum is at least $2q$ and either other sum is at most $3q/4$, where $q=e^{-2\pi/\sqrt{23}}\ge1/4$. The strict gap forces the trace-dual class of the principal ideal to be principal. The two nonprincipal sums agree, so every class uses its own kernel on both halves of the fold. [Poisson and class profiles](DedekindDiscriminant23ThetaProfiles.lean)

## Same-input identity

Lean pairs each class theta function with its trace dual. The regulator is one and the two units are $1$ and $-1$, so the class normalization is $\alpha_F=1$. The sum of the classes gives the total reading and both nontrivial characters give the principal-minus-nonprincipal reading. Clearing the poles at $0$ and $1$ makes the completed product identity entire, so its equality for $\operatorname{Re} w>1$ carries to all $w$. [Class Mellin pair](DedekindIdealClassThetaPair.lean) · [Continued product](DedekindDiscriminant23CompletedProduct.lean)

The change of variable from the positive radial coordinate to the disk integral gives a factor of two for each of the three folds. If $0<\operatorname{Re} w<1$, the actual completed field reading equals $8P(w)$, where $P$ is the [first disk formula](discriminant23-dottie.md). If $|w-3/4|\le31/128$, the existing ceiling $-1/400$ for $\operatorname{Re} P(w)$ gives a ceiling of $-1/50$ for the real part of the completed field reading. The continued $\zeta_L(w)$ is nonzero throughout this closed disk. [Same-input identity and disk theorem](DedekindDiscriminant23DottieReading.lean)

## The full low-height strip

If $1/2\le\operatorname{Re} w<1$ and $|\operatorname{Im} w|\le1/2$, the theta integrals give $|A|\le4/5$, $u=\operatorname{Re} C\ge1/8$, and $|\operatorname{Im} C|\le u/2$. Multiplying by $w(1-w)$ gives the product $(w(1-w)A-3/2)C^2$. The regular term has real part at most $3u^2/4$ and the pole term contributes at most $-9u^2/8$. The folded formula agrees at $w$ and $1-w$, so the same inequality holds on the other half. [Mellin bounds](DottieClassMellinBounds.lean) · [Weighted class product](Discriminant23DottieDisk.lean)

If $0<\operatorname{Re} w<1$ and $|\operatorname{Im} w|\le1/2$, the actual field reading times $w(1-w)$ has real part at most $-3/64$. This proves $\zeta_L(w)\ne0$ across the entire band. [Field theorem](DedekindDiscriminant23DottieReading.lean) · [Lean output and axioms](discriminant23-low-strip-replay-and-axioms.txt)

## The character fold at the same input

Write $M_K(w)$ for the pole-cleared completed reading of $K$ and $C(w)$ for the full principal-minus-nonprincipal fold. If $0<\operatorname{Re}w<1$, Lean gives $M_L(w)=M_F(w)C(w)^2$ at that very $w$. So $\zeta_L(w)=0$ if and only if $\zeta_F(w)=0$ or $C(w)=0$. If the zeros of $\zeta_F$ are on the line, Dedekind RH for $L$ is equivalent to $\operatorname{Re}w=1/2$ for every strip zero of $C$. [Base-field continuation](DedekindDiscriminant23CompletedProduct.lean) · [Zero and RH equivalences](DedekindDiscriminant23DottieReading.lean)

If $|\operatorname{Im}w|\le7/6$ in that strip, the character-fold real part is at least $1/96$ and the real part of $M_F(w)$ is at most $-3/13$. Lean gets the character bound from the height-dependent cosine loss. It gets the base bound by multiplying the total fold's norm allowance $216/143$ by the pole weight's norm allowance $11/6$ and subtracting the pole constant $3$. [Height-dependent Mellin bound](DottieClassMellinBounds.lean) · [Bounds on both factors](DedekindDiscriminant23DottieReading.lean)

If I multiply the completed reading of $L$ by $w(1-w)/C(w)^2$, the result is $M_F(w)$ and has real part at most $-3/13$. Lean proves this weight is analytic at every point of the band. The product identity also gives $|M_L(w)|\ge1/39936$, so the actual Dedekind continuation is nonzero throughout this entire band. The zero-exclusion theorem takes only the strip and height inequalities. [Weighted reading and zero exclusion](DedekindDiscriminant23DottieReading.lean) · [Exact Lean output](discriminant23-factor-reading-replay-and-axioms.txt)

## The Dirichlet input at 23

Take a primitive 23rd root of unity $x$ and set $\eta=\sum_a x^a$, with $a$ running through the eleven nonzero squares modulo $23$. Lean checks $\eta^2+\eta+6=0$. So $(1+2\eta)^2=-23$ and the quadratic base $F$ embeds in $\mathbb Q(x)$. The cyclotomic theorem gives Dedekind RH for $F$ if the Dirichlet strip-zero statement holds for each character modulo $23$. [Quadratic period and embedding](DedekindDiscriminant23DirichletReduction.lean) · [Cyclotomic transfer](DedekindCyclotomicSubfields.lean)

If that modulus-23 input holds, Lean gives the exact equivalence
$$
\operatorname{RH}(L)\quad\Longleftrightarrow\quad
C(w)\ne0\text{ for every }w\text{ with }1/2<\operatorname{Re}w<1
\text{ and }|\operatorname{Im}w|>7/6.
$$
The certified band covers the smaller heights. The field's reflected zero relation accounts for the left half at the same height. [Higher-right theorem](DedekindDiscriminant23DirichletReduction.lean) · [Exact Lean output](discriminant23-dirichlet-mod23-replay-and-axioms.txt)

## Replay

Run the [pinned discriminant-23 replay](replay-discriminant23.ps1) with the checkout and Lean version in the [archive README](README.md). [Exact Lean output](discriminant23-dottie-field-replay-and-axioms.txt)

Add `-DirichletMod23` to the same command to replay the cyclotomic dependencies and the modulus-23 theorem. [Modulus-23 replay output](discriminant23-dirichlet-mod23-replay-and-axioms.txt)
