# The actual discriminant-23 Dedekind reading on the first Dottie disk

I use $F=\mathbb Q(\sqrt{-23})$ and the splitting field $L$ of $X^3-X-1$. The local Euler proof identifies the actual factors of $\zeta_L$ above every prime of $F$. In $\operatorname{Re} w>1$ the two character series group into finite weighted sums of the three partial Dedekind zeta functions. [Euler product](DedekindDiscriminant23EulerProduct.lean) · [Class series](DedekindDiscriminant23ClassSeries.lean)

## The two theta forms

For every nonzero integral ideal $J$ of $F$, the angular integral reduces to a sum over $x\in J$. The exponent is $-(2\pi/\sqrt{23})tN(x)/N(J)$. Lean uses the bases $1,\omega$, $2,\omega$, and $2,1-\omega$ for the three ideal representatives. Both nonprincipal bases give the same normalized form $2m^2+mn+3n^2$. [Norm sum](DedekindDiscriminant23ClassTheta.lean) · [Three bases and theta sums](DedekindDiscriminant23ThetaForms.lean)

At $t=1$, Poisson summation equates the principal theta reading with its trace-dual reading. The principal sum is at least $2q$ and either other sum is at most $3q/4$, where $q=e^{-2\pi/\sqrt{23}}\ge1/4$. The strict gap forces the trace-dual class of the principal ideal to be principal. The two nonprincipal sums agree, so every class uses its own kernel on both halves of the fold. [Poisson and class profiles](DedekindDiscriminant23ThetaProfiles.lean)

## Same-input identity

Lean pairs each class theta function with its trace dual. The regulator is one and the two units are $1$ and $-1$, so the class normalization is $\alpha_F=1$. The sum of the classes gives the total reading and both nontrivial characters give the principal-minus-nonprincipal reading. Clearing the poles at $0$ and $1$ makes the completed product identity entire, so its equality for $\operatorname{Re} w>1$ carries to all $w$. [Class Mellin pair](DedekindIdealClassThetaPair.lean) · [Continued product](DedekindDiscriminant23CompletedProduct.lean)

The change of variable from the positive radial coordinate to the disk integral gives a factor of two for each of the three folds. If $0<\operatorname{Re} w<1$, the actual completed field reading equals $8P(w)$, where $P$ is the [first disk formula](discriminant23-dottie.md). If $|w-3/4|\le31/128$, the existing ceiling $-1/400$ for $\operatorname{Re} P(w)$ gives a ceiling of $-1/50$ for the real part of the completed field reading. The continued $\zeta_L(w)$ is nonzero throughout this closed disk. [Same-input identity and disk theorem](DedekindDiscriminant23DottieReading.lean)

## Replay

Run the [pinned discriminant-23 replay](replay-discriminant23.ps1) with the checkout and Lean version in the [archive README](README.md). [Exact Lean output](discriminant23-dottie-field-replay-and-axioms.txt)
