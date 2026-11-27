# Prime splitting and Euler factors at discriminant 23

Take the splitting field $L$ of $X^3-X-1$ and its quadratic subfield $F=\mathbb Q(\sqrt{-23})$. The extension $L/F$ is cyclic of degree three. Lean checks unramifiedness at finite primes and uses the complex places of $F$ at infinity. The degree agrees with the checked class number of $F$, so the image of $L$ in the separable closure of $F$ is the small Hilbert class field. [Field arithmetic](discriminant23-field-arithmetic.md) · [Hilbert class field proof](DedekindDiscriminant23Hilbert.lean)

For each prime $\mathfrak p$ of $F$, put $d=\operatorname{ord}([\mathfrak p])$. Every prime over $\mathfrak p$ has residue degree $d$, and their number times $d$ is three. If $[\mathfrak p]=1$, we get three primes of degree one. If $[\mathfrak p]\ne1$, we get one prime of degree three. [Prime splitting and residue degrees](DedekindDiscriminant23Hilbert.lean)

Put $X=(N\mathfrak p)^{-w}$ and evaluate a faithful class character at $[\mathfrak p]$ to get $u$. For the principal class the product of the three denominators is $(1-X)^3$. For either other class, $u$ is a nontrivial cube root of unity and $(1-X)(1-uX)(1-u^2X)=1-X^3$. These are the denominators from the actual primes above $\mathfrak p$. [Exact local identity](DedekindDiscriminant23EulerProduct.lean)

If $\operatorname{Re} w>1$, Lean multiplies those local identities to give
$$
\zeta_L(w)=\zeta_F(w)\,L_{\chi}(w)\,L_{\chi^2}(w),
\qquad
L_{\chi^k}(w)=\sum_{\mathfrak a\ne0}\chi([\mathfrak a])^k (N\mathfrak a)^{-w}.
$$
The next equality is between these class series after completion and the folded Mellin readings used on the first Dottie disk. [Actual Dedekind-zeta factorization](DedekindDiscriminant23EulerProduct.lean) · [First disk proof](Discriminant23DottieDisk.lean)

## Replay

Use the pinned checkout and compiler in the [archive README](README.md). This command checks the field arithmetic, first disk, splitting law, and Euler product. [Exact Lean output and axioms](discriminant23-hilbert-and-euler-replay-and-axioms.txt)

~~~powershell
pwsh ./validation/dottie-score/dedekind-mixed-theta/replay-discriminant23.ps1 `
  -AxiomCheckout <upstream-checkout> -LeanBin <pinned-toolchain-bin>
~~~
