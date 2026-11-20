# The first Riemann zero in the two quadratic fields

The first positive Riemann zero is a simple zero of both $\zeta_{\mathbb Q(\sqrt{-3})}$ and $\zeta_{\mathbb Q(i)}$. I transfer its multiplicity by evaluating the additional factor in each product at the enclosure of that same zero. The Riemann variable here is $w$, related to the corrected super zeta by $w=2s$.

Write $\rho$ for the first positive critical-line zero. I used FLINT's certified indexed zero routine to enclose $\rho$ at 160 bits. The imaginary part lies in $14.134725141734693790457251983562470270784257116\pm3.13\times10^{-46}$. The following coarse enclosures are rounded outward from the [complete readings](first-zero.json).

| Quantity at $\rho$ | Enclosure of its magnitude |
| --- | --- |
| $\zeta'(\rho)$ | $(0.7931604,0.7931605)$ |
| $L(\rho,\chi_{-3})$ | $(2.8968690,2.8968691)$ |
| $L(\rho,\chi_{-4})$ | $(2.2285140,2.2285141)$ |

The derivative enclosure gives order one for the Riemann factor. Each additional factor has order zero since its magnitude is bounded away from zero throughout the input enclosure. Adding orders in the two quadratic factorizations gives exactly one at $\rho$ in each product. For the branch field from the original quartic the same argument gives $1+\mathrm{ord}_\rho L_{\mathbb Q(i)}(w,\eta_\delta)$. Evaluating this additional Hecke factor at $\rho$ is a separate calculation.

For each quadratic character I checked the Dirichlet evaluation against the difference of Hurwitz values at shifts $1/q$ and $(q-1)/q$, multiplied by $q^{-\rho}$ for $q=3,4$. Both evaluations use FLINT interval arithmetic. The calculation treats this one point. The previously archived eleven high Riemann zeros are inputs to the multiplicity argument in the main paper, with separate factor counts required for their windows.

**Reproduction.** Run the command below from this directory and compare its output with the linked JSON. I used Python 3.12.14 and python-flint 0.9.0. The program checks each character table, overlap of the independent formulas, and the strict lower bounds on all three magnitudes. [Verifier](check_first_zero.py) · [FLINT indexed zeta zeros](https://flintlib.org/doc/acb_dirichlet.html) · [Quadratic-field factorization](https://arxiv.org/abs/2205.06298)

~~~sh
python -B check_first_zero.py
~~~

