# Gaussian endpoint signs and the parity of a real target

I tested the two heights $t_-=T_D-1/16$ and $t_+=T_D+1/16$ from my period-640 Dottie construction. The open interval between them contains no ordinary Riemann zero. For the quadratic Hecke character of my quartic field, I can bound both signed values more tightly than in the earlier contour calculation. Both bounds still admit either sign. This leaves the parity of the Gaussian zero count at target zero open. [Frozen height and field](gaussian-endpoints-input.json) · [Earlier Gaussian contour](../2026-11-20-gaussian-two-root-transition-v001/README.md)

## Which targets have odd multiplicity?

Use $k=\mathbb Q(i)$, $\delta=-5045155+1027708i$ and $K=k(\sqrt\delta)$. Write $\eta_\delta$ for the quadratic character of the Gaussian ideals. With $B=\sqrt{106039090829156}/(2\pi)$ and $S=B^2\lvert\Gamma(2+iT_D)\rvert$, the common scale used in the contour experiment is

$$
f(w)=\frac{B^w\Gamma(w)L(w,\eta_\delta)}{S},
\qquad b_\pm=f(1/2+it_\pm).
$$

The functional equation gives $f(1-\bar w)=\overline{f(w)}$, so $b_-$ and $b_+$ are real. Fix a real $v$ different from both. Count the solutions of $f(w)=v$ in the open symmetric rectangle $-1<\Re w<2$, $t_-<\Im w<t_+$, with their multiplicities. Call the count $N(v)$. Then

$$
N(v)\text{ is odd}\quad\Longleftrightarrow\quad
\min(b_-,b_+)<v<\max(b_-,b_+).
$$

Along the critical line I apply the endpoint theorem to the real analytic function $t\mapsto f(1/2+it)-v$. At a zero of order $m$, its sign changes exactly when $m$ is odd. Lean obtains the entire finite set of interior zeros from analyticity and compactness, and factors out each zero to its actual analytic order. Parametrization by $w=1/2+it$ preserves that order, since the leading complex Taylor coefficient is multiplied by the nonzero factor $i^m$. Each solution off the line has a reflected partner of the same order, so including both changes the count by an even number. The Lean theorem `reflected_total` checks the identity $N=N_{\mathrm{line}}+2N_{\mathrm{right}}$ for every finite family with this reflection and these multiplicities. The parity statement counts the open rectangle and does not require a winding computation along its boundary. If $v$ equals an endpoint reading, a boundary solution must be treated separately. [Lean proof of endpoint parity](../../lean/SuperZeta/GaussianEndpointParity.lean) · [Field character and conductor](../2026-11-20-dedekind-phase-v001/README.md)

## Measurements at the two endpoints

| Quantity | Lower endpoint | Upper endpoint |
| --- | ---: | ---: |
| Riemann zeros up to the endpoint, with multiplicity | 18,947,484,639,341 | 18,947,484,639,341 |
| Signed base-field Hardy product, rounded outward | $[0.2564,0.2576]$ | $[0.6505,0.6515]$ |
| Upper bound on the absolute value of the normalized Gaussian completion $f$ | $3.584\times10^{-19}$ | $2.945\times10^{-19}$ |
| Sign of the Gaussian completion | Unresolved | Unresolved |

I used FLINT to count ordinary zeta zeros at both ends of each interval-arithmetic enclosure of $t_\pm$. Monotonicity and agreement of the four integers give the count at the two exact heights. The signed base-field completion is a positive multiple of the product of the Riemann and Dirichlet beta Hardy values. Both products are positive here. Thus $\Lambda_K=c\Lambda_k\Lambda_{\eta_\delta}$, with $c>0$, transfers the Gaussian sign to the quartic at each endpoint. This calculation uses only local readings and the field factorization. Sutherland's verification of the ordinary and Dirichlet statements has a different scope. [Ordinary counts and positive scale conversion](endpoint-transfer.json) · [Base-field readings and error proof](gaussian-endpoints.md) · [Sutherland's report](https://math.mit.edu/~drew/grh/)

**A consequence for the moving target.** Every real target with $\lvert v\rvert\ge3.584\times10^{-19}$ has even count in the rectangle. The earlier contour gave an exact count of two on its two certified target intervals beginning at $1.05238\times10^{-18}$ in magnitude. The parity result also covers smaller targets. For example, at $v=3.0\times10^{-19}$ the upper endpoint is already below the target, so the count there is odd exactly if the lower endpoint exceeds $v$. At $v=0$ both signs still matter.

## How the split prime at 73 enters the bound

The two conjugate prime ideals above $73$ have opposite signs. In their combined Euler factor $(1-73^{-2w})^{-1}$, all odd powers of $73^{-w}$ have coefficient zero. I applied that cancellation at 404 split primes through 13,697 to bound the omitted absolute coefficients, then used a smoothed functional equation at each endpoint. The proved error radius in Hardy units falls from approximately $5.998\times10^{12}$ to below $6.564\times10^9$. Conversion to the common scale $S$ gives the two bounds in the table. [Coefficient estimate, gamma error and tail proof](endpoint-refinement.md) · [192-bit results](endpoint-refinement.json) · [Earlier Hardy estimate](gaussian-hardy-endpoints.md)

At the lower endpoint, extending the finite sum from norm $2^{20}$ to $2^{21}$ changes its value from $-0.54736$ to $+0.93525$. On the following block alone, the sum of the **absolute** cosine contributions exceeds $432.65$. The arithmetic now isolates the kind of information that would improve the sign test. A bound on the **signed** remainder would preserve cancellation between different norms. The analytic parity theorem is proved in Lean. The endpoint enclosures use directed arithmetic together with the analytic estimates linked above.

## Reproduction and provenance

From this directory, run the following with Python 3.12 and python-flint 0.9.0. The replay reads the preceding immutable contour record, recomputes the four numerical records, checks enclosure overlap across builds, and checks the endpoint bounds and signs in the table.

~~~sh
python -B replay.py
~~~

From the repository root, run `python tools/check_lean.py` with the pinned Lean 4.19.0 toolchain. The project audit checks dependencies on every imported theorem. [Module index](../../lean/README.md) · [Arithmetic replay](replay.py)

This November 20 snapshot uses the original ERH-target-check height, two base and Hardy scripts, input and records. Their local imports now use the archived height and conductor in [gaussian_inputs.py](gaussian_inputs.py), copied from the preceding snapshot. I reformatted the two working notes for GitHub and retained their analytic estimates. The count comparison, split-prime estimate, refined endpoint records and Lean parity proof accompany this deposit. Michael Rubinstein's smoothed functional equation supplies the analytic method used to compare the finite sum and its tail. [Rubinstein, *Computational methods and experiments in analytic number theory*](https://arxiv.org/abs/math/0412181)
