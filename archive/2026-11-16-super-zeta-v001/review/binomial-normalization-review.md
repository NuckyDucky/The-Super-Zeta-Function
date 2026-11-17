# Independent review: binomial normalization and its deformed zeta

16 November 2026. Reviewed `research/binomial-normalization.md`,
`research/binomial-deformed-zeta.md`, and
`computations/verify_binomial_normalization.py` independently.

## Exact product and normalization

The duplication formula gives
\(B_n=\Gamma(n+1/2)/(\sqrt\pi\Gamma(n+1))\). Consequently
\(D_n=\pi nB_n^2=n\Gamma(n+1/2)^2/\Gamma(n+1)^2\), and the finite
Barnes product is exactly
\[
\prod_{n=1}^N D_n
=\Gamma(N+1)\left[\frac{G(N+3/2)}{G(3/2)G(N+2)}\right]^2.
\]
The shifts, powers, initial factor \(G(3/2)\), and \(2\pi n\) radial
base all check out. Expanding \(F(x)=\log G(x+1)\), the shifted
difference is \(-F'(N)-3F''(N)/4+O(N^{-1})\). It cancels every
constant against Stirling's formula for \(\log\Gamma(N+1)\), leaving
precisely \(-\log N/4+O(N^{-1})\). Thus
\[
\lim N^{1/4}\prod C_n=e^{\sin d/2}/G(3/2)^2
\]
has no additional exponential or \(\pi\) factor.

The positive-kernel identity was independently differentiated and
integrated. The partial fraction factor is exactly eight:
\[
\tanh(t/4)/t=8\sum_{j\ge0}[4\pi^2(2j+1)^2+t^2]^{-1}.
\]
Its finite geometric identity gives the claimed sign and next-coefficient
remainder for every positive n. This establishes the strict Stirling-tail
control, including all coefficients stated in the note.

The finite-cutoff identity \(\log S_N=\log K+T_D-T_R\), the signs in
the digamma/Hurwitz approximation to \(T_D\), the radial logarithmic
tail, and the combined error bound agree. The recurrence for the ordinary
Barnes correction follows directly from its stated finite difference.
The displayed first two Euler–Maclaurin terms have the correct signs and
the correct \(4\pi^2\) and \(8\pi^2\) denominators.

## All-order meromorphic deformation

The combined logarithmic coefficients have even radial orders and odd
constant Stirling orders. Exponentiation gives the stated recurrence
for \(E_m(w,L)\). Its logarithmic degree is at most
\(2\lfloor m/2\rfloor\). Fixed-order controlled remainders give normal
convergence of the subtracted series on \(\Re s>-M\), jointly on compact
sets in w. This proves the all-order continuation and the stated possible
polar hyperplanes.

The highest logarithmic contribution follows from the graded leading
radial relation \(A^2=R^2-4\log^2R\): it is the coefficient of
\((1+L^2/(\pi^2n^2))^{w/2}\). Hence the even-order coefficient is
\(\pi^{-2j}\binom{w/2}{j}\); the next odd order is multiplied by
\(-w/4\). The factorials in the Laurent coefficients and all pole orders
in the note follow with the stated logarithmic-moment derivative convention.
The diagonal \(w=-s\) makes both negative-integer leading coefficients
nonzero, so its complete negative pole list and orders check out.

The finite-part calculation uses
\(\sum[\log C_n+1/(4n)]=\log K+\gamma/4\); this cancels the Laurent
constant of \(-\zeta(s+1)/4\) and gives exactly \(\log K\).
On the spectral diagonal the apparent pole at zero instead contributes
\(+1/4\), giving
\[
Z_\Lambda(0)=-1/4,\qquad
Z_\Lambda'(0)=-\log(2\pi)/2-\log K,
\quad\det_\zeta\Lambda=\sqrt{2\pi}K.
\]
These constants and signs are internally consistent and agree with the
independent numerical closed-form evaluation.

## Replay and source comparison

The verifier passed in the documented runtime with `PYTHONPATH=work/deps`.
Its numerical work took about 1.95 seconds. It checked the Barnes finite
identity at five cutoffs, exact formal coefficients through order eight,
1,024 directed radial isolations, the strict Stirling remainder, and both
controlled corrected product enclosures. It returned
\[
K=1.2250017073142016852999108811594267460129879373138051\ldots,
\]
\[
\det_\zeta\Lambda
=3.0706239160250272388866383032834685303194664518609132\ldots.
\]
The quoted errors and effective-spectrum constants match the JSON record.

The published gamma/Stirling and Barnes inputs were checked against NIST
DLMF §§5.11 and 5.17, and the cosh product against §4.36. The family-specific
normalization, finite parts, and pole coefficients are derived explicitly
in the two notes.

One routine verifier hardening was requested and applied: assert the endpoint signs
for the initial Dottie bracket \([0.73,0.74]\) before bisection. The
analytic bracket and all derived numerical conclusions are unchanged.
The final replay with these checks passed. No review issue remains.
