# Independent numerical-scope review of the final root computations

16 November 2026. Reviewed the complete final versions of
`verify_superzeta_residues.py`, `verify_residue_period.py`, and
`verify_laplace_barnes.py`, together with their retained JSON evidence.
The Laplace script was authored by this research role; its review below
therefore concentrates on independent reconstruction of its stored
containments and source provenance. The first two scripts received a
separate proof/implementation audit and independent essential calculations.

**Result:** no actionable numerical-rigor or evidence-scope issue remains
in these three scripts at the reviewed version. No production script was
changed during this review.

## 1. Independent reviewer calculations

`computations/review_numerical_scopes.py` performs bounded additional checks
and writes `numerical-scope-review-results.json`. It passed in approximately
1.5 seconds. It verifies:

- An exact symbolic derivation of the rationalized decaying superzeta kernel.
- Three independent 90-digit integrals using a different lower-endpoint
  variable, compared with the directed production reference at an explicitly
  stated point-consistency tolerance.
- Four manual AGM enclosures contained by independently constructed exact
  97-term positive-series intervals, including the endpoint-near case.
- All twelve Laplace finite-sum-plus-tail containments, reconstructed from
  the serialized finite sums and radii, and checked against the frozen
  reference file read afresh.
- The frozen reference's exact SHA256 against its provenance record.

The root author's master replay and package manifest provide the final
production-script hashes and replay log. This review adds independent
mathematical and numerical evidence.

## 2. Shifted-superzeta integrals: the kernel, branch, and tail are correct

The production integral is the exponentially decaying remainder

H(v)=d_v log E_epsilon(-v)-v^(-1/2).

It includes the difference between the half-integer reference density and
the leading continuum density, together with the relative cosine correction.
Writing u=sqrt(v), it is exactly

H(u²)=(tanh(u)-1)/u
+(1-u tanh(u))/(epsilon²cosh²(u)+u²).

Combining the fractions and using
cosh²(u)(tanh(u)-1)=-(1+exp(-2u))/2 gives precisely the implemented
`Hu` numerator and denominator. The separate symbolic calculation reduces
their difference to zero.

Consequently the script's reconstruction

S(s,w)=Gamma(s-1/2)w^(1/2-s)/(sqrt(pi)Gamma(s))
+sin(pi s)/pi * integral_0^infinity t^(-s)H(w+t)dt

has the correct Gamma factor and captures the full shifted spectrum. The
computed integral is this H remainder, with the explicitly subtracted
v^(-1/2) term; its identity specifies the numerical observable.

The lower substitution u=sqrt(w)+q^4 gives the power q^(3-4s) and the
factor 8u(2sqrt(w)+q^4)^(-s). For every selected quarter-integer s the
power is a nonnegative integer, removing the endpoint singularity. The
analytic logarithm receives the actual Acb analyticity flag. The remaining
exp/cosh/rational operations are analytic on every integration ball where
their denominator enclosure excludes zero; unresolved denominator balls
produce nonfinite enclosures and are subdivided by the certified integrator.
The final result is required to be finite with an imaginary enclosure
containing zero.

The u=120 tail bound follows directly, for positive real epsilon and u>=120,
from

|H(u²)| <= 4exp(-2u)[(1+u)/epsilon²+1/u].

Multiplying by 2u(u²-w)^(-Re(s)) gives the three powers in the implemented
tail. For Re(s)>0, the factor (1-w/120²)^(-Re(s)) bounds the shifted
power upward; for Re(s)<=0 the value one is a valid upper bound. Each
remaining exponential-power integral uses

integral_T^infinity u^a exp(-2u)du
<=T^a exp(-2T)/(2-max(a,0)/T).

All denominators are checked positive. The tail is added as a directed
radius to the certified real integral enclosure. At s=0 the Gamma term's
derivative is -2sqrt(w), so the implemented determinant comparison against
4E_epsilon(-w) has the correct sign and normalization.

The sixteen directed cases are epsilon=1,2; w=1,4; and
s=-1/4,0,1/4,3/4. The twelve actual-spectrum positive-integer trace
comparisons use 160-digit point roots, with an independently proved tail;
they are labelled point spectral comparisons rather than root isolations.
Their tail uses |u_n|>pi(n-1/2) and
|u_n²+w|>=|u_n|²-w, with the first omitted index n=129. The stated
eta factor and integral majorant have the correct conservative indexing.

The independent reviewer integrals use the original shifted variable
t=q^4 near zero, instead of u=sqrt(w)+q^4. All three point comparisons
pass the stated 10^-75 consistency tolerance. Their working precision and
point status are recorded separately from the production directed balls.

## 3. Elliptic periods: exact complements and correctly directed AGM brackets

The exact Fraction coefficient recurrence is the hypergeometric equation
for B_n². The factorial beta-moment identity and the coverage increments
have the correct normalization. The latter concern the explicitly defined
uniform-endpoint minor-arc model.

The manual AGM inputs are 1 and sqrt(1-z), formed from the exact rational
complement. This is the appropriate stable input at z=1-10^-40. At each
step the true arithmetic iterate lies above the AGM limit and the geometric
iterate below it. Thus lower(1/a_j) and upper(1/b_j) are correctly directed
period bounds. The interval reconstructed from these endpoints contains
the entire real bracket. Sixteen iterations and the recorded width check
supply the stated 145-digit-scale manual enclosure.

Acb elliptic_k receives the parameter m=z, consistently with
M(z)=2K(z)/pi. Near z=1 it receives a rounded parameter ball, whose
uncertainty is amplified by the endpoint derivative. The manual AGM and
builtin Arb AGM instead receive the exact rational complement; the record
explicitly preserves this conditioning distinction. Overlap with the wider
Acb result is the correct consistency check. The 220-digit point reference
and its conversion precision are more than sufficient for containment in
the manual interval, and remain separately labelled as point evidence.

The positive-series lower bound and tail are directed ball evaluations of
exact nonnegative terms. The independent reviewer constructs the stronger
terms 0 through 96 using exact Fractions, then an exact geometric moment
tail. Each whole manual AGM enclosure lies inside that independent series
interval. Near the logarithmic endpoint the series bound is intentionally
coarse; the narrow certificate is supplied by AGM.

The three modular/theta comparisons are 180-digit point checks with
q=exp(pi i tau), parameter lambda=theta2^4/theta3^4, and the selected
principal continuation. They are explicitly not interval certificates.

## 4. Chord density: correct transformed integrand and evidence classification

For the product density, x=exp(-2u) gives exactly

x^n f_Z(x)|dx/du|
=(2/pi)exp(-(2n+1)u)/AGM(1,exp(-u)).

The first geometric AGM iterate gives
AGM(1,exp(-u))>=exp(-u/2). Therefore the implemented tail beyond T=160 is

2 exp(-(2n+1/2)T)/(pi(2n+1/2)).

The rate (4n+1)/2 and every factor match the actual substitution. The
script evaluates this tail with directed arithmetic.

The stored truncated-integral enclosure is derived from the exact moment
theorem, positivity, and this analytic tail. The code and JSON expressly
identify that logical source. Its 100-digit point quadrature is a separate
consistency calculation with an explicit tolerance; it is not used as a
directed quadrature certificate. This preserves the distinction between an
analytic enclosure derived from an exact theorem and a numerically enclosed
integration procedure.

## 5. Laplace/Barnes: safe reconstruction of the retained containments

The script uses a 512-bit, 400-step directed rational isolation of nu,
832-bit coefficient arithmetic, and an independently cached 250-digit
Dirichlet-eta point calculation. The integer degeneracy and sign checks
are exact. Independent 90-digit coefficient/asymptotic quadratures have
their own cutoffs, tails and point labels.

The coupling certificate combines directed finite Barnes sums with the
proved positive analytic tail using q=R_L²/epsilon² and directed I_1(s).
The retained comparison is against a frozen independent 512-bit Mellin
reference, not against the same finite eta calculation.

This review reloads the serialized partial sum and tail, rebuilds their
interval, and checks both that interval and the stored interval against
the complete original reference ball. All twelve containments pass at a
fresh 768-bit parsing precision. It also verifies the reference SHA256:

fccc596bdfe19369fc794a42ed49552661062c0334ad8da0310d1fc361c71b76.

The frozen file and its original absolute path are retained under
`sources/foundation/`. The production script checks the same source hash
before each replay. The Laplace asymptotic ratios are point confirmations
of the separately proved theorem and are labelled accordingly.

## Actionable issues and final scope

No numerical formula, branch, direction-of-bound, or evidence-category fix
is required by this review. The master replay should continue to use fresh
Python processes, retain the individual outputs, and record the reviewed
script hashes with the final manifest. All reviewer checks were headless;
the active app and previous research packages were preserved.
