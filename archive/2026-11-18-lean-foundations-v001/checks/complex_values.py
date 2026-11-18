"""Vertical growth of the original quartet superzeta, epsilon=1.

Use the right-half-plane representatives from cosine-spectrum.md, eq. (5).
Write u_n=x_n+i b_n, lambda_n=u_n^2. For n>=2, |u_n|>3*pi/2 and
sinh(b_n)<=|u_n|. Since asinh(r)/r decreases, arg(u_n)<=a, where
a=asin(asinh(3*pi/2)/(3*pi/2)). The root check below shows a<arg(u_1).

In the convergent root sum subtract (pi*n)^(-2s) from each of u_n^(-2s)
and conj(u_n)^(-2s), adding back 2*pi^(-2s)*zeta(2s). The determinant
classification gives Re(u_n)>(n-1/2)*pi and |u_n-pi*n|=O(log(n+1)).
On the straight segment from pi*n to either root, the principal logarithm
is analytic and the absolute value of its argument is <=a for n>=2.
For fixed sigma=Re(s)>0 the integral of the derivative of z^(-2s) along
that segment bounds each subtracted term by
  O_sigma((1+|t|)*exp(2*a*|t|)*log(n+1)*n^(-2*sigma-1)).
The series therefore continues locally normally to Re(s)>0. The added
reference has the expected pole at 1/2. At fixed sigma>0 and |t|>=1,
zeta(2s)=O_sigma(1+|t|) by the one-term Euler summation formula.
The Dottie term has constant modulus; the first conjugate mode decays
at positive heights. These estimates give, as t->+infinity,
  Z(s)=u_1^(-2s)+O_sigma((1+t)*exp(2*a*t)).
Subtracting F(s)=2*pi^(-2s)*(2^(2s)-1)*zeta(2s) gives the same estimate
for J. For t->-infinity take complex conjugates. In particular
|F(s)/Z(s)|=O_sigma((1+t)*exp(-2*t*arg(u_1))) at positive heights.

Run with python-flint 0.9.0. The example values use an independent
logarithmic-derivative Mellin integral (cosine-spectrum.md, eqs. 21-22)
with interval quadrature and explicit absolute errors on both tails.
"""
from flint import acb, arb, ctx


def check_first_root():
    center = acb(arb("2.486885698908560230696957034350657979422828553"),
                 arb("1.809361341295703319016276100194011325600076225"))
    radius = arb("1e-44")
    error = abs(center + center.cos()) + (center.imag + radius).cosh()*radius**2/2
    assert error < abs(1-center.sin())*radius
    box = center + acb(arb(0,radius), arb(0,radius))
    cutoff = 3*arb.pi()/2
    other_angles = (cutoff.asinh()/cutoff).asin()
    assert box.arg() > other_angles
    print("Dominant angular exponent", (2*box.arg()).str(10),
          "upper bound for remaining angular exponents", (2*other_angles).str(10))
    return box


def values(s, first_zero=False):
    def integrand(u, analytic):
        x = u.exp()
        sech2 = 1/x.cosh()**2
        return ((2-2*s)*u).exp()*sech2*(1-x*x.tanh())/(1+x*x*sech2)

    left, right = -160, 6
    cuts = [left,-70,-35,-15,-5,0,1,2,3,4,5,right]
    q = sum(acb.integral(integrand, a, b, abs_tol=arb("1e-57"))
            for a,b in zip(cuts,cuts[1:]))
    beta, X = s.real, arb(right).exp()
    assert beta>=0 and beta<1
    tail = ((2-2*beta)*left).exp()/(2-2*beta) + (2*X**2+2*X+1)*(-2*X).exp()
    j = 2*(arb.pi()*s).sin()/arb.pi() * (q+acb(arb(0,tail),arb(0,tail)))
    f = 2*arb.pi()**(-2*s)*(arb(2)**(2*s)-1)*(2*s).zeta()
    if first_zero:
        assert f.contains(0)
        f = acb(0)  # s was defined as half of the enclosed true zero
    return j+f, j, f


if __name__=="__main__":
    ctx.prec=288
    root = check_first_root()
    for label,s in [("quarter + i",acb(arb(1)/4,1)),
                    ("first half-zero",acb.zeta_zero(1)/2),
                    ("quarter + 20i",acb(arb(1)/4,20)),
                    ("quarter + 40i",acb(arb(1)/4,40))]:
        z,j,f = values(s, first_zero=label=="first half-zero")
        assert z.is_finite() and abs(z)>0
        print(label, "Z=",z.str(18),"J=",j.str(18),"F=",f.str(18),
              "|F/Z|=",abs(f/z).str(8),
              "first mode relative error=",abs(z*root**(2*s)-1).str(5))
