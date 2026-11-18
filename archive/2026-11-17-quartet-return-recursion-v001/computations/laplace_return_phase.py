"""Numerically test the scaling limit of the coupling increments at T=2*sqrt(j).

This is a high-precision quadrature comparison. The asymptotic proof is in
quartet-return-phase.tex. Two precisions and cutoffs check numerical stability.
"""
import mpmath as mp


def normalized(order, slope, digits, cutoff):
    with mp.workdps(digits):
        root = mp.findroot(lambda x:x*mp.tanh(x)-1,mp.mpf("1.2"))
        rate = 1-1/root**2
        k = mp.sqrt(order)
        def integrand(z):
            y = z/k
            x = root*mp.exp(y)
            h = (x/mp.cosh(x))**2
            return mp.exp(order*mp.log(h/((1+h)*rate))-y/2-1j*slope*z)
        segments = [-cutoff,-8,-4,-2,0,2,4,8,cutoff]
        return + (mp.quad(integrand,segments)/mp.sqrt(mp.pi))


if __name__ == "__main__":
    mp.mp.dps = 65
    a = mp.findroot(lambda x:x*mp.tanh(x)-1,mp.mpf("1.2"))
    print("Laplace coordinate",mp.nstr(a,25),"rate",mp.nstr(1-a**-2,25))
    for j in (64,256,1024,4096):
        coarse = normalized(j,2,42,12)
        fine = normalized(j,2,65,15)
        assert abs(coarse-fine)<mp.mpf("1e-22")
        print(j,"real",mp.nstr(fine.real,14),"imag",mp.nstr(fine.imag,14),
              "distance to exp(-1)",mp.nstr(abs(fine-mp.exp(-1)),8),flush=True)
