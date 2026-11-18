"""Directed local prediction of the next unprefactored Mellin partial-sum zero."""
from flint import acb, arb, ctx
from track_native_superzeta_layers import mesh


def estimate(points, step, left, w, order):
    weights = [(y, weight*(1-r**order)) for y, weight, r in points]
    for _ in range(8):
        osc = (-w*left).exp()
        advance = (-w*step).exp()
        total, derivative = acb(0), acb(0)
        for y, weight in weights:
            term = weight*osc
            total += term
            derivative -= y*term
            osc = (osc*advance).mid()
        shift = (total/derivative).mid()
        w = (w-shift).mid()
        if abs(shift) < arb('1e-43'):
            break
    return w


def jets(center, order, count):
    """True integral and derivatives, including bounds on both omitted tails."""
    b = arb('1.49')
    assert center.real > arb('.49') and center.real < arb('.51')
    x = arb(5).exp()
    left = 178
    cut = [-left,-105,-60,-35,-20,-10,-5,-2,0,1,2,3,4,5]
    # For y<0, h<=exp(2y). For y>5, bound (log x)^j by x^j,
    # h<4x^2 exp(-2x), dy=dx/x, and x^(-Re w)<1.
    lower_tail = 2*(-left*b).exp()
    upper_tail = (-2*x).exp()
    tails = [lower_tail/b+(4*x+2)*upper_tail,
             lower_tail*(left/b+1/b**2)+(4*x*x+4*x+2)*upper_tail,
             lower_tail*(left**2/b+2*left/b**2+2/b**3)
             +(4*x**3+6*x**2+6*x+3)*upper_tail]
    terms = []
    for j in range(count):
        def kernel(y, analytic):
            a = y.exp()
            h = (a/a.cosh())**2
            return 2*(-center*y).exp()*h*(1-(h/(1+h))**order)*(-y)**j
        val = sum(acb.integral(kernel,u,v,abs_tol=arb('1e-83'))
                  for u,v in zip(cut,cut[1:]))
        err = arb(0,tails[j])
        terms.append(val+acb(err,err))
    return terms


def disk(w, order):
    f, df = jets(w, order, 2)
    center = (w-f/df).mid()
    f, df = jets(center, order, 2)
    r = arb('1e-43')
    assert center.real-r > arb('.49') and center.real+r < arb('.51')
    # |A''| <= 4/.49^3+4/1.49^3 < 40, by the real integral.
    assert abs(f)+20*r*r < abs(df)*r
    return center,r


def square_error(radius):
    return acb(arb(0,radius),arb(0,radius))


def step_test(seed, order, samples):
    entries, mesh_step, left = samples
    anchor = acb(arb('.5'),arb(seed))
    old = estimate(entries,mesh_step,left,anchor,order)
    c,r = disk(old,order)
    f,df,ddf = jets(c,order+1,3)
    # On this disk |A'''| <= 12/.49^4 + 12/1.49^4 < 215.
    f_at_root = f+square_error(abs(df)*r+20*r*r)
    df_at_root = df+square_error(abs(ddf)*r+108*r*r)
    forecast = -f_at_root/df_at_root
    # The forecast is fixed before solving for the child from its original anchor.
    new = estimate(entries,mesh_step,left,anchor,order+1)
    d,t = disk(new,order+1)
    movement = d-c+square_error(r+t)
    miss = movement-forecast
    degrees = 180/arb.pi()
    print('old',c.str(36),'new',d.str(36),'both disk radius',r.str(6))
    print('orders',order,order+1)
    for label,vec in [('forecast',forecast),('observed',movement),('miss',miss)]:
        print(label, vec.real.str(18), vec.imag.str(18), 'distance',abs(vec).str(15),
              'angle degrees', (vec.arg()*degrees).str(16))
    print('oriented difference degrees',((movement/forecast).arg()*degrees).str(16))
    print('relative miss', (abs(miss)/abs(movement)).str(12), flush=True)


if __name__ == '__main__':
    samples = mesh(112,384)
    for seed, order in [('32.935061587739189691',40),('48.005150881167',60)]:
        step_test(seed,order,samples)
