"""Numerical, zeta-free partial Mellin sums. Compare two independent meshes.

Run with python-flint. Riemann ordinates are seeds for this tracking experiment.
Neither Newton steps nor the check on the denser mesh uses Riemann zeta.
Quadrature convergence is tested numerically. --certify also counts finite roots
around selected mesh estimates independently, using rigorous interval integration.
"""
from flint import acb, arb, ctx
import sys


def mesh(density, bits):
    ctx.prec = bits
    left, right = -105, 5
    step = arb(1) / density
    entries = []
    for k in range(left * density, right * density + 1):
        y = k * step
        x = y.exp()
        h = (x / x.cosh()) ** 2
        r = h / (1 + h)
        wt = (step if k in (left * density, right * density) else 2 * step)
        entries.append((y, wt * h, r))
    return entries, step, left


def track(points, step, left, seed, orders):
    w = acb(arb('0.5'), arb(seed))
    previous_move = None
    for order in orders:
        weights = [(y, wt * (1-r**order)) for y, wt, r in points]
        prev = w
        for _ in range(7):
            osc = (-w * left).exp()
            advance = (-w * step).exp()
            total, deriv = acb(0), acb(0)
            for y, wt in weights:
                term = wt * osc
                total += term
                deriv -= y * term
                # Midpoint quadrature, to prevent interval wrapping on repeated rotations.
                osc = (osc * advance).mid()
            update = (total / deriv).mid()
            w = (w - update).mid()
            if abs(update) < arb('1e-29'):
                break
        print(order, w.real.mid().str(36), w.imag.mid().str(36), 'move',
              abs(w-prev).mid().str(9), 'Newton-correction', abs(update).mid().str(6), flush=True)
        if previous_move is not None:
            z = (w-prev)/previous_move
            print('consecutive-move ratio',order,z.real.mid().str(14),z.imag.mid().str(14),flush=True)
        previous_move = w-prev
        if '--certify' in sys.argv and order in (40, 41, 42, 43, 60, 61, 62, 63) and ctx.prec == 288:
            certify(w, order)


def certify(w, order):
    # Rouché against S_K'(w) z on a circle centered at w, using whole-line integral bounds.
    rad = arb('1e-34') if w.imag > 45 else arb('1e-25')
    assert w.real - rad > arb('.49') and w.real + rad < arb('.51')
    b = arb('1.49')
    X = arb(5).exp()
    tails = (2*(-105*b).exp()/b + (4*X+2)*(-2*X).exp(),
             2*(-105*b).exp()*(105/b+1/b**2) + (4*X**2+4*X+2)*(-2*X).exp())
    cuts = [-105,-60,-35,-20,-10,-5,-2,0,1,2,3,4,5]
    values = []
    for j in (0,1):
        def fn(y, analytic):
            x = y.exp()
            h = (x/x.cosh())**2
            return 2*(-w*y).exp()*h*(1-(h/(1+h))**order)*(-y)**j
        val = sum(acb.integral(fn, a, b_, abs_tol=arb('1e-65')) for a,b_ in zip(cuts,cuts[1:]))
        err = arb(0, tails[j])
        values.append(val + acb(err,err))
    # h<=min(exp(2y),1) and 0<=1-r^K<=1 give |S_K''|<=4/1.49^3+4/.49^3<40.
    ratio = (abs(values[0])+20*rad**2)/(abs(values[1])*rad)
    assert ratio < 1, (values, ratio)
    print('CERTIFIED one simple finite-layer zero, radius', rad, 'Rouche ratio upper', ratio.upper().str(8), flush=True)


if __name__ == '__main__':
    for density, bits in [(64, 224), (96, 288)]:
        entries, step, left = mesh(density, bits)
        print('nodes per log unit:', density, 'precision bits:', bits, flush=True)
        track(entries, step, left, '32.935061587739189691', (40, 41, 42, 43))
        track(entries, step, left, '32.935061587739189691', (60,))
        track(entries, step, left, '48.005150881167', (60, 61, 62, 63))
    if '--ratios' in sys.argv:
        for density, bits in [(80, 352), (112, 416)]:
            entries, step, left = mesh(density, bits)
            print('deep ratios density',density,'bits',bits,flush=True)
            for k in (70, 100, 150):
                track(entries, step, left, '32.935061587739189691', (k, k+1, k+2))
