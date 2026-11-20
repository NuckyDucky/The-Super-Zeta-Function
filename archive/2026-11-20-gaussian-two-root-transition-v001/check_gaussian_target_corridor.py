"""Certified real target corridors for the completed Gaussian factor at T_D.

Requires python-flint and the two adjacent earlier contour certificates.
See gaussian-target-corridor.md for the estimates used between evaluations.
"""
from collections import Counter
from pathlib import Path
import json

from flint import acb, arb, ctx, dirichlet_char

from gaussian_inputs import LIMIT, Q, height, prime_ideals


class EulerProduct:
    def __init__(self, limit):
        _, ideals = prime_ideals(limit)
        mult = Counter(q for q, _ in ideals)
        counts = Counter(ideals)
        self.logs = [arb(q).log() for q in mult]
        self.mult = list(mult.values())
        self.signs = [(counts[q, 1], counts[q, -1]) for q in mult]

    def tail(self, sigma):
        residual = arb(1)
        slope = arb(0)
        for log_q, n in zip(self.logs, self.mult):
            v = (-sigma * log_q).exp()
            residual *= (1-v)**n
            slope += n * log_q * v/(1-v)
        total = acb(sigma).zeta() * acb(sigma).dirichlet_l(dirichlet_char(4, 3))
        assert total.imag.contains(0) and total.real > 0
        err = (residual * total.real).log()
        assert err > 0
        return err.upper(), slope.upper(), total.real.upper()

    def samples(self, start, step, count):
        advances = [(-step * ell).exp() for ell in self.logs]
        for k in range(count):
            if k % 32 == 0:
                w = start+k*step
                values = [(-w * ell).exp() for ell in self.logs]
            den = acb(1)
            for j, (pos, neg) in enumerate(self.signs):
                z = values[j]
                if pos and neg:
                    den *= 1-z*z
                elif pos:
                    den *= (1-z)**pos
                elif neg:
                    den *= (1+z)**neg
                values[j] = z*advances[j]
            assert not den.contains(0)
            yield 1/den


def main():
    ctx.prec = 160
    root = Path(__file__).parent
    product = EulerProduct(LIMIT)
    T, h = height(), arb(1)/16
    r, lam = arb(509)/500, arb(1)/2
    log_b = (arb(Q).sqrt()/(2*arb.pi())).log()
    log_scale = 2*log_b + acb(2,T).lgamma().real
    err, slope, zeta_k = product.tail(r)
    local_gamma = 36/(T-12)
    cells = 800
    step = arb(10)/cells
    near = arb(0)
    for j, value in enumerate(product.samples(acb(r,T-5+step/2), acb(0,step), cells)):
        least_abs = (abs(-5 + (2*j+1)*step/2)-step/2).max(arb(0))
        bound = abs(value)*(err + slope*step/2 + local_gamma - lam*least_abs**2).exp()
        near = near.max(bound.upper())
    medium = zeta_k*(local_gamma - 25*lam).exp()
    far = zeta_k*(-144*lam + 12*arb.pi()).exp()
    envelope = (r*log_b + acb(r,T).lgamma().real - log_scale
                + lam*((r-arb(1)/2)**2+h**2) + arb.pi()*h/2).exp()
    core = (envelope*near.max(medium).max(far)).upper()
    slopesup = (log_b + abs(acb(2,T+1)).log() + arb.pi()/2 + 1 + slope).upper()
    subcells = 128
    width = (arb(9)/8-r)/subcells
    tails = [product.tail(r+j*width)[0] for j in range(subcells)]
    caps = {1:arb(0),-1:arb(0)}
    counts = {}
    for ysign in (-1,1):
        remaining = {1:0,-1:0}
        t = T+ysign*h
        for j, value in enumerate(product.samples(acb(r+width/2,t),acb(width),subcells)):
            w = acb(r+(2*j+1)*width/2,t)
            center = (w*log_b+w.lgamma()-log_scale).exp()*value
            eps = tails[j] + width*slopesup/2
            ang = abs(center.arg())
            for sign, dist in ((1,ang),(-1,arb.pi()-ang)):
                if not dist > eps:
                    remaining[sign] += 1
                    caps[sign] = caps[sign].max((abs(center)*eps.exp()).upper())
        counts["top" if ysign==1 else "bottom"] = remaining
    arcs = json.loads((root/"gaussian-loop-arcs.json").read_text())["edges"]
    regions = json.loads((root/"gaussian-preimage-counts.json").read_text())["regions"]
    outer = arb("6e-16")
    report = []
    for sign in (-1,1):
        anchor = ("-" if sign<0 else "")+"6e-16"
        assert any(k["target_center_re"] == anchor and k["target_center_im"] == "0"
                   and k["preimages_with_multiplicity"] == 2 for k in regions)
        clear = arb(1)
        for edge in arcs.values():
            for disk in edge["segments"]:
                z = acb(disk["x"],disk["y"])
                closest = (sign*z.real).min(outer).max(arb(0))
                clear = clear.min((abs(z-sign*closest)-arb(disk["r"])).lower())
        assert clear > 0
        obstruction = max(core.upper(),caps[sign].upper())
        mantissa = int((obstruction*10**23).ceil().unique_fmpz())
        endpoint = arb(mantissa)/10**23
        assert obstruction < endpoint < outer
        assert mantissa <= 105238
        report.append(dict(sign=sign, small_endpoint_magnitude=f"{mantissa}e-23",
                           large_endpoint_magnitude="6e-16",preimages=2, distinct_simple=True,
                           certified_obstruction_upper=str(obstruction), horizontal_cap=str(caps[sign]),
                           old_arc_segment_clearance_lower=str(clear.lower())))
    result = dict(precision_bits=ctx.prec,prime_norm_cutoff=LIMIT, target_normalization="H(w)/S",
                  real_input_bounds=[-1,2],input_height_offsets=["-1/16","+1/16"],
                  core_real_input_bounds=["-9/500","509/500"],core_radius_upper=str(core),
                  damping_lambda="1/2",maximum_principle_window_radius=12, local_phase_cells=cells,
                  near_prime_envelope=str(near), middle_prime_envelope=str(medium), far_prime_envelope=str(far),
                  grid_euler_log_tail=str(err), finite_product_log_derivative_bound=str(slope),
                  horizontal_subcells_per_extension=subcells,phase_unexcluded_subcells=counts,
                  origin_count=None, corridors=report)
    (root/"gaussian-target-corridor.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
