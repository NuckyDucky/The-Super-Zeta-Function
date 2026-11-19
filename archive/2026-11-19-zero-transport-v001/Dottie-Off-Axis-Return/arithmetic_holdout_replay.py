"""Independent replay of the k=3 path with a centered derivative enclosure.

Run with python-flint 0.9.0. After the deterministic 30,000-segment trial
exhausts its budget, this replay can follow precisely the same seed and path.
The added derivative bound is a mean-value estimate on the identical disk.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from flint import acb, acb_series, arb, ctx
import arithmetic_braid as braid


def centered_tube(node, node_radius, left, right):
    bmid = braid.ball((left+right)/2)
    center = braid.shrink_root(node, bmid, 3)
    deriv = braid.derivative_w(center,bmid)
    D = deriv.mid()
    bspan = braid.ball(left).union(braid.ball(right))
    half = abs(braid.ball((right-left)/2))
    residual = abs(braid.reference(center,bmid)) + arb.pi()*half*abs(braid.derivative_angle(center,bspan))
    radius = max(arb('1e-20'), (3*residual/abs(D)).upper(), (2*abs(center-node)).upper())
    if radius > arb('0.1'):
        return None
    square = center + acb(arb(0,radius),arb(0,radius))
    pi = arb.pi()
    v = acb_series([square,1],3)
    dww = 2*((v.zeta(bspan)+v.zeta(1-bspan))*(-v*pi.log()).exp())[2]
    v = acb_series([center,1],2)
    dwb = (-v*((v+1).zeta(bspan)-(v+1).zeta(1-bspan))*(-v*pi.log()).exp())[1]
    # First vary w keeping b fixed; then vary b with w fixed at center.
    k = abs(1-deriv/D) + (radius*abs(dww)+half*abs(dwb))/abs(D)
    if not (k<1 and k*radius+residual/abs(D)<radius):
        return None
    assert abs(center-node)+node_radius<radius
    end = braid.shrink_root(center,braid.ball(right),4)
    assert abs(center-end)+node_radius<radius
    assert abs(braid.reference(end,braid.ball(right))/D)+k*node_radius<node_radius
    return end,k,radius,center


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    ctx.prec=224
    ctx.cap=3
    braid.tube=centered_tube
    path=braid.track('holdout')
    args.output.write_text(json.dumps({'precision_bits':ctx.prec,
        'method':'separate replay with centered derivative enclosure','paths':[path]},indent=2)+'\n', encoding='utf8')
