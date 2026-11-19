"""Trace the frozen k=4 comparison. No Riemann ordinate or zero-count input.
Requires python-flint 0.9.0 and the archived Dottie-Off-Axis-Return calculation.
Set --library to the previous archive's extracted directory, if needed.
"""
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json
import sys

from flint import arb, acb, ctx


def trace(library):
    sys.path.insert(0, str(library))
    from arithmetic_braid import ball, complex_record
    from arithmetic_holdout_replay import centered_tube
    from arithmetic_escape_match import fourier_tube
    from signature_fourier_escape import input_geometry, uniform_constants

    ctx.prec = 256
    ctx.cap = 3
    b0 = Fraction(1,6)
    b1 = Fraction(1,4)
    logs = [arb(n).log() for n in range(1,65)]
    anchor = acb(0,8*arb.pi()/arb(3).log())
    node = anchor.mid()
    radius = arb('1e-14')
    assert abs(node-anchor) < radius
    def endpoint(z):
        return complex_record(z+acb(arb(0,radius),arb(0,radius)))
    segments = 0
    b = b0
    max_q = arb(0)
    samples = [{'b':str(b0), 'zero':complex_record(anchor)}]
    out = {'seed':'8*pi*i/log(3)', 'start_b':'1/6','end_b':'1/4','precision_bits':ctx.prec,
           'small_disk_radius':'1e-14','accepted_segment_budget':50000,
           'seed_exact_reason':'(3^w-1)=0 at b=1/6', 'checkpoints':samples,
           'protocol_sha256':hashlib.sha256(Path(__file__).with_name('protocol.txt').read_bytes()).hexdigest()}
    def finish(status):
        return {**out,'status':status,'accepted_segments':segments,'largest_contraction':max_q.str(20),
                'last_b':str(b),'terminal_box':endpoint(node)}
    for cell in range(256):
        left = b0 + (b1-b0)*cell/256
        right = b0 + (b1-b0)*(cell+1)/256
        queue = [(left,right,0)]
        while queue:
            a,b,depth = queue.pop()
            result = (fourier_tube(node,radius,a,b,logs) if node.real < -2
                      else centered_tube(node,radius,a,b))
            if result is None:
                assert depth < 24
                mid = (a+b)/2
                queue.extend(((mid,b,depth+1),(a,mid,depth+1)))
                continue
            node,q,_,_ = result
            max_q = max(max_q,q.upper())
            segments += 1
            if segments >= 50000 and b!=b1:
                return finish('budget-exhausted')
        samples.append({'b':str(right),'zero':endpoint(node)})
        if (cell+1)%32 == 0:
            print(cell+1,segments,endpoint(node),flush=True)
        if right < b1 and node.real < -2:
            cosine = (2*ball(right)).cos_pi()
            if cosine>0 and cosine<=arb('0.05'):
                k = round(float(node.imag)*float(arb(2).log())/(2*float(arb.pi())))
                center,_ = input_geometry(cosine,k)
                if k != 0 and abs(node-center)+radius < 8*cosine:
                    out['escape']={'k':k,'rouche_constants':uniform_constants(),
                                   'entry_distance_upper':(abs(node-center)+radius).str(18),
                                   'entry_radius_lower':(8*cosine).str(18)}
                    return finish('escape-certified')
    assert b==b1
    return finish('finite-endpoint-frozen')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).resolve().parent
    parser.add_argument('--library',type=Path,default=here.parent/'Dottie-Off-Axis-Return')
    parser.add_argument('--output',type=Path,default=here/'triadic_endpoint.json')
    args=parser.parse_args()
    record=trace(args.library.resolve())
    args.output.write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
    print(record['status'],record['last_b'],record['terminal_box'],flush=True)
