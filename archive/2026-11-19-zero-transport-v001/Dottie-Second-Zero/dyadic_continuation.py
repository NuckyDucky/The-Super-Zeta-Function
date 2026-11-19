"""Follow the explicit dyadic seed using only the bilateral Hurwitz reference."""
from fractions import Fraction
from pathlib import Path
import argparse
import json
import sys
from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
source = HERE.parent / "Dottie-Off-Axis-Return"
sys.path.insert(0, str(source))
from arithmetic_braid import complex_record, ball
from arithmetic_holdout_replay import centered_tube

def go(output):
    ctx.prec = 224
    ctx.cap = 3
    b0 = Fraction(1, 6)
    b1 = Fraction(1, 4)
    seed = acb(0, 4 * arb.pi() / arb(2).log())
    node = seed.mid()
    small = arb('1e-18')
    assert abs(seed-node) < small
    lim = 50000
    accepted = 0
    rejected = 0
    max_q = arb(0)
    data = {'precision_bits': ctx.prec, 'branch': 'dyadic', 'initial_root_expression':'4*pi*i/log(2)',
            'node_radius': small.str(12),'accepted_limit':lim,
            'checkpoints':[{'shift': str(b0),'zero':complex_record(seed)}]}
    parts = 256
    for j in range(parts):
        right = b0 + (b1-b0)*Fraction(j+1,parts)
        pending=[(b0 + (b1-b0)*Fraction(j,parts),right,0)]
        while pending:
            a,b,depth=pending.pop()
            assert depth <= 40
            check=centered_tube(node,small,a,b)
            if check is None:
                split=(a+b)/2
                pending.extend(((split,b,depth+1),(a,split,depth+1)))
                rejected+=1
                continue
            node,q,_,_=check
            accepted+=1
            max_q=max(max_q,q.upper())
            if accepted==lim and b!=b1:
                data.update(status='budget exhausted',accepted=accepted,
                            terminal_shift=str(b),terminal=complex_record(node+acb(arb(0,small),arb(0,small))))
                output.write_text(json.dumps(data,indent=2)+'\n')
                return
        z=node+acb(arb(0,small),arb(0,small))
        data['checkpoints'].append({'shift':str(right),'zero':complex_record(z)})
        if (j+1)%16==0:
            print(j+1,accepted, node.str(11),flush=True)
    data.update(status='certified through b=1/4',terminal_shift=str(b1),
                accepted=accepted,rejected=rejected,maximum_contraction=max_q.str(18),
                terminal=complex_record(z))
    output.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print('saved terminal',json.dumps(data['terminal']),flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE/'dyadic_continuation.json')
    go(parser.parse_args().output)
