"""Replay one clockwise sweep starting only from the previous sealed enclosure."""
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import sys
from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent/'Dottie-Off-Axis-Return'))
from arithmetic_braid import ball, complex_record, shrink_root
from arithmetic_reference import disk_check
from arithmetic_holdout_replay import centered_tube
from arithmetic_escape_match import fourier_tube


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(sweep, destination):
    assert 1 <= sweep <= 6
    previous = (HERE.parent/'Dottie-Second-Zero'/'dyadic_continuation.json'
                if sweep == 1 else HERE/f'sweep_{sweep-1}.json')
    source = json.loads(previous.read_bytes())
    assert source['terminal_shift'] == '1/4'
    bounds = source['terminal']
    anchor = acb(arb(bounds['real']), arb(bounds['imag']))
    ctx.cap = 3
    start, finish = Fraction(1,6), Fraction(1,4)
    node = shrink_root(anchor.mid(), ball(start), 4)
    radius = arb('1e-17')
    common = arb('1e-9')
    assert abs(anchor-node) < common
    assert disk_check(node,common,ball(start))[2]
    assert disk_check(node,radius,ball(start))[2]
    record = dict(sweep=sweep, precision_bits=ctx.prec, node_radius=str(radius),
                  seed_source=previous.name,seed_sha256=digest(previous),
                  protocol_sha256=digest(HERE/'protocol.txt'),start_box=bounds,
                  reset_isolation_radius='1e-9', checkpoints=[])
    def box():
        return complex_record(node+acb(arb(0,radius),arb(0,radius)))
    def checkpoint(b):
        record['checkpoints'].append(dict(shift=str(b),zero=box()))
    accepted, rejected = 0, 0
    worst = arb(0)
    logs = [arb(n).log() for n in range(1,65)]
    def seal(status,b):
        record.update(status=status,accepted=accepted,rejected=rejected,
                      maximum_contraction=worst.str(18), terminal_shift=str(b),terminal=box())
        destination.write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
        print(status,b,accepted,record['terminal'],flush=True)
    checkpoint(start)
    last = start
    for cell in range(256):
        left = start+(finish-start)*Fraction(cell,256)
        right = start+(finish-start)*Fraction(cell+1,256)
        queue = [(left,right,0)]
        while queue:
            a,b,depth=queue.pop()
            assert last == a
            if accepted >= 50000 or depth > 40:
                seal('unresolved',last)
                return
            tube = (fourier_tube(node,radius,a,b,logs) if node.real < -2
                    else centered_tube(node,radius,a,b))
            if tube is None:
                half=(a+b)/2
                queue.extend(((half,b,depth+1),(a,half,depth+1)))
                rejected+=1
                continue
            node,q,_,_=tube
            accepted+=1
            worst=max(worst,q.upper())
            last=b
        checkpoint(right)
        if cell%32==31:
            print('cell',cell+1,'segments',accepted,'w',node.str(10),flush=True)
        if right<finish and node.real < -2 and (2*ball(right)).cos_pi() <= arb('0.05'):
            from tail_certificate import certify_escape_at
            escape = certify_escape_at(right,node,radius)
            if escape is not None:
                record['escape']=escape
                seal('certified escape',right)
                return
    seal('certified finite endpoint',finish)

if __name__ == '__main__':
    ctx.prec = 256
    sweep=int(sys.argv[1])
    run(sweep,Path(sys.argv[2]) if len(sys.argv)>2 else HERE/f'sweep_{sweep}.json')
