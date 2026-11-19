"""Recover the source address of the last sealed forward branch by reverse transport.

Requires Python 3.12 and python-flint 0.9.0. Only the previously classified
seventh zero's terminal box enters the continuation. Identify the backward
endpoint separately after sealing the new record. Run with assertions enabled.
"""
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "Dottie-Off-Axis-Return"))
from arithmetic_braid import ball, complex_record, shrink_root
from arithmetic_reference import disk_check
from arithmetic_holdout_replay import centered_tube


def dump(path, record):
    path = Path(path)
    path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf8")
    return path


def follow():
    previous = HERE.parent / "Dottie-Forward-Iteration" / "identification_3.json"
    data = json.loads(previous.read_bytes())
    assert data["ordinal"] == 7 and data["real_part"] == "1/2 exactly"
    anchor = acb(arb(1)/2, arb(data["received_imaginary_ball"]))
    return follow_from_box(anchor, previous.name, sha256(previous.read_bytes()).hexdigest(),
                           HERE / "reverse-path.json")


def follow_from_box(anchor, start_source, source_hash, destination, forward=False):
    """Trace a known zero along one sweep and return the sealed raw record."""
    start, finish = Fraction(1,4), Fraction(1,6)
    if forward:
        start,finish=finish,start
    node = shrink_root(anchor.mid(), ball(start), 4)
    radius = arb('1e-17')
    common = arb('1e-10')
    assert abs(node-anchor) < common
    assert disk_check(node,common,ball(start))[2] and disk_check(node,radius,ball(start))[2]
    def box():
        return complex_record(node + acb(arb(0,radius),arb(0,radius)))
    checkpoints = [{"shift": str(start), "zero": box()}]
    accepted, rejected = 0, 0
    maximum = arb(0)
    last = start
    cells = 192
    for j in range(cells):
        a,b = (start+(finish-start)*Fraction(i,cells) for i in (j,j+1))
        pending = [(a,b,0)]
        while pending:
            left,right,depth = pending.pop()
            assert left == last and (right-left)*(finish-start)>0 and depth <= 32 and accepted < 50000
            # centered_tube encloses the two inputs by their union and uses
            # abs(right-left) for the residual, so its proof works backwards.
            tube = centered_tube(node,radius,left,right)
            if tube is None:
                m = (left+right)/2
                pending.extend(((m,right,depth+1),(left,m,depth+1)))
                rejected += 1
            else:
                node,q,_,_ = tube
                maximum = max(maximum,q.upper())
                accepted += 1
                last = right
        checkpoints.append({"shift":str(b),"zero":box()})
    assert last == finish
    return dump(destination,{
        "start_source":start_source,"source_sha256":source_hash,
        "precision_bits":ctx.prec,"seed":complex_record(anchor),"terminal":box(),
        "base_cells":cells,"accepted_tubes":accepted,"subdivisions":rejected,
        "maximum_contraction":maximum.str(20),"checkpoints":checkpoints})


def lattice_matches(sealed):
    record = json.loads(sealed.read_bytes())
    point = record['terminal']
    z = acb(arb(point['real']),arb(point['imag']))
    assert record['checkpoints'][-1]['shift'] == '1/6'
    # The exact b=1/6 factorization contains both 2^w-1 and 3^w-1.
    # A common isolation disk identifies any analytic lattice solution in it.
    matches = []
    for base in (2,3):
        k = (z.imag*arb(base).log()/(2*arb.pi()) + arb(1)/2).floor().unique_fmpz()
        if k is None:
            continue
        exact = acb(0, 2*int(k)*arb.pi()/arb(base).log())
        center, radius = z.mid(),arb('1e-9')
        if abs(center-exact)<radius and abs(center-z)<radius:
            q, residual, ok = disk_check(center,radius,arb(1)/6)
            assert ok
            matches.append(dict(base=base,index=int(k),common_radius=str(radius),
                                contraction=q.upper().str(16),residual=residual.upper().str(16)))
    return matches


def identify(sealed):
    matches=lattice_matches(sealed)
    assert len(matches)==1
    result = dict(sealed_sha256=sha256(sealed.read_bytes()).hexdigest(), **matches[0])
    dump(HERE / "reverse-identification.json",result)
    print(result)


if __name__ == '__main__':
    ctx.prec,ctx.cap=288,3
    identify(follow())
