"""Identify the rational-shift crossings of the five published 2007 figure branches.

This retrospective comparison uses the published start ordinals as inputs.
Run from any directory with python-flint 0.9.0 and assertions enabled.
"""
import argparse
from fractions import Fraction

from flint import acb, arb, ctx
from reverse import HERE, ball, centered_tube, complex_record, disk_check, dump


def cross(node, start, finish, node_radius):
    pending = [(start, finish, 0)]
    accepted = 0
    largest_q = arb(0)
    while pending:
        left, right, depth = pending.pop()
        assert depth < 23 and accepted < 40000
        answer = centered_tube(node, node_radius, left, right)
        if answer is None:
            mid = (left + right) / 2
            pending.extend(((mid, right, depth+1), (left, mid, depth+1)))
            continue
        node, q, _, _ = answer
        largest_q = max(largest_q,q.upper())
        accepted += 1
    return node, dict(accepted_tubes=accepted, max_contraction=largest_q.str(20))


def match(node, b):
    radius = arb('1e-8')
    assert disk_check(node, radius, ball(b))[2]
    candidates = [(f'rho{j}', acb.zeta_zero(j)) for j in range(1, 8)]
    bases = [2, 3] if b == Fraction(1,6) else [2]
    for p in bases:
        j = (node.imag * arb(p).log() / (2*arb.pi()) + arb(1)/2).floor().unique_fmpz()
        if j is not None and j != 0:
            candidates.append((f'2*pi*i*{j}/log({p})',acb(0,2*arb.pi()*int(j)/arb(p).log())))
    labels = [label for label,z in candidates if abs(z-node)<radius]
    assert len(labels)==1
    return labels[0]


def compare(ordinal):
    start = Fraction(1,2)
    radius = arb('1e-17')
    root = acb.zeta_zero(ordinal)
    node = root.mid()
    assert abs(node-root)<radius and disk_check(node, radius, ball(start))[2]
    data = dict(precision_bits=ctx.prec, historical_figure=['2a','2b','3a','3b','4'][ordinal-1],
                initial_zeta_ordinal=ordinal, shift_convention='b=1-a in the 2007 paper',
                root_radius='1e-17', identification_disk_radius='1e-8', checkpoints=[])
    for b in (Fraction(1,4), Fraction(1,6)):
        node, row = cross(node, start, b, radius)
        row.update(paper_a=str(1-b), b=str(b), label=match(node,b),
                   root=complex_record(node+acb(arb(0,radius),arb(0,radius))))
        data['checkpoints'].append(row)
        start = b
        print(ordinal, row['paper_a'], row['label'], row['accepted_tubes'], flush=True)
    dump(HERE / f'historical-figure-{ordinal}.json', data)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('ordinal',type=int,choices=range(1,6))
    ctx.prec,ctx.cap=192,3
    compare(ap.parse_args().ordinal)
