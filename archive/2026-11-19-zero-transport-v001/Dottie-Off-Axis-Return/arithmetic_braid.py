"""Certified continuation between the +60 and +45 degree reciprocal references.

For each rational segment in the Hurwitz shift b, the Newton map with fixed
preconditioner D contracts a common complex disk for all b in the segment.
The certified endpoint disks glue consecutive segments. A closed-form
prefactor zero in the final disk identifies its endpoint exactly.

Usage: python arithmetic_braid.py [--output arithmetic_braid.json]
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from flint import acb, arb, ctx
from arithmetic_reference import reference, derivative_w, derivative_angle, complex_record


def ball(x):
    return arb(x.numerator)/x.denominator


def shrink_root(w,b,steps):
    for _ in range(steps):
        w=(w-reference(w,b)/derivative_w(w,b)).mid()
    return w


def tube(node, node_radius, left, right):
    mid = ball((left+right)/2)
    midpoint = shrink_root(node, mid, 2)
    D = derivative_w(midpoint,mid).mid()
    both = ball(left).union(ball(right))
    half_width=abs(ball((right-left)/2))
    residual=abs(reference(midpoint,mid))+arb.pi()*half_width*abs(derivative_angle(midpoint,both))
    radius=max(arb('1e-20'),(3*residual/abs(D)).upper(),(2*abs(midpoint-node)).upper())
    if radius>arb('0.006'):
        return None
    delta=acb(arb(0,radius),arb(0,radius))
    q=abs(1-derivative_w(midpoint+delta,both)/D)
    if not (q<1 and q*radius+residual/abs(D)<radius):
        return None
    assert abs(midpoint-node)+node_radius<radius
    end = shrink_root(midpoint,ball(right),3)
    # Restrict the same contraction to a small disk centered on end.
    assert abs(midpoint-end)+node_radius<radius
    end_residual = abs(reference(end,ball(right))/D)
    assert end_residual+q*node_radius<node_radius
    return end, q, radius, midpoint


def track(seed, budget_file=None):
    q_start, q_end = 6, 4
    b0=Fraction(1,q_start)
    b1=Fraction(1,q_end)
    if seed == 'riemann':
        anchor = acb.zeta_zero(1)
        anchor_label = 'first nontrivial Riemann zero'
    else:
        multiple = 6 if seed == 'holdout' else 4
        anchor = acb(0,multiple*arb.pi()/arb(3).log())
        anchor_label = f'{multiple}*pi*i/log(3)'
        assert not anchor.zeta().contains(0)
    node=anchor.mid()
    node_radius=arb('1e-14')
    assert abs(anchor-node)<node_radius
    nbase=256
    accepted=0
    rejected=0
    max_depth=0
    max_q=arb(0)
    max_radius=arb(0)
    checkpoints=[{'shift':str(b0),'zero':complex_record(anchor)}]
    for cell in range(nbase):
        initial_left=b0+(b1-b0)*Fraction(cell,nbase)
        initial_right=b0+(b1-b0)*Fraction(cell+1,nbase)
        todo=[(initial_left, initial_right,0)]
        while todo:
            left,right,depth=todo.pop()
            checked=tube(node,node_radius,left,right)
            if checked is None:
                assert depth < 18,(left,right,node)
                mid=(left+right)/2
                todo.extend(((mid,right,depth+1),(left,mid,depth+1)))
                rejected+=1
                continue
            node,q,radius,center=checked
            max_q=max(max_q,q.upper())
            max_radius=max(max_radius,radius)
            accepted+=1
            if seed == 'holdout' and accepted == 30000:
                last_disk=node+acb(arb(0,node_radius),arb(0,node_radius))
                if budget_file:
                    outcome={'precision_bits':ctx.prec,'status':'segment budget exhausted',
                        'accepted_segments':accepted,'parameter_b':str(right),
                        'theta_degrees':str((Fraction(1,2)-right)*180),
                        'last_certified_disk':complex_record(last_disk),'checkpoints':checkpoints}
                    budget_file.write_text(json.dumps(outcome,indent=2)+'\n',encoding='utf8')
                raise ArithmeticError('Holdout segment budget exceeded')
            max_depth=max(max_depth,depth)
        sample=node+acb(arb(0,node_radius),arb(0,node_radius))
        checkpoints.append({'shift':str(initial_right),'zero':complex_record(sample)})
        if (cell+1)%32==0:
            print('verified',seed,cell+1,'/',nbase,'segments',accepted,flush=True)
    # Neither endpoint candidate participates in the continuation.
    if seed=='riemann':
        endpoint=acb(0,4*arb.pi()/arb(2).log())
        endpoint_label='4*pi*i/log(2)'
        assert not endpoint.zeta().contains(0)
    elif seed == 'lattice':
        endpoint=acb.zeta_zero(1)
        endpoint_label='first nontrivial Riemann zero'
    else:
        # Inspect the q=4 prefactor only AFTER a terminal root is enclosed.
        prefactor=acb(4)**sample-acb(2)**sample
        if prefactor.contains(0):
            lattice_index=int(float(sample.imag)*float(arb(2).log())/(2*float(arb.pi()))+0.5)
            endpoint=acb(0,2*lattice_index*arb.pi()/arb(2).log())
            endpoint_label=f'{2*lattice_index}*pi*i/log(2)'
        else:
            # Factorization already identifies the terminal root as a zero of
            # Riemann zeta. Match its ordinal via independent FLINT enclosures.
            for index in range(1,101):
                endpoint=acb.zeta_zero(index)
                if abs(endpoint-node)<node_radius:
                    break
                assert not (endpoint.imag > sample.imag+1), (sample,endpoint)
            else:
                raise ArithmeticError('Riemann zero lookup exhausted')
            endpoint_label=f'nontrivial Riemann zero #{index}'
    assert abs(endpoint-node)<node_radius
    return {'initial_anchor_q':q_start, 'terminal_anchor_q':q_end,
            'initial_root_expression':anchor_label,'initial_root':complex_record(anchor),
            'terminal_root_expression':endpoint_label,'terminal_root':complex_record(endpoint),
            'independently_predicted_terminal_box':complex_record(sample),
            'abs_riemann_zeta_at_terminal_root':abs(endpoint.zeta()).str(35),
            'base_cells':nbase, 'certified_segments':accepted,'rejected_segments_bisected':rejected,
            'maximum_subdivision_depth':max_depth,'largest_contraction_bound':max_q.str(12),
            'largest_uniform_radius':max_radius.str(12),'overlap_disk_radius':node_radius.str(12),
            'checkpoints':checkpoints}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    p.add_argument('--seed',choices=['riemann','lattice','holdout','both'],default='both')
    args=p.parse_args()
    ctx.prec=224
    ctx.cap=3
    seeds=('riemann','lattice') if args.seed=='both' else (args.seed,)
    paths=[track(seed,args.output) for seed in seeds]
    data=json.dumps({'precision_bits':ctx.prec,'paths':paths},indent=2)
    if args.output:
        args.output.write_text(data+'\n',encoding='utf-8')
    if not args.output:
        print(data)
