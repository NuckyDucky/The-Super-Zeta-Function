"""Rigorous finite-leg continuation of the prospective k=3 zero into its Fourier tail.

The terminal point is b=31/128. The continuation from b=1/6 first uses
the Hurwitz formula. Once Re(w)<-1 the absolutely convergent cosine series
gives tighter uniform derivative enclosures for the same zeros.
"""
from fractions import Fraction
import argparse
import json
from pathlib import Path

from flint import acb,arb,ctx
import arithmetic_braid as braid
from arithmetic_holdout_replay import centered_tube


def fourier_value(w,b):
    normalization = arb.pi()*(-((w+1)*arb(2).log())).exp()/((1-w).gamma()*(w*arb.pi()/2).sin())
    return braid.reference(w,b)*normalization


def fourier_dw(w,b,logs):
    # The tail of x^(u-1) log(x) is positive decreasing on [N,infinity).
    u=w.real.upper()
    assert u < -1
    cutoff=len(logs)
    N=arb(cutoff)
    tail=N**u*(N.log()/(-u)+1/u**2)
    partial=acb(0)
    for n,logn in enumerate(logs,1):
        partial += ((w-1)*logn).exp()*logn*(2*n*b).cos_pi()
    return partial+acb(arb(0,tail),arb(0,tail))


def fourier_db(w,b,logs):
    u=w.real.upper()
    assert u < -1
    cutoff=len(logs)
    N=arb(cutoff)
    tail=N**(u+1)/(-u-1)
    partial=acb(0)
    for n,logn in enumerate(logs,1):
        partial -= (w*logn).exp()*(2*n*b).sin_pi()
    return 2*arb.pi()*(partial+acb(arb(0,tail),arb(0,tail)))


def fourier_tube(node,node_radius,left,right,logs):
    mid=braid.ball((left+right)/2)
    center=braid.shrink_root(node,mid,3)
    D=fourier_dw(center,mid,logs).mid()
    hull=braid.ball(left).union(braid.ball(right))
    half=braid.ball((right-left)/2)
    residual=abs(fourier_value(center,mid))+half*abs(fourier_db(center,hull,logs))
    rad=max(arb('1e-17'),(3*residual/abs(D)).upper(),(2*abs(center-node)).upper())
    if center.real+rad>=-1 or rad > arb('0.1'):
        return None
    square=center+acb(arb(0,rad),arb(0,rad))
    k=abs(1-fourier_dw(square,hull,logs)/D)
    if not (k<1 and residual/abs(D)+k*rad<rad):
        return None
    assert abs(center-node)+node_radius<rad
    end=braid.shrink_root(center,braid.ball(right),4)
    assert abs(center-end)+node_radius<rad
    assert abs(fourier_value(end,braid.ball(right))/D)+k*node_radius<node_radius
    return end,k,rad,center


def run():
    ctx.prec=224
    ctx.cap=3
    logs=[arb(n).log() for n in range(1,65)]
    anchor=acb(0,6*arb.pi()/arb(3).log())
    node=anchor.mid()
    small=arb('1e-14')
    assert abs(anchor-node)<small
    total=0
    counts=[0,0]
    max_k=arb(0)
    samples=[{'shift':'1/6','zero':braid.complex_record(anchor)}]
    for cell in range(232):
        left=Fraction(1,6)+Fraction(cell,3072)
        right=left+Fraction(1,3072)
        queue=[(left,right,0)]
        stage=int(cell>=160)
        while queue:
            a,b,depth=queue.pop()
            result=fourier_tube(node,small,a,b,logs) if stage else centered_tube(node,small,a,b)
            if result is None:
                assert depth<18
                middle=(a+b)/2
                queue.extend(((middle,b,depth+1),(a,middle,depth+1)))
                continue
            node,k,r,c=result
            counts[stage]+=1
            total+=1
            max_k=max(max_k,k.upper())
        box=node+acb(arb(0,small),arb(0,small))
        samples.append({'shift':str(right),'zero':braid.complex_record(box)})
        if (cell+1)%16==0: print(cell+1,counts,flush=True)
    assert right==Fraction(31,128)
    b=braid.ball(right)
    cosine=(2*b).cos_pi()
    d=1-2*cosine**2
    center=acb(1+(cosine/d).log()/arb(2).log(),4*arb.pi()/arb(2).log())
    radius=8*cosine
    dist=abs(node-center)+small
    assert dist<radius
    return {'precision_bits':ctx.prec,'paths':[{'initial_root_expression':'6*pi*i/log(3)',
        'terminal_shift':str(right),'terminal_angle':str((Fraction(1,2)-right)*180),
        'terminal_root_box':braid.complex_record(box),'analytic_tube_center':braid.complex_record(center),
        'distance_to_analytic_center_upper':dist.str(20),'analytic_tube_radius':radius.str(20),
        'certified_segments':total,'number_Hurwitz':counts[0],'number_Fourier':counts[1],
        'maximum_contraction':max_k.str(20),'checkpoints':samples}]}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    args.output.write_text(json.dumps(run(),indent=2)+'\n',encoding='utf8')
