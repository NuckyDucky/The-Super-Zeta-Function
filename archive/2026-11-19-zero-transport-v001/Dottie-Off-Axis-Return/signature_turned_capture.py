"""Enclose the exactly 30-degree-turned flank and test fresh-cap capture.

Requires flank_path.py and the local source checkout of The-Super-Zeta-Function.
Higher precision resolves the direction after a large cap excursion.
"""
import argparse
from fractions import Fraction as Fr
import json
from pathlib import Path
import sys
from flint import acb,arb,ctx
import flank_path as fp

def run(repo):
    sys.path.insert(0, str(repo/'archive/2026-11-19-oriented-return-v001/computations'))
    from orbit_crossing import advance, stage
    from quarter_probe import degree
    from verify_dottie_horn_slice import trapping_data
    fp.stage, fp.advance, fp.degree = stage, advance, degree
    # 2600 bits allow phase recovery when the imaginary exponent is O(10^452).
    ctx.prec=2600
    y0,eta=fp.Y0,fp.ETA
    t=fp.real
    def proposal(s, y):
        # Original glue calculation supplies an approximate periodic point.
        p=fp.seed(s,y)
        L=acb(s*t(eta), t(y))
        for _ in range(7):
            z=p
            m=acb(1)
            for _ in range(320):
                for rate in (-L,L):
                    z=fp.center((rate*z).exp())
                    m=fp.center(m*rate*z)
            corr=(z-p)/(1-m)
            p=fp.center(p+corr)
            if abs(corr)<t('1e-700'): break
        return p
    def trap(s,lo,hi):
        p=proposal(s,(lo+hi)/2)
        L=acb(s*t(eta),t(lo).union(t(hi)))
        g,gr,*_=advance(p,arb(0),L,320)
        res=(abs(g-p)+gr).upper()
        r=max(t('1e-700'),res*4).upper()
        _,_,k,ex=advance(p,r,L,320,monitor=True)
        assert k<1 and res+k*r<r
        return p,r,L,k,min((abs(z-p)-rr-r).lower() for z,rr in ex.values())
    # The independent witness continuation uses a larger interval trap.
    coarse_trap=fp.trap
    fp.trap=trap
    def solve(s, seed, parent):
        initial=trap(s,y0,y0)
        cap_start,_,_,_=trapping_data(initial[2])
        assert abs(initial[0]-cap_start)+initial[1]<t('1e-27')
        target=fp.moment(s,y0,y0,False)['a']-30
        q=seed
        for _ in range(8):
            cand=fp.moment(s,q,q)
            delta=(cand['a']-target)/cand['slope']
            q-=Fr(str(delta.mid().fmpq()))
            q=Fr(round(q*10**680),10**680)
            if abs(delta)<t('1e-635'):break
        width=Fr(1,10**610)
        a,b=q-width,q+width
        assert parent[0]<a<b<parent[1]
        assert s*fp.moment(s,a,a,False)['a']<s*target<s*fp.moment(s,b,b,False)['a']
        refined=trap(s,a,b)
        anchor, bigr,*_=coarse_trap(s,*parent)
        assert abs(anchor-refined[0])+refined[1]<bigr
        return a,b,refined
    input_data=json.loads(Path(__file__).with_name('flank_path.json').read_text())['flanks']
    result={}
    for s, key in [(-1,'left'),(1,'right')]:
        parent=tuple(Fr(input_data[key]['turned_y'][k]) for k in ('lower','upper'))
        a,b,marked=solve(s,sum(parent)/2,parent)
        L=acb(s*t(eta),t(a).union(t(b)))
        # At the right, P is the scalar cycle reached readily; at the
        # left it is Q. Compare its cap images to explicit trapping disks.
        easy=s*L
        easy_start, caprad, *_ = advance(acb(1),arb(0),easy,320*60)
        easy_radius=t('1e-18')
        assert caprad<easy_radius
        g,gr,k,_=advance(easy_start,easy_radius,easy,320,monitor=True)
        assert abs(g-easy_start)+gr<easy_radius and k<1
        if s==1:
            ep, er=marked[:2]
        else:
            ep,er=stage(marked[0],marked[1],-L)
        assert abs(ep-easy_start)+er<easy_radius
        K=-easy
        # Prove that the *whole* radius-2r cap disk returns within r/4
        # after 321 iterates. Cauchy's estimate then gives contraction
        # on the inner r disk. Check both maximal proper divisors of 321.
        rcap=t('1e-610')
        disc=acb(1),(2*rcap).upper()
        exclusions={}
        for j in range(1,320):
            for rate in (-K,K):disc=stage(*disc,rate)
            if j in (3,107):
                gap=(abs(disc[0]-1)-disc[1]-rcap).lower()
                assert gap>0
                exclusions[j]=gap.str(16)
        disc=stage(*disc,-K)
        huge=K*fp.box(*disc)
        assert huge.real>100 and huge.imag.is_finite()
        direction=(-K.real*huge.imag.cos()+K.imag*huge.imag.sin())
        assert direction<t('-0.1') and arb(100).exp()/10>2000 and abs(K)<1
        # e^Re(b)*direction bounds Re(-K z_320), since z_320=exp(b).
        # Consequently |g_K(z_320)-1| <= expm1(|K| e^-2000).
        rebound=(-arb(2000)).exp().expm1().upper()
        assert rebound<rcap/4
        assert rebound/rcap<1
        print(key, 'big real',huge.real.str(12),'direction',direction.str(22),flush=True,file=sys.stderr)
        result[key]=dict(turned_parameter_bounds=[str(a),str(b)],
                         turned_parameter_width=str(b-a),
                         easy_phase=('P' if s==1 else 'Q'),
                         easy_cap_enters_marked_cycle=True,easy_cap_laps=60,easy_contraction_upper=k.str(14),
                         hard_phase=('Q' if s==1 else 'P'),
                         hard_cap_period=321,easy_cap_period=320, fresh_cap_ordered_period=205440,
                         hard_cap_fat_disk='2e-610',hard_cap_inner_trap='1e-610',
                         hard_lap_return_radius_upper=rebound.str(15),
                         hard_lap_inner_derivative_upper=(rebound/rcap).str(15),
                         hard_maximal_proper_divisor_gaps=exclusions,
                         largest_exp_real=huge.real.str(22),
                         next_inner_real_normalized_by_exp_of_big_real=direction.str(22))
    return dict(precision_bits=ctx.prec,flanks=result)

if __name__=='__main__':
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('repo',type=Path)
    cli.add_argument('--out',type=Path)
    args=cli.parse_args()
    data=json.dumps(run(args.repo.resolve()),indent=2)+'\n'
    if args.out:args.out.write_text(data,encoding='utf8')
    else:print(data)
