"""Directed inverse of the 320-fold scalar return on each vertical flank.
PP (first phase) is always the first phase in F_L.  Angles in degrees.
Use: python flank_path.py PATH_TO_REPO [--output FILE]
Python 3.12, python-flint 0.9.0. Numerical proposals have no proof role.
"""
import argparse
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import json, sys
from flint import acb, arb, ctx

Y0 = Fraction("0.509892982511772")
ETA = Fraction("4.749479070945369e-8")
START = Y0 - Fraction("3e-10")
END = {-1: Y0 + Fraction("7.6e-9"), 1: Y0 - Fraction("5.9e-9")}
CHARTS = {}

def real(q):
    q=Fraction(q)
    return arb(q.numerator)/q.denominator

def center(z):
    return acb(z.real.mid(),z.imag.mid())

def box(z,r):
    t=arb(0,r.upper())
    return z+acb(t,t)

def disc(z):
    c=center(z)
    return c,abs(z-c).upper()

def affine(disk,q,b):
    c,r=disc(q*disk[0]+b)
    return c,(r+abs(q)*disk[1]).upper()

@lru_cache(maxsize=1000)
def seed(s,y):
    # A linear approximation to a continued periodic point only seeds Newton.
    d=float(y-Y0)/float(END[s]-Y0)
    p=complex(.018066,-.000718)+d*complex(-.001,-.022) if s<0 else complex(.999592,.009208)+d*complex(.0058,-.0038)
    p=acb(p.real,p.imag)
    L=acb(s*real(ETA),real(y))
    for _ in range(8):
        z=p; m=acb(1)
        for j in range(320):
            for rate in (-L,L):
                z=center((rate*z).exp());m=center(m*(rate*z))
        if not z.is_finite() or not m.is_finite(): raise ArithmeticError("Newton seed")
        corr=(z-p)/(1-m)
        p=center(p+corr)
        if abs(corr)<real('1e-112'): break
    return p

def trap(s,lo,hi):
    p=seed(s,(lo+hi)/2)
    L=acb(s*real(ETA),real(lo).union(real(hi)))
    a,b,_,_=advance(p,arb(0),L,320)
    residual=(abs(a-p)+b).upper()
    r=max(real('1e-100').upper(), 4*residual).upper()
    _,_,k,ex=advance(p,r,L,320,monitor=True)
    if not (k<1 and residual+k*r<r): raise ArithmeticError("trapping")
    gaps=[(abs(u-p)-rr-r).lower() for u,rr in ex.values()]
    if len(gaps)!=2 or min(gaps)<=0: raise ArithmeticError("period")
    return p,r,L,k,min(gaps)

def moment(s,lo,hi,slope=True):
    p,r,L,k,gap=trap(s,lo,hi)
    if s in CHARTS:
        # A numerical solver could otherwise jump to a different periodic
        # point. Verify the small certificate lies in a previously glued cell.
        assert any(a<=lo<=hi<=b and abs(p-m['p'])+r<m['r']
                   for a,b,m in CHARTS[s])
    z=p; rr=r; total=acb(0); stages=[]
    for j in range(320):
        for sign in (-1,1):
            rate=sign*L
            before=box(z,rr)
            total+=rate*before
            z,rr=stage(z,rr,rate)
            if slope: stages.append((sign,before,box(z,rr)))
    mu=(320*(-L*L).log()+total).exp()
    a=degree(mu)
    result=dict(a=a,mu=mu,p=p,r=r,k=k,gap=gap)
    if slope:
        i=acb(0,1); t=disc(acb(0))
        for sign,before,after in stages:
            t=affine(t,sign*L*after,sign*i*before*after)
        t=disc(box(*t)/(1-mu))
        b=640*i/L
        for sign,before,after in stages:
            b+=sign*i*before+sign*L*box(*t)
            t=affine(t,sign*L*after,sign*i*before*after)
        result['slope']=b.imag*180/arb.pi()
    return result

def calibration(s):
    if s<0: lo,hi=START,END[s]
    else: lo,hi=END[s],Y0+Fraction('3e-10')
    pending=[(lo,hi,0)]; cells=[]
    while pending:
        a,b,d=pending.pop()
        try:
            m=moment(s,a,b)
            if not(s*m['slope']>10**9 and s*m['slope']<10**10 and m['a']>-160 and m['a']<140):
                raise ArithmeticError('slope')
        except ArithmeticError:
            assert d<17, (s,a,b,d)
            h=(a+b)/2;pending.extend([(h,b,d+1),(a,h,d+1)])
            continue
        cells.append((a,b,m))
    cells.sort(key=lambda c:c[0])
    assert cells[0][0]==lo and cells[-1][1]==hi
    # A point certificate at every seam belongs to both trapping disks.
    # Uniqueness glues the fixed points across the complete parameter range.
    for (a,b,m),(c,d,n) in zip(cells,cells[1:]):
        assert b==c
        e,r,*_=trap(s,b,b)
        assert abs(e-m['p'])+r<m['r'] and abs(e-n['p'])+r<n['r']
    # Prove the two inclinations genuinely issue from the cap in the certificate.
    p,r,*_=trap(s,Y0,Y0)
    L=acb(s*real(ETA),real(Y0))
    marked,_,_,_=trapping_data(L)
    for a,b,m in cells:
        if a<=Y0<=b:
            assert abs(p-m['p'])+r<m['r']
            assert abs(marked-p)+real('1e-27')<m['r']
    CHARTS[s]=cells
    assert all(s*m['a']>0 for a,b,m in cells)
    return lo,hi,dict(cells=len(cells),slope_abs_lower=min((s*m['slope']).lower() for _,_,m in cells).str(15),
        slope_abs_upper=max((s*m['slope']).upper() for _,_,m in cells).str(15),
        contraction_upper=max(m['k'] for _,_,m in cells).str(12),
        proper_divisor_gap_lower=min(m['gap'] for _,_,m in cells).str(12),
        angle_lower=min(m['a'].lower() for _,_,m in cells).str(12),
        angle_upper=max(m['a'].upper() for _,_,m in cells).str(12),
        start=str(lo),end=str(hi),certified_continuation_of_original_cap_root=True)

def tinybracket(s,target,lo,hi):
    # Safeguarded Newton proposes rational parameter endpoints. Signs at the
    # final endpoints, together with the independently covered monotone interval,
    # certify the complete inverse of this input angle enclosure.
    initial_lo,initial_hi=lo,hi
    assert s*moment(s,lo,lo,False)['a']<s*target<s*moment(s,hi,hi,False)['a']
    q=(lo+hi)/2
    for _ in range(12):
        m=moment(s,q,q)
        dq=(m['a']-target)/m['slope']
        if abs(dq.mid())<real('1e-74'): break
        v=Fraction(str(dq.mid().fmpq()))
        if s*m['a']<s*target:lo=q
        elif s*m['a']>s*target:hi=q
        t=q-v
        q=t if lo<t<hi else (lo+hi)/2
        # Snap a seed to a rational mesh to bound exact-arithmetic growth.
        q=Fraction(round(q*10**82),10**82)
    for power in [62,56,50,44,38,33,29,25,21,18]:
        d=Fraction(1,10**power)
        left,right=q-d,q+d
        if not initial_lo<left<right<initial_hi: continue
        f=moment(s,left,left,False)['a']; g=moment(s,right,right,False)['a']
        if s*f<s*target<s*g: return left,right
    raise ArithmeticError(('inverse bracket',s,target,q))

def stamp(bounds):
    a,b=bounds
    return dict(lower=str(a),upper=str(b),interval=real(a).union(real(b)).str(42),width=str(b-a))

def blind_return(readings):
    # Only the fresh two real spectral measurements are passed. Both charts
    # have already been calibrated; their angle bands are disjoint by sign.
    unit=decode(readings)
    angle=degree(unit)
    if angle<0:
        rail=-1
    elif angle>0:
        rail=1
    else:
        raise ArithmeticError("No unique chart")
    bins=CHARTS[rail]
    back=degree(unit*acb(arb(3).sqrt()/2,arb(1)/2))
    bounds=tinybracket(rail,back,bins[0][0],bins[-1][1])
    return rail,bounds

def packet(m):
    unit=m['mu']/abs(m['mu'])
    packet=encode(unit)
    angle=degree(decode(packet))
    assert angle.overlaps(m['a'])
    return dict(angle=angle.str(38), Mplus=packet[0].str(30), Mminus=packet[1].str(30),
                multiplier=m['mu'].str(36)),angle,packet

def ordered_root(s,lo,hi):
    # g_{-L} composed with E_{-L} equals E_{-L} composed with g_L.
    # The initial lag is certified from the independent cap traps. Keeping
    # that lag then gives the analytic continuation of the full ordered pair.
    m=moment(s,lo,hi,False)
    L=acb(s*real(ETA),real(lo).union(real(hi)))
    lag=0 if s<0 else 319
    z,r,*_=advance(m['p'],m['r'],L,lag)
    q,qr=stage(z,r,-L)
    return L,(m['p'],m['r']),(q,qr)

def history(L,p,q):
    for _ in range(640):
        yield L*box(*q),-L*box(*p)
        p,q=stage(*q,L),stage(*p,-L)

def run(s):
    a,b,cal=calibration(s)
    orig=moment(s,Y0,Y0,False)
    source,ang,origreads=packet(orig)
    r30=acb(arb(3).sqrt()/2,arb(-1)/2)
    target=degree(decode(origreads)*r30)
    a1,b1=tinybracket(s,target,a,b)
    turned,ang1,fresh=packet(moment(s,a1,b1,False))
    ret=degree(decode(fresh)*r30.conjugate())
    a2,b2=tinybracket(s,ret,a,b)
    assert a2<Y0<b2
    # The two candidate charts have disjoint angle projections. The sign of
    # the decoded angle supplies the rail in this two-chart experiment.
    assert s*ang>0 and s*ang1>0 and s*ret>0
    L,p,q=ordered_root(s,Y0,Y0)
    q_cap,*_=trapping_data(-L)
    assert abs(q[0]-q_cap)+q[1]<real('1e-27')
    largest=arb(0)
    count=0
    for primary,returned in zip(history(L,p,q),history(*ordered_root(s,a2,b2)),strict=True):
        for u,v in zip(primary,returned,strict=True):
            assert u.overlaps(v)
            largest=max(largest,abs(u-v).upper())
            count+=1
    assert count==1280
    anchors={}
    for angle in ([-90] if s<0 else [60,54,45]):
        anchors[str(angle)]=stamp(tinybracket(s,arb(angle),a,b))
    return dict(sign=s,y0=str(Y0),x=str(s*ETA),chart=cal,original=source,
        turned=turned,turned_y=stamp((a1,b1)),returned_y=stamp((a2,b2)),markers=anchors,
        rooted_Q_equals_negative_stage_after_P_scalar_iterations=0 if s<0 else 319,
        fresh_return_exponents_compared=count, all_exponent_boxes_overlap=True,
        largest_lift_difference_upper=largest.str(12),
        y0_in_return=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repo', type=Path)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    sys.path.insert(0,str((args.repo/'archive/2026-11-19-oriented-return-v001/computations').resolve()))
    from orbit_crossing import advance,stage
    from quarter_probe import degree,encode,decode
    from verify_dottie_horn_slice import trapping_data
    if not __debug__: raise RuntimeError('Enable assertions.')
    ctx.prec=448
    results={}
    for s,side in [(-1,'left'),(1,'right')]:
        results[side]=run(s)
        print(side,json.dumps(results[side]),file=sys.stderr,flush=True)
    blind=[]
    for name in ('right','left'):
        data=results[name]['turned']
        # Round the emitted pair to the same displayed balls available to an
        # external reader; no hidden native phase, parameter or sign is input.
        measured=(arb(data['Mplus']),arb(data['Mminus']))
        rail,bounds=blind_return(measured)
        assert bounds[0]<Y0<bounds[1] and rail==results[name]['sign']
        blind.append(dict(measured=[data['Mplus'],data['Mminus']],recovered_sign=rail,
                          recovered_y=stamp(bounds)))
    record=json.dumps(dict(precision_bits=448,first_phase='P',round_trip='clockwise then counterclockwise',
        x_path='Fixed at the original signed witness x on both journeys',flanks=results,
        blind_recovery_from_serialized_turned_trace_pairs=blind),indent=2)+'\n'
    if args.output:args.output.write_text(record,encoding='utf-8')
    else:print(record)

