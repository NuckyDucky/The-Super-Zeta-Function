"""Retrospective predecessor search for the two skipped zeros, with a forward replay."""
from fractions import Fraction
from hashlib import sha256
import json
import sys
from flint import acb,arb,ctx
from reverse import HERE, follow_from_box, lattice_matches, disk_check, complex_record, dump, ball


def hardy(t):
    phase=acb(arb(1)/4,t/2).lgamma().imag-t*arb.pi().log()/2
    value=acb(0,phase).exp()*acb(arb(1)/2,t).zeta()
    assert value.imag.contains(0)
    return value.real


def bracket(ordinal):
    other=HERE.parent/'Dottie-Forward-Iteration'
    low4=Fraction(json.loads((other/'identification_1.json').read_bytes())['upper_height'])
    high7=Fraction(json.loads((other/'identification_3.json').read_bytes())['lower_height'])
    middle=8*arb.pi()/arb(2).log()
    # An exact rational near the intermediate address, chosen independently of the skipped zeros.
    middle_q=Fraction(int((middle*10**6).floor().unique_fmpz()),10**6)
    lo,hi=(low4,middle_q) if ordinal==5 else (middle_q,high7)
    def counts(a,b):
        return [int(ball(q).zeta_nzeros().unique_fmpz()) for q in (a,b)]
    wide=[str(lo),str(hi)]
    assert counts(lo,hi)==[ordinal-1,ordinal]
    slo,shi=hardy(ball(lo)),hardy(ball(hi))
    assert slo*shi<0
    for _ in range(112):
        m=(lo+hi)/2
        s=hardy(ball(m))
        assert not s.contains(0)
        if slo*s>0:
            lo,slo=m,s
        else:
            hi,shi=m,s
    assert slo*shi<0
    # At extreme proximity FLINT may be unable to compute an unambiguous
    # cumulative count. The original bracket and sign-preserving bisection
    # already prove uniqueness of the root inside the narrow interval.
    box=acb(arb(1)/2,ball(lo).union(ball(hi)))
    return box,dict(ordinal=ordinal,wide_rational_bracket=wide,
                    cumulative_counts=[ordinal-1,ordinal],hardy_bisections=112,
                    narrow_rational_bracket=[str(lo),str(hi)],
                    narrow_signs=[slo.str(20),shi.str(20)],box=complex_record(box))


def run(ordinal):
    assert ordinal in (5,6)
    prefix=f'rho{ordinal}-'
    target,report=bracket(ordinal)
    boxfile=dump(HERE/(prefix+'input.json'),report)
    sealed=follow_from_box(target,boxfile.name,sha256(boxfile.read_bytes()).hexdigest(),
                           HERE/(prefix+'reverse.json'))
    matches=lattice_matches(sealed)
    digest=sha256(sealed.read_bytes()).hexdigest()
    data=json.loads(sealed.read_bytes())
    raw=data['terminal']
    back=acb(arb(raw['real']),arb(raw['imag']))
    if matches:
        assert len(matches)==1
        identity=matches[0]
        start=acb(0,2*identity['index']*arb.pi()/arb(identity['base']).log())
    else:
        sys.path.insert(0,str(HERE.parent/'Dottie-Second-Zero'))
        from classify import classify
        assert not ((acb(2)**back-1)*(acb(3)**back-1)).contains(0)
        identity=classify(raw['real'],raw['imag'])
        assert identity['type']=='Riemann zero'
        start=back
    ident=dump(HERE/(prefix+'identification.json'),dict(reverse_sha256=digest,**identity))
    print(ordinal,'source',identity,'tubes',data['accepted_tubes'],flush=True)
    forward=follow_from_box(start,ident.name,sha256(ident.read_bytes()).hexdigest(),
                            HERE/(prefix+'replay.json'),forward=True)
    point=json.loads(forward.read_bytes())['terminal']
    z=acb(arb(point['real']),arb(point['imag']))
    c=z.mid()
    radius=arb('1e-10')
    assert abs(target-c)<radius and abs(z-c)<radius and disk_check(c,radius,arb(1)/4)[2]
    dump(HERE/(prefix+'roundtrip.json'),dict(ordinal=ordinal,
         input_sha256=sha256(boxfile.read_bytes()).hexdigest(),return_sha256=sha256(forward.read_bytes()).hexdigest(),
         end_box=point,common_isolation_radius='1e-10',accepted_forward_tubes=json.loads(forward.read_bytes())['accepted_tubes']))


if __name__=='__main__':
    ctx.prec,ctx.cap=288,3
    run(int(sys.argv[1]))
