"""Independent essential derivations and serialized-evidence checks.

Does not modify or replay the production numerical scripts.
"""
from pathlib import Path
from fractions import Fraction
from math import comb
import hashlib
import json
import sympy as sy
import mpmath as mp
from flint import arb,ctx

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
ctx.prec=768


def ar(q):
    q=Fraction(q)
    return arb(q.numerator)/q.denominator


def kernel_checks():
    u,e=sy.symbols('u e',nonzero=True)
    original=(sy.tanh(u)-1)/u+(1-u*sy.tanh(u))/(e**2*sy.cosh(u)**2+u**2)
    rational=((1-u)/e**2-(1+sy.exp(-2*u))/(2*u))/(sy.cosh(u)**2+u**2/e**2)
    residual=sy.simplify(sy.together((original-rational).rewrite(sy.exp)))
    assert residual==0
    rows=[]
    old=json.loads((HERE/'superzeta-residue-results.json').read_text())
    with mp.workdps(90):
        for sf,wf,ef in ((Fraction(-1,4),1,1),(Fraction(1,4),4,2),(Fraction(3,4),1,2)):
            s=mp.mpf(sf.numerator)/sf.denominator;w=mp.mpf(wf);eps=mp.mpf(ef)
            def h(u):
                return (mp.tanh(u)-1)/u+(1-u*mp.tanh(u))/(eps**2*mp.cosh(u)**2+u*u)
            # Independent lower substitution: t=q^4, rather than u=u0+q^4.
            low=lambda q:4*q**int(3-4*sf)*h(mp.sqrt(w+q**4))
            high=lambda u:2*u*(u*u-w)**(-s)*h(u)
            split=mp.sqrt(w+1)
            value=mp.quad(low,[0,1])+mp.quad(high,[split,4,12,40,120])
            reference=next(row for row in old['directed_shifted_Mellin_checks']
                           if row['s']==str(sf) and row['w']==str(wf) and row['epsilon']==str(ef))
            ball=arb(reference['directed_integral'])
            assert abs(ball-arb(mp.nstr(value,85)))<arb('1e-75')
            rows.append({'s':str(sf),'w':wf,'epsilon':ef,
                         'independent_90dps_point':mp.nstr(value,85),
                         'directed_reference':str(ball),'point_consistency_tolerance':'1e-75',
                         'lower_substitution':'original t=q^4',
                         'kernel':'d_v log E_epsilon(-v)-1/sqrt(v)',
                         'scope':'point consistency with independently certified reference'})
    return {'exact_symbolic_kernel_residual':str(residual),'alternative_variable_checks':rows}


def independent_positive_series():
    old=json.loads((HERE/'residue-period-results.json').read_text())
    rows=[]
    for row in old['directed_period_results']:
        z=Fraction(row['exact_parameter']);N=96
        partial=sum(Fraction(comb(2*n,n)**2,16**n)*z**n for n in range(N+1))
        tail=Fraction(comb(2*N+2,N+1)**2,16**(N+1))*z**(N+1)/(1-z)
        bounding_interval=arb(ar(partial)+ar(tail)/2,ar(tail)/2)
        manual=arb(row['directed_AGM_enclosure'])
        assert bounding_interval.contains(manual)
        rows.append({'parameter_label':row['parameter_label'],'exact_parameter':str(z),
                     'independent_exact_series_terms':'0 through96',
                     'manual_AGM_interval_contained_in_exact_series_interval':True,
                     'independent_tail':str(ar(tail))})
    return rows


def laplace_containments():
    data=json.loads((HERE/'laplace-barnes-results.json').read_text())
    provenance=json.loads((ROOT/'sources/foundation/cosine-reference-provenance.json').read_text())
    raw=(ROOT/'sources/foundation'/provenance['file']).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==provenance['sha256']
    reference=json.loads(raw)
    lookup={(row['s'],str(Fraction(row['epsilon']))):arb(row['entire_correction'])
            for row in reference['directed_Mellin_checks']}
    rows=[]
    for row in data['coupling_partial_sum_checks']:
        partial=arb(row['directed_finite_partial_sum'])
        tail=arb(row['directed_analytic_tail_bound'])
        target=lookup[(row['s'],row['epsilon'])]
        reconstructed=arb(partial,tail)
        assert reconstructed.contains(target)
        assert arb(row['directed_sum_plus_tail_enclosure']).contains(target)
        assert abs(partial-target)<tail
        rows.append({'s':row['s'],'epsilon':row['epsilon'],'M':row['M'],
                     'reconstructed_enclosure_contains_frozen_reference':True,
                     'stored_enclosure_contains_frozen_reference':True})
    assert len(rows)==12
    return {'source_hash_matches':True,'sha256':provenance['sha256'],
            'independently_reparsed_containments':rows}


def main():
    result={'exact_and_alternative_kernel_checks':kernel_checks(),
            'independent_96term_series_AGM_checks':independent_positive_series(),
            'serialized_Laplace_containment_checks':laplace_containments(),
            'review_ball_precision_bits':ctx.prec,'passed':True}
    (HERE/'numerical-scope-review-results.json').write_text(json.dumps(result,indent=2))
    print('PASS: exact kernel identity,3 alternative-variable integrals,4 exact-series AGM containments,12 Laplace containments and source hash.')


if __name__=='__main__':main()
