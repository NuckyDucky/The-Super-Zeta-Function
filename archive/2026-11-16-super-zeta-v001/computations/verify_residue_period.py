"""Exact moments, directed AGM periods, and point chord-density checks.

All elliptic integrals use the PARAMETER m, not the modulus sqrt(m).
Directed statements use python-flint at 512 bits. Theta identities and
quadratures are separately labelled high-precision point checks.
"""
from pathlib import Path
from fractions import Fraction
import json
import math
import platform
import time
import mpmath as mp
from flint import arb, acb, ctx

HERE=Path(__file__).resolve().parent
ctx.prec=512

def ra(value):
    value=Fraction(value)
    return arb(value.numerator)/value.denominator

def exact_coefficients():
    B=[Fraction(math.comb(2*n,n),4**n) for n in range(34)]
    coefficients=[v*v for v in B]
    recurrence=[]
    for n in range(33):
        residual=4*(n+1)**2*coefficients[n+1]-(2*n+1)**2*coefficients[n]
        assert residual==0
        recurrence.append(str(residual))
    assert coefficients[0]==1 and coefficients[1]==Fraction(1,4)
    for n in range(33):
        # The half-integer beta moment, written with exact factorials.
        moment=Fraction(math.factorial(2*n),4**n*math.factorial(n)**2)
        assert moment==B[n] and moment**2==coefficients[n]
    coverage=[];previous=Fraction(0);sum_new=Fraction(0)
    for N in range(1,33):
        covered=1-Fraction(3,4)**N
        added=Fraction(1,4)*Fraction(3,4)**(N-1)
        assert covered-previous==added
        sum_new+=added;assert sum_new==covered
        coverage.append({'N':N,'expected_covered_fraction':str(covered),
                         'expected_new_fraction':str(added),
                         'probability_fixed_point_uncovered':str(Fraction(3,4)**N)})
        previous=covered
    return B,coefficients,{'coefficients_and_moments':[
        {'n':n,'B_n':str(B[n]),'B_n_squared':str(coefficients[n])} for n in range(33)],
        'ODE_coefficient_residuals_powers_0_to_32':recurrence,
        'ODE':'z(1-z)M_second+(1-2z)M_prime-M/4=0',
        'coverage_exact_fractions':coverage,
        'status':'exact Fraction recurrence, beta moments and coverage identities passed'}

def directed_periods(coefficients):
    records=[]
    cases=[('1/4',Fraction(1,4)),('1/2',Fraction(1,2)),
           ('99/100',Fraction(99,100)),
           ('1-10^-40',1-Fraction(1,10**40))]
    for label,zq in cases:
        complement=1-zq
        # Form the known exact complement directly. This retains input
        # information close to z=1 rather than subtracting rounded balls.
        a,b=arb(1),ra(complement).sqrt()
        steps=[]
        for j in range(17):
            lower=(1/a).lower();upper=(1/b).upper()
            assert lower>0 and upper>=lower
            width=upper-lower
            enclosure=arb((lower+upper)/2,(upper-lower)/2)
            steps.append({'iteration':j,'lower_bound':lower.str(160),
                          'upper_bound':upper.str(160),
                          'width_upper_bound':width.upper().str(30)})
            if j<16:
                a,b=(a+b)/2,(a*b).sqrt()
        reference=2*acb(ra(zq)).elliptic_k()/arb.pi()
        assert reference.imag.contains(0)
        assert enclosure.overlaps(reference.real)
        assert width.upper()<arb('1e-145')
        builtin_agm=1/arb(1).agm(ra(complement).sqrt())
        assert enclosure.overlaps(builtin_agm)
        partial=sum((ra(coefficients[n])*ra(zq)**n for n in range(33)),arb(0))
        tail=ra(coefficients[33])*ra(zq)**33/ra(complement)
        assert reference.real>partial and reference.real<partial+tail
        with mp.workdps(220):
            zm=mp.mpf(zq.numerator)/zq.denominator
            point=2*mp.ellipk(zm)/mp.pi
            assert enclosure.contains(arb(mp.nstr(point,200)))
            point_string=mp.nstr(point,160)
        records.append({'parameter_label':label,'exact_parameter':str(zq),
          'exact_complement':str(complement),'working_bits':ctx.prec,
          'manual_AGM_iterations':16,'directed_AGM_enclosure':enclosure.str(160),
          'directed_AGM_width_upper_bound':width.upper().str(50),
          'directed_Acb_elliptic_k_parameter_enclosure':reference.str(160),
          'directed_Acb_real_width_upper_bound':(reference.real.upper()-reference.real.lower()).upper().str(50),
          'directed_builtin_Arb_AGM_enclosure':builtin_agm.str(160),
          'directed_builtin_AGM_width_upper_bound':(builtin_agm.upper()-builtin_agm.lower()).upper().str(50),
          'positive_series_terms_0_to_32':partial.str(65),
          'positive_series_tail_bound':tail.str(55),
          'point_reference_220dps':point_string,
          'conditioning_record':'manual and builtin AGM use the exact rational complement; Acb elliptic_k receives its 512-bit rounded parameter ball',
          'selected_iteration_bounds':[steps[j] for j in [0,1,2,4,8,12,16]],
          'parameter_convention':'elliptic_k(m) and M(m)=2K(m)/pi; sqrt(1-m) is the AGM complement'})
    return records

def theta_checks():
    rows=[]
    with mp.workdps(180):
        for real,imag in [('0','1'),('0','2'),('.2','1')]:
            tau=mp.mpc(real,imag);q=mp.exp(mp.pi*1j*tau)
            t2,t3=mp.jtheta(2,0,q),mp.jtheta(3,0,q)
            lam=(t2/t3)**4
            # All selected points lie on the principal continuation from i.
            assert abs(lam)<1
            period=2*mp.ellipk(lam)/mp.pi
            error=abs(period-t3**2)
            assert error<mp.mpf('1e-165')
            if real=='0' and imag=='1':assert abs(lam-mp.mpf('.5'))<mp.mpf('1e-165')
            rows.append({'tau':mp.nstr(tau,35),'nome_convention':'q=exp(pi*i*tau)',
               'lambda':mp.nstr(lam,120),'theta3_squared':mp.nstr(t3**2,120),
               'M_lambda_principal_period':mp.nstr(period,120),
               'absolute_identity_residual':mp.nstr(error,40),
               'point_working_decimal_digits':180,
               'certificate_status':'high-precision point check; not an interval certificate'})
    return rows

def chord_density_checks(coefficients):
    rows=[];T=160
    for n in [0,1,4]:
        rate=ra(Fraction(4*n+1,2))
        tail=2*(-rate*T).exp()/(arb.pi()*rate)
        exact=coefficients[n]
        # This directed interval follows from the exact moment theorem,
        # positivity, and the analytic tail. It is independent of quadrature.
        truncated_enclosure=arb(ra(exact)-tail/2,tail/2)
        with mp.workdps(100):
            def integrand(u):
                return 2*mp.exp(-(2*n+1)*u)/(mp.pi*mp.agm(1,mp.exp(-u)))
            quadrature=mp.quad(integrand,[0,mp.mpf('.25'),1,4,16,64,T])
            target=mp.mpf(exact.numerator)/exact.denominator
            point_distance=abs(quadrature-target)
            # A numerical consistency tolerance is stated separately from
            # the rigorous integral-tail bound and is not used as a proof.
            tolerance=mp.mpf('1e-90')+mp.mpf(tail.upper()._mpf_)
            assert point_distance<tolerance
            rows.append({'moment_n':n,'exact_total_moment':str(exact),
               'substitution':'x=exp(-2u), sqrt(x)=exp(-u)',
               'integrand':'(2/pi)*exp(-(2n+1)u)/AGM(1,exp(-u))',
               'truncation_T':T,'directed_analytic_tail_upper_bound':tail.str(85),
               'rigorous_symbolic_truncation_interval':{
                   'lower':'exact_total_moment - directed_analytic_tail_upper_bound',
                   'upper':'exact_total_moment'},
               'directed_truncated_integral_enclosure_from_exact_moment_and_tail':truncated_enclosure.str(110),
               'point_quadrature_100dps':mp.nstr(quadrature,100),
               'point_distance_from_exact_total_moment':mp.nstr(point_distance,40),
               'point_consistency_tolerance':mp.nstr(tolerance,40),
               'point_working_decimal_digits':100,
               'quadrature_status':'point evaluation only; no directed quadrature-error claim',
               'tail_proof':'AGM(1,exp(-u))>=exp(-u/2); integrate (2/pi)exp(-(2n+1/2)u)'})
    return rows

def main():
    start=time.perf_counter()
    B,coefficients,exact=exact_coefficients()
    out={'status':'all exact, directed AGM and analytic-tail checks passed; point checks passed separately',
       'precision':{'python':platform.python_version(),'directed_bits':ctx.prec,
                    'AGM_point_reference_dps':220,'theta_point_dps':180,'quadrature_point_dps':100},
       'exact_Fraction_results':exact,'directed_period_results':directed_periods(coefficients),
       'theta_modular_point_checks':theta_checks(),
       'chord_density_moment_checks':chord_density_checks(coefficients),
       'evidence_categories':{
          'exact':'integer/Fraction coefficients, ODE recurrence, beta moments and coverage fractions',
          'directed':'manual AGM brackets, Acb/Arb consistency, positive series bounds and analytic density tails',
          'point':'220-digit period references, 180-digit theta identities and 100-digit quadratures'},
       'primary_formulas':[
          'https://dlmf.nist.gov/19.8','https://dlmf.nist.gov/20.9',
          'https://dlmf.nist.gov/15.9.E24'],
       'elapsed_seconds':time.perf_counter()-start}
    path=HERE/'residue-period-results.json'
    path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(out['status']);print('seconds',out['elapsed_seconds'])
    for row in out['directed_period_results']:
        print(row['parameter_label'],'AGM width',row['directed_AGM_width_upper_bound'])
    for row in out['chord_density_moment_checks']:
        print('moment',row['moment_n'],'point error',row['point_distance_from_exact_total_moment'],
              'directed tail',row['directed_analytic_tail_upper_bound'])

if __name__=='__main__':main()
