"""Finite-jet reconstruction of Nick's three recorded marked-cap orbits.

Exact printed rational y midpoints and source scalar periods are inputs. At 180
and 280 decimal digits, reconstruct U rationally from normalized c3/c4, then
iterate the resulting entire normalized return on both local fixed-point sheets.
Every step is compared with the original g_(iy) orbit from the marked cap z=1.
These point-arithmetic checks complement the source's interval capture proofs.
"""
from pathlib import Path
import hashlib
import json
import mpmath as mp

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'sources' / 'nick-dottie-spire.tex'
WINDOWS = [
    (639, 639, '.5098930698771419799831'),
    (640, 320, '.5098929835386691077069'),
    (641, 641, '.5098928862668716592052'),
]
PRECISIONS = (180, 280)


def fmt(value, digits=120):
    return mp.nstr(value, digits)


def enc(z, digits=120):
    return {'real': fmt(mp.re(z), digits), 'imaginary': fmt(mp.im(z), digits)}


def run(dps):
    result = []
    with mp.workdps(dps):
        d = mp.findroot(lambda z: mp.cos(z)-z, mp.mpf('.74'))
        s = mp.sin(d)
        yd = mp.exp(-s)
        limit = mp.mpf('1e-100')
        solve_tol = mp.power(10, -dps+15)
        for paired_period, scalar_period, printed_y in WINDOWS:
            y = mp.mpf(printed_y)
            L = mp.j*y
            tau = mp.log(y/yd)
            epsilon = lambda u: u/mp.cos(u)
            lf = lambda u: mp.j*epsilon(u)*mp.exp(-u*mp.tan(u))
            df = lambda u: lf(u)*(1-epsilon(u)**2)/u
            roots = [mp.findroot(lambda u: lf(u)-L,
                      d*mp.exp(sign*mp.sqrt(-tau/(1+s))), df=df,
                      solver='newton', tol=solve_tol)
                     for sign in (-1, 1)]
            assert abs(roots[0]-roots[1]) > mp.mpf('.001')
            assert max(abs(u-d) for u in roots) < mp.mpf('.01')
            g = lambda z: mp.exp(L*mp.exp(-L*z))
            orbit = [mp.mpc(1)]
            for n in range(scalar_period):
                orbit.append(g(orbit[-1]))
            sheets = []
            for sign, u in zip((-1, 1), roots):
                a = u*mp.tan(u)
                P = mp.exp(a+mp.j*u)
                Q = mp.exp(a-mp.j*u)
                U = L*Q
                V = -L*P
                mu = U*V
                b = -mu*L*(1+U)/2
                # Compute the normalized coefficients as original-map derivatives.
                # The rational recovery, rather than direct U, feeds the entire G.
                c3 = mp.diff(g, P, 3)/(6*b*b)
                c4 = mp.diff(g, P, 4)/(24*b**3)
                residue = 1-mu*c3
                w = (24*mu**2*c4-22+42*residue)/(6*residue-2)
                recovered_U = (1+w)/(1-w)
                recovered_V = mu/recovered_U
                recovery_error = max(abs(recovered_U-U), abs(recovered_V-V))
                assert recovery_error < limit
                fixed_residual = max(abs(lf(u)-L), abs(g(P)-P),
                                     abs(mp.exp(L*Q)-P), abs(mp.exp(-L*P)-Q))
                assert fixed_residual < limit
                G = lambda x: mu**2*(1+recovered_U)/(2*recovered_U)*mp.expm1(
                    recovered_U*mp.expm1(2*x/(mu*(1+recovered_U))))
                xx = b*(1-P)
                normalized = [xx]
                errors = [mp.mpf(0)]
                for n in range(1, scalar_period+1):
                    xx = G(xx)
                    expected = b*(orbit[n]-P)
                    error = abs(xx-expected)
                    assert error < limit, (dps, paired_period, sign, n, error)
                    normalized.append(xx)
                    errors.append(error)
                maximum = max(errors)
                sheets.append({'sign': sign, 'u': u, 'P': P, 'Q': Q,
                    'U': U, 'recovered_U': recovered_U, 'V': V, 'mu': mu,
                    'b': b, 'c3': c3, 'c4': c4, 'normalized': normalized,
                    'errors': errors, 'max_error': maximum,
                    'max_error_index': errors.index(maximum),
                    'recovery_error': recovery_error, 'fixed_residual': fixed_residual})
            result.append({'paired_period': paired_period,
                'scalar_period': scalar_period, 'printed_y': printed_y,
                'L': L, 'tau': tau, 'orbit': orbit, 'sheets': sheets})
    return result


def main():
    source_text = SOURCE.read_text(encoding='utf8')
    for paired, scalar, y in WINDOWS:
        assert y[1:] in source_text
        assert f'{paired} & {scalar}' in source_text
    runs = {precision: run(precision) for precision in PRECISIONS}
    records = []
    with mp.workdps(300):
        threshold = mp.mpf('1e-100')
        for low, high in zip(runs[180], runs[280]):
            original_errors = [abs(x-y) for x, y in zip(low['orbit'], high['orbit'])]
            assert max(original_errors) < threshold
            sheets = []
            for sl, sh in zip(low['sheets'], high['sheets']):
                normalized_cross = [abs(x-y) for x, y in zip(sl['normalized'], sh['normalized'])]
                assert max(normalized_cross) < threshold
                sheets.append({'seed_sign': sh['sign'],
                    **{key: enc(sh[key]) for key in ['u', 'P', 'Q', 'U', 'recovered_U', 'V', 'mu', 'b', 'c3', 'c4']},
                    'marked_normalized_cap': enc(sh['normalized'][0]),
                    'final_normalized_cap': enc(sh['normalized'][-1]),
                    'maximum_normalized_cross_precision_difference': fmt(max(normalized_cross), 12),
                    'precision_checks': [
                        {'decimal_precision': p,
                         'maximum_jet_recovery_error': fmt(r['recovery_error'], 12),
                         'maximum_fixed_pair_residual': fmt(r['fixed_residual'], 12),
                         'maximum_every_iterate_transport_error': fmt(r['max_error'], 12),
                         'maximum_error_iteration': r['max_error_index']}
                        for p, r in [(180, sl), (280, sh)]]})
            records.append({'paired_period_from_source': high['paired_period'],
                'scalar_period_from_source': high['scalar_period'],
                'exact_rational_printed_y': high['printed_y'],
                'rational_denominator': '10000000000000000000000',
                'L': enc(high['L']), 'logarithmic_tau': enc(high['tau']),
                'original_marked_cap': enc(mp.mpc(1)),
                'final_original_cap': enc(high['orbit'][-1]),
                'original_iterations_checked': high['scalar_period'],
                'normalized_iterations_checked_per_sheet': high['scalar_period'],
                'maximum_original_cross_precision_difference': fmt(max(original_errors), 12),
                'sheets': sheets})
    output = {'status': 'passed', 'arithmetic': 'mpmath point arithmetic',
        'decimal_precisions': list(PRECISIONS),
        'absolute_error_threshold': '1e-100',
        'source': {'file': str(SOURCE), 'sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            'table_label': 'tab:windows',
            'credit': 'Nick canonical Dottie-spire table supplies the midpoint inputs and paired/scalar periods; its interval capture certificates remain credited to that source.'},
        'scope': 'At the three exact printed rational midpoints, recover U from actual cubic/quartic derivatives and compare every transported cap iterate through the stated scalar period on both computed local fixed-point sheets; repeat original and normalized orbits at two precisions.',
        'original_iterations_per_precision': sum(row[1] for row in WINDOWS),
        'normalized_iterations_per_precision': 2*sum(row[1] for row in WINDOWS),
        'windows': records}
    (HERE/'marked-cap-results.json').write_text(json.dumps(output, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'status': output['status'],
        'original_iterations_per_precision': output['original_iterations_per_precision'],
        'normalized_iterations_per_precision': output['normalized_iterations_per_precision'],
        'worst_original_cross_precision': max(float(w['maximum_original_cross_precision_difference']) for w in records),
        'worst_transport_180': max(float(s['precision_checks'][0]['maximum_every_iterate_transport_error']) for w in records for s in w['sheets']),
        'worst_transport_280': max(float(s['precision_checks'][1]['maximum_every_iterate_transport_error']) for w in records for s in w['sheets']),
        'worst_jet_recovery_180': max(float(s['precision_checks'][0]['maximum_jet_recovery_error']) for w in records for s in w['sheets'])}, indent=2))


if __name__ == '__main__':
    main()
