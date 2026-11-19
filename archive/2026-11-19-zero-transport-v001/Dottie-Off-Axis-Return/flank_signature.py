"""Interval measurement of the two actual scalar cap cycles at each flank.

Usage: python -B flank_signature.py PATH_TO_SUPER_ZETA_REPOSITORY [--out record.json]
The 30 degree stage below tests spectral transfer with a unit complex mark.
The native-parameter continuation is recorded separately in flank_path.py.
"""
import argparse
import json
import sys
from pathlib import Path

from flint import acb, arb, ctx


def inside(disk):
    c, r = disk
    er = arb(0, r)
    return c + acb(er, er)


def to_disk(z):
    c = acb(z.real.mid(), z.imag.mid())
    return c, abs(z - c).upper()


def affine(disk, a, b):
    c, extra = to_disk(a * disk[0] + b)
    return c, (extra + abs(a) * disk[1]).upper()


def rec(z):
    return z.str(27)


def run(repo):
    archive = repo / "archive"
    sys.path.insert(0, str(archive / "2026-11-17-quartet-return-recursion-v001/computations"))
    import verify_dottie_horn_slice as original
    sys.path.insert(0, str(archive / "2026-11-19-oriented-return-v001/computations"))
    from orbit_crossing import rational
    from quarter_probe import encode, decode, degree
    ctx.prec = 512
    if not __debug__:
        raise RuntimeError("Enable assertions.")
    eta, y = map(rational, [original.OFFSET, original.HEIGHT])
    rot = acb(arb(3).sqrt()/2, -arb(1)/2)

    def scalar(L):
        c, cap_radius, residual, k = original.trapping_data(L)
        trap_center = c
        before = (c, (residual/(1-k)).upper())
        for _ in range(30):
            c, r, *_ = original.advance(*before, L, 320)
            before = c, r
        base = before
        path = []
        exponents = acb(0)
        direct = acb(1)
        for _ in range(320):
            for s in (-1, 1):
                z = inside(before)
                exponents += s*L*z
                after = original.stage(*before, s*L)
                znext = inside(after)
                direct *= s*L*znext
                path.append((s, before, znext))
                before = after
        mu = (-L**2)**320 * exponents.exp()
        assert mu.overlaps(direct)
        assert abs(mu) < 1 and abs(mu) > 0
        # Complex derivative with respect to the scalar parameter L; if
        # physical parameter is -L, its derivative acquires a minus sign.
        dz = (acb(0),arb(0))
        for s, d, znext in path:
            dz = affine(dz, s*L*znext, s*inside(d)*znext)
        dz = to_disk(inside(dz)/(1-mu))
        log_slope = 640/L
        for s, d, znext in path:
            log_slope += s*(inside(d) + L * inside(dz))
            dz = affine(dz, s*L*znext, s*inside(d)*znext)
        unit = mu/abs(mu)
        trace = encode(unit)
        assert decode(trace).overlaps(unit)
        clockwise = encode(decode(trace)*rot)
        undo = decode(clockwise)*rot.conjugate()
        assert undo.overlaps(unit)
        return dict(base=base, path=path, trap_center=trap_center, k=k, residual=residual, cap_radius=cap_radius,
                    mu=mu, unit=unit, trace=trace, clockwise=clockwise, undo=undo,
                    log_slope=log_slope)

    sides = {}
    for word, realpart in [('left',-eta),('right',eta)]:
        L = acb(realpart, y)
        P, Q = scalar(L), scalar(-L)
        hx = original.stage(*P['base'], -L)
        # Test every phase of the true Q-rooted cycle for membership of the
        # half-image of the P-rooted cycle, in case the roots differ by a
        # cyclic rotation of the same scalar cycle.
        gaps = []
        for s, d, _ in Q['path'][::2]:
            assert s == -1
            gaps.append((abs(d[0]-hx[0])-d[1]-hx[1]).lower())
        if word == 'left':
            # B(p) = q, since B(p) is g_-L^320-fixed and inside q's trap.
            graft = hx
            target = Q
            index = 0
        else:
            # A(q) = p by the same argument in p's trap. Hence
            # B(p) = B(A(q)) = g_-L(q), Q cycle index 1.
            graft = original.stage(*Q['base'], L)
            target = P
            index = 1
        graft_bound = (abs(graft[0]-target['trap_center'])+graft[1]).upper()
        assert graft_bound < original.DISK_RADIUS
        other_gaps = [gap for j,gap in enumerate(gaps) if j != index]
        assert min(other_gaps)>0
        assert P['mu'].overlaps(Q['mu'])
        sides[word]=(P,Q,index,graft_bound,min(other_gaps))
    P0, Q0, *_ = sides['left']
    P1, Q1, *_ = sides['right']
    assert P0['mu'].conjugate().overlaps(Q1['mu'])
    assert Q0['mu'].conjugate().overlaps(P1['mu'])
    assert not P0['trace'][0].overlaps(P1['trace'][0])
    assert not P0['trace'][1].overlaps(P1['trace'][1])
    def export(x, sign):
        return dict(cap_root=rec(inside(x['base'])), multiplier=rec(x['mu']),
            magnitude=rec(abs(x['mu'])), phase_degrees=rec(degree(x['unit'])),
            M_plus=rec(x['trace'][0]), M_minus=rec(x['trace'][1]),
            vertical_slope_deg_per_y=rec(sign*x['log_slope'].real*180/arb.pi()),
            log_mu_derivative_per_physical_L=rec(sign*x['log_slope']),
            logpolar_jacobian=rec(abs(x['log_slope'])**2),
            inverse_parameter_sensitivity_per_radian_at_fixed_log_modulus=rec(1/abs(x['log_slope'])),
            contraction=rec(x['k']), cap_entrance_radius=rec(x['cap_radius']),
            spectral_clockwise_M_plus=rec(x['clockwise'][0]), spectral_clockwise_M_minus=rec(x['clockwise'][1]),
            spectral_undone_mark_error=rec(abs(x['undo']-x['unit']).upper()))
    assert all(abs(p['log_slope']) > 1e8 for p,q,*_ in sides.values())
    return dict(precision=ctx.prec, exact_height=original.HEIGHT, exact_offset=original.OFFSET,
        scalar_period=320,ordered_period=640, multiplier_methods_agree=True,
        reflected_cap_phases_conjugate_swapped=True, P_trace_boxes_disjoint_between_flanks=True,
        within_flank_P_and_Q_share_the_cyclic_multiplier=True,
        source_bare_order_M_plus_gt_M_minus_both_flanks=all(P['trace'][0]>P['trace'][1] for P,Q,*_ in sides.values()),
        flanks={k:dict(P=export(P,1),Q=export(Q,-1),Q_lap_index_of_B_of_P=index,
                      strict_trap_inclusion_via=('B(p) in q trap' if index==0 else 'A(q) in p trap'),
                      trap_radius=rec(original.DISK_RADIUS),distance_to_trap_center_upper=rec(graft),
                      other_319_phase_gap_lower=rec(gap))
                  for k,(P,Q,index,graft,gap) in sides.items()})


if __name__ == '__main__':
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('repo',type=Path)
    cli.add_argument('--out',type=Path)
    args=cli.parse_args()
    result=json.dumps(run(args.repo.resolve()), indent=2)+'\n'
    if args.out:
        args.out.write_text(result,encoding='utf8')
    print(result)
