"""Certify a simple branch value inside the loop formed by the two first laps."""
import json
from pathlib import Path
from flint import acb, acb_series, arb, ctx

HERE=Path(__file__).resolve().parent


def jet(w):
    z=acb_series([w,1],4)
    a=(z*arb(2).log()).exp()
    return a*(a-1)*z.zeta()


def components(z):
    return [z.real.str(24),z.imag.str(24)]


def main():
    ctx.prec,ctx.cap=224,4
    z=acb(.25,36.9)
    for _ in range(12):
        coeff=jet(z)
        z=(z-coeff[1]/(2*coeff[2])).mid()
    r=arb('1e-30')
    box=z+acb(arb(0,r),arb(0,r))
    j=jet(z)
    jb=jet(box)
    pivot=(2*j[2]).mid()
    contraction=abs(1-2*jb[2]/pivot).upper()
    assert contraction<1 and abs(j[1]/pivot)+contraction*r<r
    assert not jb[2].contains(0) and not jb[0].contains(0)
    val=jb[0]/jet(acb(0,37))[0]
    data=json.loads((HERE/'phase_lift.json').read_bytes())
    ell=acb(*[arb(s) for s in data['lifted_log_multiplier']])
    time=abs(val).log()/ell.real
    lo=time*ell.imag
    hi=time*(ell.imag+2*arb.pi())
    assert 0<time and time<1 and lo<val.arg() and val.arg()<hi
    # For 0<t<1 the equal-radius arcs are strictly separated by 2*pi*t.
    # Traversing the principal spiral forward and the ordered one backward
    # gives a simple loop with winding +1 about every point between them.
    result=dict(precision_bits=ctx.prec,critical_w=components(box),critical_disk_radius=r.str(4),
                contraction=contraction.str(8),second_derivative=components(2*jb[2]),
                normalized_critical_value=components(val),time_at_critical_radius=time.str(22),
                ray_angle=val.arg().str(22),ordered_angle=lo.str(22),principal_angle=hi.str(22),
                winding=1,orientation='principal forward, ordered backward')
    (HERE/'critical_loop.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    if not __debug__: raise RuntimeError('Use Python with assertions enabled')
    main()
