"""Test the log-scale and winding of the actual marked Dottie period-640 cycles.

Use a ball enclosing each periodic point, transport it through the ordered
stages, and sum coherent logarithms of the tangent derivatives. The chosen
stage constant logs and final multiplier argument are principal. The candidate
height comes from one winding of the measured return, before evaluating zeta.
"""
import sys
from pathlib import Path

sys.path.insert(0,str(Path(__file__).resolve().parent/"deps"))
from verify_dottie_horn_slice import acb, arb, ctx, HEIGHT, OFFSET, PERIOD, stage, trapping_data


def return_scale(parameter):
    center,_,residual,contraction = trapping_data(parameter)
    radius = (residual/(1-contraction)).upper()
    lifted = PERIOD*(parameter.log()+(-parameter).log())
    for _ in range(PERIOD):
        for rate in (-parameter,parameter):
            err = arb(0,radius)
            lifted += rate*(center+acb(err,err))
            center,radius = stage(center,radius,rate)
    multiplier = lifted.exp()
    scale = -lifted.real
    assert scale>0 and abs(multiplier)<1
    winding = ((lifted.imag-multiplier.arg())/(2*arb.pi())).unique_fmpz()
    assert winding is not None
    t = 2*arb.pi()*abs(winding)/scale
    return scale,int(winding),t


if __name__ == "__main__":
    assert ctx.prec==384
    # Freeze all candidate data before comparing with Riemann zeta.
    data=[]
    for side in (-1,0,1):
        parameter=acb(side*arb(OFFSET),arb(HEIGHT))
        for phase,rate in (("P",parameter),("Q",-parameter)):
            scale,wind,t=return_scale(rate)
            data.append((side,phase,scale,wind,t))
            print(side,phase,"log magnification",scale.str(16),"winding",wind,
                  "T",t.str(17),flush=True)
    for side,phase,_,_,t in data:
        magnitude=abs(acb(arb(1)/2,t).zeta())
        assert magnitude>0
        print(side,phase,"zeta magnitude",magnitude.str(16),flush=True)
