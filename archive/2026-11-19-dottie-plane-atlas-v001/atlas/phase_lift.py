"""Read the ordered derivative factors from the continued 640-stage orbit."""
import argparse
import json
import sys
from pathlib import Path
from flint import acb, acb_series, arb, ctx

HERE = Path(__file__).resolve().parent


def pair(z):
    return [z.real.str(30), z.imag.str(30)]


def calculate(repo):
    arc = repo.resolve()/"archive"
    sys.path[:0] = [str(arc/"2026-11-19-oriented-return-v001"/"computations"),
                    str(arc/"2026-11-19-zero-transport-v001"/"Dottie-Off-Axis-Return")]
    import flank_path as f
    from orbit_crossing import advance, stage
    from quarter_probe import degree
    from verify_dottie_horn_slice import trapping_data
    f.advance,f.stage,f.degree,f.trapping_data=advance,stage,degree,trapping_data
    ctx.prec,ctx.cap=448,5
    lo,hi,_=f.calibration(1)
    y0,y1=f.tinybracket(1,arb(45),lo,hi)
    orbit=f.moment(1,y0,y1,False)
    L=acb(f.real(f.ETA), f.real(y0).union(f.real(y1)))
    z,rad=orbit["p"],orbit["r"]
    total=acb(0)
    prod_center,prod_radius=acb(1),arb(0)
    stages=[]
    for j in range(640):
        rate=(-1 if j%2==0 else 1)*L
        exponent=rate*f.box(z,rad)
        z,rad=stage(z,rad,rate)
        # z_j -> exp(rate*z_j), with the pre-exponential value retained.
        lifted=rate.log()+exponent
        factor=rate*f.box(z,rad)
        assert lifted.exp().overlaps(factor)
        total+=lifted
        fc,fr=f.disc(factor)
        product,rounding=f.disc(prod_center*fc)
        prod_radius=(rounding+abs(prod_center)*fr+abs(fc)*prod_radius+fr*prod_radius).upper()
        prod_center=product
        if j<2:
            stages.append({"sign":-1 if j==0 else 1,"exponent":pair(exponent),"factor":pair(factor)})
    prod=f.box(prod_center,prod_radius)
    mu=orbit["mu"]
    assert prod.overlaps(mu) and total.exp().overlaps(mu)
    k=((total.imag-arb.pi()/4)/(2*arb.pi())).unique_fmpz()
    assert k is not None and abs(total.exp()-mu)<arb("1e-12") and abs(prod-mu)<arb("1e-12")
    # Attach the zero-path strain trace to the two endpoints of the atlas.
    record=json.loads((HERE/"plane_reference.json").read_bytes())["trough"]
    w0=acb(arb(record["sigma"]),arb(record["T"]))
    b0=arb(1)/6+arb(record["alpha"])/180
    w1=acb.zeta_zero(6)
    def deriv(z,b):
        t=acb_series([z,1],2)
        return (t.zeta(b)+t.zeta(1-b))[1]
    ratio=deriv(w0,b0)/deriv(w1,arb(1)/4)
    assert not ratio.contains(0)
    return dict(precision_bits=ctx.prec,phase="scalar P origin, negative then positive half-steps",
                native_angle_degrees=45,stages=640,L=pair(L),first_two=stages,
                lifted_log_multiplier=pair(total),lifted_winding_relative_to_45_degrees=int(k),
                multiplier=pair(mu),modulus=abs(mu).str(25),direct_product=pair(prod),
                sixth_transport_derivative=pair(ratio),sixth_length_factor=abs(ratio).str(18),
                sixth_area_factor=(abs(ratio)**2).str(18))


if __name__=="__main__":
    if not __debug__: raise RuntimeError("Use Python with assertions enabled")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo",required=True,type=Path)
    parser.add_argument("--out",required=True,type=Path)
    args=parser.parse_args()
    data=calculate(args.repo)
    args.out.write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(data,indent=2))
