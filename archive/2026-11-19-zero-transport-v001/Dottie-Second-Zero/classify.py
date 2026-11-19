"""Identify a sealed endpoint using a zero count, never a table of ordinates.

Pass the two directed real/imaginary enclosures exactly as emitted by the path
verifier. For an endpoint near the critical line, Rouché's theorem gives a
unique simple zero in a reflection-invariant disk. The argument uses Taylor's
formula with the derivative enclosed on the entire disk. Counting all zeros
at rational heights bracketing this disk identifies the index independently.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

from flint import acb, acb_series, arb, ctx

def classify(real, imag):
    z = acb(arb(real), arb(imag))
    t = z.imag.mid()
    factor = acb(2)**z-1
    if factor.contains(0):
        index = int(round(float(t*arb(2).log()/(2*arb.pi()))))
        root = acb(0,2*index*arb.pi()/arb(2).log())
        assert abs(z-root)<arb('1e-8') and not z.zeta().contains(0)
        return dict(type="Euler factor", index=index, root=str(root),
                    zeta_magnitude=abs(z.zeta()).str(24))
    assert z.real>0 and z.real<1
    line=acb(arb(1)/2,t)
    radius=arb('1e-8')
    assert abs(z-line)<radius
    x=acb_series([line,1],2).zeta()
    d=x[1].mid()
    big=line+acb(arb(0,radius),arb(0,radius))
    dz=acb_series([big,1],2).zeta()[1]
    rouche=(abs(x[0])/radius+abs(dz-d))/abs(d)
    assert rouche<1
    # Endpoints of this rational bracket lie strictly outside our unique-zero disk.
    mesh=10**6
    integer=int((t*mesh).floor().unique_fmpz())
    low,high=Fraction(integer-1,mesh),Fraction(integer+2,mesh)
    a,b=[arb(s.numerator)/s.denominator for s in (low,high)]
    assert a<t-radius and t+radius<b
    lower=a.zeta_nzeros().unique_fmpz()
    upper=b.zeta_nzeros().unique_fmpz()
    assert lower is not None and upper is not None and upper==lower+1
    def hardy(t):
        phase=acb(arb(1)/4,t/2).lgamma().imag - t*arb.pi().log()/2
        value=acb(0,phase).exp()*acb(arb(1)/2,t).zeta()
        assert value.imag.contains(0)
        return value.real
    za,zb=hardy(a),hardy(b)
    assert za*zb<0
    return dict(type="Riemann zero",ordinal=int(upper),real_part="1/2 exactly",
                received_imaginary_ball=imag, symmetric_disk_radius="1e-8",
                rouche_ratio_upper=rouche.upper().str(18), lower_height=str(low),
                upper_height=str(high), counts=[int(lower),int(upper)],
                Hardy_Z_at_lower=za.str(25),Hardy_Z_at_upper=zb.str(25))
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('endpoint_file', type=Path,
                        help='sealed output of dyadic_continuation.py or triadic_continue.py')
    parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    ctx.prec=384
    ctx.cap=3
    frozen = args.endpoint_file.read_bytes()
    record = json.loads(frozen)
    assert record.get('terminal_shift',record.get('last_b')) == '1/4'
    point = record.get('terminal') or record['terminal_box']
    result=classify(point['real'],point['imag'])
    result['endpoint_file_sha256'] = sha256(frozen).hexdigest()
    payload=json.dumps(result,indent=2)
    if args.out: args.out.write_text(payload+'\n',encoding='utf8')
    print(payload)
