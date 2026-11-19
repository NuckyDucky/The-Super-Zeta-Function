"""Post-freeze independent test of the k=4 comparison's Euler-factor endpoint.
Checks a Rouché disk for the bare Hurwitz pair and proves the enclosed
ordinary zeta function is nowhere zero there. No list of zeros is used.
"""
from pathlib import Path
import json
import hashlib
from flint import acb, acb_series, arb, ctx

def record(p):
    text=p.read_text(encoding='utf8')
    return json.loads(text),hashlib.sha256(p.read_bytes()).hexdigest()

def verify():
    here=Path(__file__).resolve().parent
    data,checksum=record(here/'triadic_endpoint.json')
    _,other_checksum=record(here/'dyadic_continuation.json')
    assert data['status']=='finite-endpoint-frozen' and data['last_b']=='1/4'
    stored=data['terminal_box']
    box=acb(arb(stored['real']),arb(stored['imag']))
    n=int(round(float(box.imag*arb(2).log()/(2*arb.pi()))))
    exact=acb(0,2*n*arb.pi()/arb(2).log())
    center=exact.mid()
    radius=arb('1e-9')
    assert abs(box-center)<radius and abs(exact-center)<radius
    assert n!=0 and 2*radius<2*arb.pi()/arb(2).log()
    disk=center+acb(arb(0,radius),arb(0,radius))
    zbound=abs(disk.zeta())
    assert zbound>0
    b=arb(1)/4
    def jet(z):
        v=acb_series([z,1],2)
        return v.zeta(b)+v.zeta(1-b)
    vals=jet(center)
    fprime=vals[1].mid()
    factor=(abs(vals[0])/radius + abs(jet(disk)[1]-fprime))/abs(fprime)
    assert factor<1
    # q=4 factorization: 2^w (2^w-1) ζ(w). Since ζ is nonzero on the
    # enclosures, exact is the only reference zero in the common disk.
    return {'precision_bits':ctx.prec, 'triadic_endpoint_sha256':checksum,
            'dyadic_endpoint_sha256':other_checksum,'identification':f'{2*n}*pi*i/log(2)',
            'dyadic_factor_index':n,'common_disk_radius':'1e-9',
            'exact_imaginary_ball':exact.imag.str(44),
            'bare_Hurwitz_Rouche_ratio':factor.str(27),
            'zeta_magnitude_over_common_disk':zbound.str(27),
            'zeta_magnitude_at_explicit_point':abs(exact.zeta()).str(27)}

if __name__=='__main__':
    ctx.prec=384
    ctx.cap=2
    result=json.dumps(verify(),indent=2)+'\n'
    Path(__file__).with_name('triadic_classification.json').write_text(result,encoding='utf8')
    print(result)
