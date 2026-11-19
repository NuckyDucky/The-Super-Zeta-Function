"""Exhibit what cancels at 54 degrees along both certified zero paths."""
from fractions import Fraction
import json
from pathlib import Path
from flint import acb, arb, ctx, dirichlet_char
from arithmetic_braid import tube
from arithmetic_reference import reference, complex_record

base = Path(__file__).resolve().parent

def run():
    ctx.prec = 256
    ctx.cap = 3
    char = dirichlet_char(5, 4)
    assert char(1)==1 and char(4)==1 and char(2)==-1 and char(3)==-1
    b = Fraction(1,5)
    shift = arb(1)/5
    records={}
    for seed in ('lattice','riemann'):
        path=json.loads((base/f'arithmetic_braid_{seed}.json').read_text())['paths'][0]
        sample=max((i for i in path['checkpoints'] if Fraction(i['shift'])<b),
                   key=lambda i:Fraction(i['shift']))
        interval=acb(arb(sample['zero']['real']),arb(sample['zero']['imag']))
        node=interval.mid()
        radius=arb('2e-13')
        assert abs(interval-node)<radius
        pending=[(Fraction(sample['shift']),b)]
        cells=0
        while pending:
            left,right=pending.pop()
            result=tube(node,radius,left,right)
            if result is None:
                assert right-left>Fraction(1,10**12)
                middle=(left+right)/2
                pending.extend(((middle,right),(left,middle)))
            else:
                node=result[0]
                cells+=1
        w=node+acb(arb(0,radius),arb(0,radius))
        z=w.zeta()
        quadratic=char.l(w)
        ordinary=(1-acb(5)**(-w))*z
        assert not z.contains(0) and not quadratic.contains(0)
        assert (quadratic+ordinary).contains(0)
        assert reference(w,shift).overlaps(acb(5/arb.pi())**w*(quadratic+ordinary)/2)
        records[seed]={'additional_certified_tubes':cells,'zero':complex_record(w),
                       'Riemann_zeta_magnitude':abs(z).str(25),
                       'ordinary_term':complex_record(ordinary),
                       'quadratic_L_term':complex_record(quadratic)}
    rho=acb.zeta_zero(1)
    at_rho=reference(rho,shift)
    quadratic=char.l(rho)
    assert not at_rho.contains(0)
    assert at_rho.overlaps(acb(5/arb.pi())**rho*quadratic/2)
    return {'directed_precision_bits':ctx.prec,'angle_degrees':54,'shift':'1/5','paths':records,
            'reference_at_first_Riemann_zero':complex_record(at_rho),
            'reference_magnitude_at_first_Riemann_zero':abs(at_rho).str(25),
            'quadratic_L_at_first_Riemann_zero':complex_record(quadratic)}

if __name__=='__main__':
    data=json.dumps(run(),indent=2)
    (base/'fifth_residue.json').write_text(data+'\n',encoding='utf-8')
    print(data)
