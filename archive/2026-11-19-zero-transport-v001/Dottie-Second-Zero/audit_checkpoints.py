"""Count simple roots independently at all the recorded shifts."""
from pathlib import Path
from fractions import Fraction
import json
from flint import acb, acb_series, arb, ctx

ctx.prec=320
ctx.cap=2
here=Path(__file__).resolve().parent
def check(filename):
    record=json.loads((here/filename).read_text())
    worst=arb(0)
    r=arb('1e-10')
    for sample in record['checkpoints']:
        f=Fraction(sample.get('shift') or sample['b'])
        b=arb(f.numerator)/f.denominator
        w=acb(arb(sample['zero']['real']),arb(sample['zero']['imag']))
        center=w.mid()
        assert abs(w-center)<r
        def H(z):
            v=acb_series([z,1],2)
            return v.zeta(b)+v.zeta(1-b)
        at=H(center)
        D=at[1].mid()
        deriv=H(center+acb(arb(0,r),arb(0,r)))[1]
        ratio=(abs(at[0])/r+abs(deriv-D))/abs(D)
        assert ratio<1
        worst=max(worst,ratio.upper())
    return {'path':filename,'disks':len(record['checkpoints']),'radius':r.str(12),
            'max_Rouche_ratio':worst.str(16)}
if __name__=='__main__':
    result={'bits':ctx.prec,'checks':[check('dyadic_continuation.json'),check('triadic_endpoint.json')]}
    out=json.dumps(result,indent=2)
    print(out)
    (here/'checkpoint_audit.json').write_text(out+'\n',encoding='utf8')
