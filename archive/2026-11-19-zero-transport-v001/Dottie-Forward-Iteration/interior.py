"""Audit ordinary Riemann zeta along the previously sealed moving-reference arcs."""
from pathlib import Path
from fractions import Fraction
import sys
import json
from flint import arb, acb, acb_series, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'Dottie-Second-Zero'))
from dyadic_geometry import tangent, parsed
from arithmetic_holdout_replay import centered_tube


def run(sweep):
    points = json.loads((HERE/f'sweep_{sweep}.json').read_bytes())['checkpoints']
    endpoints = [(position,parsed(points[i]['zero'])) for i,position in ((0,'start'),(-1,'end'))]
    size=arb('0.00001')
    anchors=[]
    for side, box in endpoints:
        if not box.real.contains(arb(1)/2):
            continue
        c=acb(arb(1)/2,box.imag.mid())
        assert abs(box-c)<size
        local=acb_series([c,1],2).zeta()
        big=c+acb(arb(0,size),arb(0,size))
        deriv=acb_series([big,1],2).zeta()[1]
        d=local[1].mid()
        ratio=(abs(local[0])/size+abs(deriv-d))/abs(d)
        assert ratio<1
        anchors.append((side,box,c,ratio))
    r=arb('1e-15')
    counts={'nonzero_by_direct_bound':0,'start_isolation_plus_increasing_height':0,
            'end_isolation_plus_increasing_height':0}
    for j in range(256):
        node=parsed(points[j]['zero']).mid()
        assert abs(parsed(points[j]['zero'])-node)<r
        left,right=[Fraction(p['shift']) for p in points[j:j+2]]
        pending=[(left,right,0)]
        while pending:
            a,b,depth=pending.pop()
            result=centered_tube(node,r,a,b)
            if result is not None:
                end,_,rad,c=result
                square=c+acb(arb(0,rad),arb(0,rad))
                derivative=acb_series([square,1],2).zeta()[1]
                if abs(c.zeta())>rad*abs(derivative):
                    counts['nonzero_by_direct_bound']+=1
                    node=end
                    continue
                reason=None
                for side,box,center,ratio in anchors:
                    if abs(c-center)+rad>=size or not tangent(c,rad,a,b).imag>0:
                        continue
                    if side=='start' and (a==Fraction(1,6) or node.imag-r>box.imag):
                        reason='start_isolation_plus_increasing_height'
                    if side=='end' and (b==Fraction(1,4) or end.imag+r<box.imag):
                        reason='end_isolation_plus_increasing_height'
                if reason:
                    counts[reason]+=1
                    node=end
                    continue
            assert depth<32,(j,a,b)
            m=(a+b)/2
            pending.extend(((m,b,depth+1),(a,m,depth+1)))
        assert abs(parsed(points[j+1]['zero'])-node)<2*r
    return dict(sweep=sweep,precision_bits=ctx.prec,counts=counts,
                endpoint_isolations={side:q.upper().str(16) for side,_,_,q in anchors},
                open_arc_free_of_ordinary_zeta_zeros=True)

if __name__=='__main__':
    ctx.prec,ctx.cap=256,3
    data=run(int(sys.argv[1]))
    (HERE/f'interior_{data["sweep"]}.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
    print(data)
