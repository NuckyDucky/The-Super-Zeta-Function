"""Retrospective interval proof of the final contiguous quadratic-forecast windows."""
import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path
from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "Dottie-Fold-Arrival"))
from fold_shapes import Branch, ball, jets_from_partials, param, partials
from verify import jets, square, sgn


def quadratic(w, v, a, h):
    d = arb(15) - h
    return w + d*v + d**2*a/2


def run():
    ctx.prec, ctx.cap = 192, 4
    path = HERE / "certified.json"
    frozen = json.loads(path.read_bytes())
    item = next(row for row in frozen["endpoints"] if row["case"] == 6)
    center = acb(arb(item["center"]["real"]), arb(item["center"]["imag"]))
    endpoint = square(center, arb(item["disk_radius"]))
    branch = Branch(HERE.parent)
    tolerances = [F(1,10), F(1,100), F(1,1000)]
    # Start just before the archived lower bound of the last trough.
    first, last = F("13.40917355"), F(15)
    crossings = {q: [] for q in tolerances}
    endpoints = {}

    def point(h):
        if h not in endpoints:
            w,v,a = branch.node_values(param(h))
            endpoints[h] = quadratic(w,v,a,ball(h)) - endpoint
        return endpoints[h]

    assert all(abs(point(first)) > ball(t) > abs(point(last)) for t in tolerances)
    stack = [(first, last)]
    node = branch.at(param(first))
    cells = 0
    while stack:
        l, r = stack.pop()
        x, y, m = param(l), param(r), (l+r)/2
        cert = branch.centered_tube(node,branch.radius,x,y)
        if cert is not None:
            end,_,rad,c = cert
            width = ball((y-x)/2)
            B = ball(x).union(ball(y))
            W = square(c,rad)
            D = partials(W,B,3)
            mid = partials(c,ball(param(m)),2)
            for n in (2,1):
                for j in range(n+1):
                    i = n-j
                    err = (rad*abs(D[i+1,j])+width*abs(D[i,j+1])).upper()
                    D[i,j] = square(mid[i,j],err)
            v,a,jerk = jets_from_partials(D)
            span = ball(l).union(ball(r))
            direct = quadratic(W,v,a,span)-endpoint
            # Derivative of the endpoint predictor is (15-h)^2 w'''(h)/2.
            derivative = (15-span)**2*jerk/2
            if derivative.is_finite():
                wmid = branch.at(param(m))
                assert abs(wmid-c)+branch.radius < rad
                centered = square(point(m),(ball((r-l)/2)*abs(derivative)).upper())
                delta = acb(direct.real.intersection(centered.real),
                            direct.imag.intersection(centered.imag))
                size = abs(delta)
                possible = [q for q in tolerances if size.overlaps(ball(q))]
                # If the derivative of the squared error is negative, this
                # threshold can be crossed at most once and only downwards.
                if not possible or (delta.conjugate()*derivative).real < 0:
                    for q in possible:
                        a_sign = sgn(abs(point(l))-ball(q))
                        b_sign = sgn(abs(point(r))-ball(q))
                        assert a_sign >= b_sign
                        if a_sign > b_sign:
                            crossings[q].append((l,r))
                    node = end
                    cells += 1
                    continue
        assert r-l > F(1,2**36)
        stack.extend([((l+r)/2,r),(l,(l+r)/2)])
    assert abs(node-center)+branch.radius < arb("1e-9")
    assert branch.disk_check(node,arb("1e-9"),ball(param(last)))[2]
    result=[]
    for q, values in crossings.items():
        assert len(values)==1
        l,r=values[0]
        for _ in range(48):
            m=(l+r)/2
            if sgn(abs(point(m))-ball(q))>0: l=m
            else: r=m
        result.append(dict(tolerance=str(q),crossing_degrees=ball(l).union(ball(r)).str(22),
                           remaining_degrees=ball(last-r).union(ball(last-l)).str(22),
                           exact_bracket=[str(l),str(r)]))
    return dict(certified_endpoint_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                precision_bits=ctx.prec,domain_degrees=[str(first),str(last)],cells=cells,
                error="complex modulus of one-shot endpoint quadratic minus independently continued endpoint",
                result=result)


if __name__=="__main__":
    if not __debug__: raise RuntimeError("Enable assertions")
    output=run()
    (HERE/"horizon.json").write_text(json.dumps(output,indent=2)+"\n")
    print(output)
