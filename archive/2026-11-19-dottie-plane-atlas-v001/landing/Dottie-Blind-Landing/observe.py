"""Compute one local observed jet. Only the supplied past checkpoint is visible."""
from fractions import Fraction as F
import json
from pathlib import Path
import sys
from flint import acb, acb_series, arb, ctx

sys.path.insert(0,str(Path(__file__).resolve().parent.parent/"Dottie-Off-Axis-Return"))
from arithmetic_holdout_replay import centered_tube
from arithmetic_braid import shrink_root, ball
from arithmetic_reference import disk_check

def record(z):
    return {"real":z.real.str(40),"imag":z.imag.str(40)}

def observe(pkt):
    assert set(pkt)=={"case","cutoff","b_past","anchor","h_bounds"}
    ctx.prec,ctx.cap=192,3
    h0,h1=map(F,pkt["h_bounds"])
    base=F(1,6)
    b0,b1=base+h0/180,base+h1/180
    left=F(pkt["b_past"])
    assert base<=left<=b0<=b1<F(1,4)
    old=acb(arb(pkt["anchor"]["real"]),arb(pkt["anchor"]["imag"]))
    center=shrink_root(old.mid(),ball(left),4)
    radius=arb("1e-28")
    assert abs(old-center)<arb("1e-9")
    assert disk_check(center,arb("1e-9"),ball(left))[2] and disk_check(center,radius,ball(left))[2]
    def walk(node,a,b):
        if a==b: return node
        assert left<=a<b<=b0
        tube=centered_tube(node,radius,a,b)
        if tube is not None: return tube[0]
        assert b-a>F(1,2**60)
        mid=(a+b)/2
        return walk(walk(node,a,mid),mid,b)
    c=walk(center,left,b0)
    b=ball(b0).union(ball(b1))
    end_r=arb("1e-14") if b0!=b1 else radius
    assert disk_check(c,end_r,b)[2]
    z=c+acb(arb(0,end_r),arb(0,end_r))
    s=acb_series([z,1],3)
    spectral=s.zeta(b)+s.zeta(1-b)
    hb=-s*((s+1).zeta(b)-(s+1).zeta(1-b))
    hbb=z*(z+1)*((z+2).zeta(b)+(z+2).zeta(1-b))
    v=-hb[0]/spectral[1]
    a=-(hbb+2*hb[1]*v+2*spectral[2]*v*v)/spectral[1]
    v,a=v/180,a/180**2
    # The exact sixth trough, isolated in the earlier certificate.
    if pkt["case"]==6 and pkt["cutoff"]=="trough":
        assert v.imag.contains(0) and a.imag>0
        v=acb(v.real,0)
    h=ball(h0).union(ball(h1))
    D=15-h
    assert all(x.real.is_finite() and x.imag.is_finite() for x in [z,v,a])
    return {"case":pkt["case"],"cutoff":pkt["cutoff"],"h":h.str(36),
            "z":record(z),"v":record(v),"a":record(a),
            "past_anchor_shift":str(left),
            "forecast":{"constant":record(z),"linear":record(z+D*v),
                        "quadratic":record(z+D*v+D**2*a/2)}}

def no_disk(event,args):
    if event=="open": raise RuntimeError("forecast subprocess has no further file access")

if __name__=="__main__":
    if not __debug__: raise RuntimeError("Enable assertions")
    packet=json.load(sys.stdin)
    sys.addaudithook(no_disk)
    print(json.dumps(observe(packet)))
