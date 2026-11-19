"""Compare the original grid flags with the two preimages of a moving critical value."""
import argparse
from hashlib import sha256
import json
from math import factorial
from pathlib import Path
import numpy as np
from flint import acb, acb_series, arb, ctx

HERE=Path(__file__).resolve().parent
COEFF=[float(arb.bernoulli(2*k))/factorial(2*k) for k in range(1,13)]

def jets(z,b):
    z,b=np.broadcast_arrays(np.asarray(z,complex),np.asarray(b,float))
    H, Hw, Hww, Hb=(np.zeros_like(z) for _ in range(4))
    for a,sgn in [(b,1),(1-b,-1)]:
        k=a[...,None]+np.arange(24)
        logs=np.log(k)
        powers=np.exp(-z[...,None]*logs)
        X=24+a
        lx=np.log(X)
        Y=np.exp(-z*lx)
        t=X/(z-1)+.5
        t1=-X/(z-1)**2
        t2=2*X/(z-1)**3
        ta=-1-z*.5/X
        p=np.ones_like(z); p1=np.zeros_like(z); p2=np.zeros_like(z)
        for n in range(1,24):
            p2,p1,p=p2*(z+n-1)+2*p1,p1*(z+n-1)+p,p*(z+n-1)
            if n%2:
                c=COEFF[n//2]*X**(-n)
                t+=c*p; t1+=c*p1; t2+=c*p2
                ta-=(z+n)*c*p/X
        H+=np.sum(powers,axis=-1)+Y*t
        Hw-=np.sum(powers*logs,axis=-1)-Y*(t1-lx*t)
        Hww+=np.sum(powers*logs*logs,axis=-1)+Y*(t2-2*lx*t1+lx*lx*t)
        Hb+=sgn*(-z*np.sum(powers/k,axis=-1)+Y*ta)
    return H,Hw,Hww,Hb

def trace(b0,n):
    s=np.linspace(0.,1.,n+1)
    b=b0+(.25-b0)*s**2
    c=np.full(b.shape,.235950387044401+36.9451796757567j)
    for _ in range(9):
        _,v,a,_=jets(c,b)
        c-=v/a
    K,hw,hww,hb=jets(c,b)
    c0=c[0]
    scale=np.sqrt(2*hb[0]/hww[0]*(.25-b0))
    paths=[]
    maxres=0.
    for sign in (1,-1):
        z=c0+sign*scale*s[1:]
        for _ in range(10):
            h,v,_,_=jets(z,b0)
            z-=(h-K[1:])/v
        maxres=max(maxres,float(np.max(abs(jets(z,b0)[0]-K[1:]))))
        paths.append(np.r_[c0,z])
    return b,c,paths,dict(max_abs_Hw=float(max(abs(hw))),max_abs_level_residual=maxres,
                           min_abs_Hww=float(min(abs(hww))),min_abs_Hb=float(min(abs(hb))))

def closest(p,path):
    a=path[:-1]; v=np.diff(path)
    # Closest point on each line segment to each grid point, in small batches.
    distance=np.empty(len(p)); times=np.empty(len(p))
    for j in range(0,len(p),64):
        w=p[j:j+64,None]-a
        t=np.clip((w*v.conjugate()).real/(abs(v)**2),0,1)
        r=abs(w-t*v)
        k=r.argmin(axis=1)
        distance[j:j+len(k)]=r[np.arange(len(k)),k]
        times[j:j+len(k)]=k+t[np.arange(len(k)),k]
    return distance,times/(len(path)-1)

def ab(z): return acb(float(np.real(z)),float(np.imag(z)))

def square(z,r): return z+acb(arb(0,r),arb(0,r))

def direct(z,b,n=3): 
    t=acb_series([z,1],n)
    return t.zeta(b)+t.zeta(1-b)

def isolate(z,b,order,level):
    w=ab(z)
    for _ in range(6):
        j=direct(w,b)
        w=(w-(j[order]-level)/((order+1)*j[order+1])).mid()
    R=arb("1e-25") if order else arb("1e-10")
    j=direct(w,b)
    box=square(w,R)
    jbox=direct(box,b)
    pivot=((order+1)*j[order+1]).mid()
    contraction=abs(1-(order+1)*jbox[order+1]/pivot)
    assert contraction<1 and abs((j[order]-level)/pivot)+contraction*R<R
    return box,jbox

def pair(z,b,order,level):
    root,j=isolate(z,b,order,level)
    return root,j[0]

def compare():
    ctx.prec,ctx.cap=192,4
    old=np.load(HERE/"plane_map.npz")
    sigma,y=old["x"],old["y"]
    grid=np.add.outer(1j*y,sigma).ravel()
    mask=~old["accepted"].ravel()
    assert sum(mask)==37
    f=json.loads((HERE/"plane_reference.json").read_bytes())["trough"]["alpha"]
    h=arb(f); b0=1/6+float(h.mid())/180
    exact_b0=(arb(1)/6+h/180).union(arb(b0))
    b,c,paths,diag=trace(b0,768)
    _,_,coarse,_=trace(b0,384)
    diag["coarse_chord_midpoint_max_deviation"]=max(float(max(abs(x[1::2]-(y[:-1]+y[1:])/2))) for x,y in zip(paths,coarse))
    dist,times=zip(*(closest(grid,arc) for arc in paths))
    nearest=np.minimum(*dist)
    branch=np.argmin(dist,axis=0)
    half_diag=abs((sigma[1]-sigma[0])+1j*(y[1]-y[0]))/2
    ix=np.flatnonzero(mask)
    out={"source_grid_sha256":sha256((HERE/"plane_map.npz").read_bytes()).hexdigest(),
         "original_gray_count":len(ix),"cell_side":float(sigma[1]-sigma[0]),"half_cell_diagonal":half_diag,
         "node_precision":"double, Euler-Maclaurin; independent interval certificates below",
         "critical_start":[c[0].real,c[0].imag],"critical_end":[c[-1].real,c[-1].imag],
         "arc_end":[[z[-1].real,z[-1].imag] for z in paths],"numerical_checks":diag}
    out["groups"]={}
    for name,g in [("flagged",mask),("accepted",~mask)]:
        d=nearest[g]/half_diag
        out["groups"][name]={"size":int(sum(g)),"dist_in_half_diagonals_min_median_max":
            [float(min(d)),float(np.median(d)),float(max(d))],"within_half_diagonal":int(sum(d<=1)),
            "near_branch_counts":[int(sum(branch[g]==k)) for k in (0,1)]}
    certified=[]
    for i in ix:
        k=branch[i]
        s=times[k][i]
        # Pick a rational binary value of b strictly between the two endpoint shifts when possible.
        bt=arb(float(b0+(.25-b0)*s*s))
        if not bt>exact_b0 or not bt<=arb(1)/4: continue
        j=int(round(s*(len(c)-1)))
        wc,K=pair(c[j],bt,1,acb(0))
        w0,_=pair(paths[k][j],exact_b0,0,K)
        inside=abs(w0.real-arb(grid[i].real))<arb("0.00625") and abs(w0.imag-arb(grid[i].imag))<arb("0.00625")
        certified.append({"row":int(i//len(sigma)),"column":int(i%len(sigma)),"arc":int(k),
                          "numerical_distance":float(nearest[i]),"shift":str(bt.mid().fmpq()),
                          "critical_point":[wc.real.str(17),wc.imag.str(17)],"start_preimage":[w0.real.str(17),w0.imag.str(17)],
                          "source_pixel_contains_level_preimage":bool(inside)})
    out["pixel_checks"]=certified
    out["inside_square_certificates"]=sum(j["source_pixel_contains_level_preimage"] for j in certified)
    return out

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--out",type=Path,default=HERE/"gray_locus.json")
    args=p.parse_args();data=compare()
    args.out.write_bytes((json.dumps(data,indent=2,allow_nan=False)+"\n").encode())
    print(json.dumps({k:v for k,v in data.items() if k!="pixel_checks"},indent=2))
