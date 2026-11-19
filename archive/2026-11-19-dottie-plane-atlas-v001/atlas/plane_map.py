"""Finite Hurwitz-level transport between the last sixth-branch trough and landing."""
import argparse
import hashlib
import json
from fractions import Fraction
from math import factorial
from pathlib import Path

import numpy as np
from flint import acb, acb_series, arb, ctx


HERE = Path(__file__).resolve().parent
N = 24
M = 12
COEFFICIENTS = [float(arb.bernoulli(2*k))/factorial(2*k) for k in range(1,M+1)]
END = 15.0
STEP_AGREEMENT = 2e-5
LEVEL_TOL = 5e-7


def fields(w,b):
    """Euler–Maclaurin jets (H,H_w,H_b) of the unweighted symmetrized Hurwitz sum."""
    w = np.asarray(w,dtype=complex)
    shape = w.shape
    s = w.ravel()
    valid = np.isfinite(s) & (abs(s.real)<9) & (abs(s.imag)<65)
    s = np.where(valid,s,0.5+37j)
    with np.errstate(all="ignore"):
        H = np.zeros_like(s)
        Hw = np.zeros_like(s)
        Hb = np.zeros_like(s)
        # Each derivative uses the same Euler–Maclaurin series. Direct powers
        # account for the terms of the finite Dirichlet sum.
        for a,sign in ((b,1),(1-b,-1)):
            k = np.arange(N,dtype=float)+a
            logs = np.log(k)
            powers = np.exp(-s[:,None]*logs)
            X = N+a
            Y = np.exp(-s*np.log(X))
            tail = X/(s-1)+0.5
            tail_w = -X/(s-1)**2
            tail_a = -1-s/(2*X)
            rising = np.ones_like(s)
            rising_w = np.zeros_like(s)
            for order in range(1,2*M):
                alpha = s+order-1
                rising_w = rising_w*alpha+rising
                rising = rising*alpha
                if order%2:
                    c = COEFFICIENTS[order//2]*X**(-order)
                    tail += c*rising
                    tail_w += c*rising_w
                    tail_a -= (s+order)*c*rising/X
            H += np.sum(powers,axis=1)+Y*tail
            Hw += -np.sum(powers*logs,axis=1)+Y*(tail_w-np.log(X)*tail)
            Hb += sign*(-s*np.sum(powers/k,axis=1)+Y*tail_a)
    return tuple(np.where(valid,f,np.nan+1j*np.nan).reshape(shape) for f in (H,Hw,Hb))


def rk(w0,h0,steps):
    """Clockwise RK4, retaining the nodes needed to compare two full paths."""
    delta = (END-h0)/steps
    levels = [w0.copy()]
    w = w0.copy()
    min_slope = np.full(w.shape,np.inf)
    def velocity(z,h):
        _,hw,hb = fields(z,1/6+h/180)
        np.minimum(min_slope,abs(hw),out=min_slope)
        with np.errstate(all="ignore"):
            return -hb/(180*hw)
    for n in range(steps):
        h = h0+n*delta
        k1 = velocity(w,h)
        k2 = velocity(w+delta*k1/2,h+delta/2)
        k3 = velocity(w+delta*k2/2,h+delta/2)
        k4 = velocity(w+delta*k3,h+delta)
        w = w+(delta/6)*(k1+2*k2+2*k3+k4)
        levels.append(w.copy())
    return np.asarray(levels),min_slope


def transported(w0,h0,coarse):
    b0 = 1/6+h0/180
    H0,D0,_ = fields(w0,b0)
    first, _ = rk(w0,h0,coarse)
    fine, min_slope = rk(w0,h0,2*coarse)
    error_nodes = np.max(abs(first-fine[::2]),axis=0)
    error_level = np.zeros(w0.shape)
    for j in range(1,len(fine)):
        h = h0+(END-h0)*j/(len(fine)-1)
        level,_,_ = fields(fine[j],1/6+h/180)
        error_level = np.maximum(error_level,abs(level-H0)/(1+abs(H0)))
    end = fine[-1]
    _,D1,_ = fields(end,1/4)
    with np.errstate(all="ignore"):
        length_log2 = np.log2(abs(D0/D1))
    mask = (error_nodes<=STEP_AGREEMENT)&(error_level<LEVEL_TOL)&np.isfinite(length_log2)&(min_slope>1e-4)
    return end,length_log2,mask,error_nodes,error_level,min_slope


def exact_fields(w,b):
    s = acb(w.real,w.imag)
    B = arb(b)
    t = acb_series([s,1],2)
    series = t.zeta(B)+t.zeta(1-B)
    db = s*((s+1).zeta(1-B)-(s+1).zeta(B))
    return [complex(z) for z in (series[0],series[1],db)]


def reference(path):
    data = json.loads(path.read_bytes())
    trough = data["trough"]
    start = complex(float(arb(trough["sigma"]).mid()),float(arb(trough["T"]).mid()))
    h = float(arb(trough["alpha"]).mid())
    points = [start]
    angles = [h]
    for entry in data["checkpoints"]:
        point = entry["zero"]
        points.append(complex(float(arb(point["real"]).mid()),float(arb(point["imag"]).mid())))
        angles.append(float(180*(Fraction(entry["shift"])-Fraction(1,6))))
    return np.array(angles),np.array(points)


def compute(out, *, x=None, y=None, prefix="plane_map"):
    ctx.prec,ctx.cap = 160,2
    reference_path=HERE/"plane_reference.json"
    angles,track = reference(reference_path)
    h0=angles[0]
    if x is None:
        x=np.linspace(-.75,.65,113)
    if y is None:
        y=np.linspace(36.75,37.95,97)
    W=np.add.outer(1j*y,x).ravel()
    outputs=list(transported(W,h0,12))
    depth=np.full(W.shape,24)
    for coarse in (32,96,192):
        select=np.flatnonzero(~outputs[2])
        if not len(select): break
        current=transported(W[select],h0,coarse)
        for vector,v in zip(outputs,current): vector[select]=v
        depth[select]=2*coarse
    dest,log2,mask,step_err,level_err,mind=outputs
    assert mask.any()
    # Validate the series and the level independently with FLINT on a
    # rectangular lattice, in the strongest expansion and contraction, and
    # at every published marked checkpoint. This tests both H and its jets.
    good=np.flatnonzero(mask)
    sample=list(good[::max(1,len(good)//25)])
    sample+= [good[np.argmax(log2[good])],good[np.argmin(log2[good])]]
    sample=np.unique(sample)
    jets_error=np.zeros(3)
    invariant=0.0
    for idx in sample:
        hf,hw,hb=exact_fields(W[idx],1/6+h0/180)
        ef,ew,eb=exact_fields(dest[idx],.25)
        invariant=max(invariant,abs(ef-hf)/(1+abs(hf)))
        for z,b,ref in ((W[idx],1/6+h0/180,(hf,hw,hb)),(dest[idx],.25,(ef,ew,eb))):
            compare=np.asarray(fields(z,b))
            jets_error=np.maximum(jets_error,np.abs(compare-ref)/(1+np.abs(ref)))
    zero_residual=max(abs(exact_fields(w,1/6+h/180)[0]) for w,h in zip(track,angles))
    zfine,_=rk(track[:1],h0,192)
    spacing=(END-h0)/192
    # Compare the independent RK solver to each certified checkpoint by
    # integrating to a local step exactly ending at that shift.
    checkpoints_error=[]
    for angle,w in zip(angles[1:],track[1:]):
        step=min(191,int((angle-h0)/spacing))
        at=h0+step*spacing
        z=zfine[step,0]
        d=angle-at
        def v(s,h):
            _,D,B=fields(s,1/6+h/180)
            return -B/(180*D)
        a=v(z,at); b=v(z+d*a/2,at+d/2); c=v(z+d*b/2,at+d/2); e=v(z+d*c,angle)
        checkpoints_error.append(abs(z+d*(a+2*b+2*c+e)/6-w))
    assert max(jets_error)<2e-11 and invariant<LEVEL_TOL and zero_residual<2e-12
    assert max(checkpoints_error)<1e-8
    lengths=2**log2[mask]
    nearest_start=int(np.argmin(abs(W-track[0])))
    examples=np.array([.075+36.75j,-.525+37.3125j])
    example_paths,_=rk(examples,h0,384)
    def item(i):
        return dict(sigma0=W[i].real,T0=W[i].imag,sigma1=dest[i].real,T1=dest[i].imag,
                    length_ratio=2**log2[i],level_real=fields(W[i],1/6+h0/180)[0].real.item(),
                    level_imag=fields(W[i],1/6+h0/180)[0].imag.item())
    mark_D0=exact_fields(track[0],1/6+h0/180)[1]
    mark_D1=exact_fields(track[-1],.25)[1]
    summary=dict(reference_sha256=hashlib.sha256(reference_path.read_bytes()).hexdigest(),
        domain={"Re w":[float(x[0]),float(x[-1])],"Im w":[float(y[0]),float(y[-1])]},
        h_degrees=[h0,END],shape=[len(y),len(x)],grid_count=len(W),accepted=int(sum(mask)),
        unresolved=int(sum(~mask)),RK_steps_used={str(int(k)):int(sum(depth==k)) for k in np.unique(depth)},
        accepted_min_length_ratio=float(min(lengths)),accepted_max_length_ratio=float(max(lengths)),
        accepted_median_length_ratio=float(np.median(lengths)),accepted_fraction_compressed=float(np.mean(lengths<1)),
        max_common_node_disagreement=float(max(step_err[mask])),max_relative_level_drift=float(max(level_err[mask])),
        marked_zero_length_ratio=abs(mark_D0/mark_D1),marked_zero_max_checkpoint_error=float(max(checkpoints_error)),
        marked_zero_sampled_residual=float(zero_residual),flint_comparison_points=len(sample),
        flint_relative_jet_errors=jets_error.tolist(),flint_max_endpoint_relative_level_drift=float(invariant),
        most_compressed=item(good[np.argmin(log2[good])]),most_expanded=item(good[np.argmax(log2[good])]),
        nearest_marked_grid_point=item(nearest_start),agreement_threshold=STEP_AGREEMENT,level_drift_threshold=LEVEL_TOL)
    reshape=lambda t:t.reshape(len(y),len(x))
    np.savez_compressed(out/(prefix+".npz"),x=x,y=y,end=reshape(dest),log2_length=reshape(log2),
        accepted=reshape(mask),node_error=reshape(step_err),level_error=reshape(level_err),
        min_sampled_abs_Hw=reshape(mind),steps=reshape(depth),marked_h=angles,marked_w=track,
        example_h=np.linspace(h0,END,385),example_w=example_paths)
    (out/(prefix+".json")).write_text(json.dumps(summary,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    print(json.dumps(summary,indent=2),flush=True)


def mark_unresolved(ax,x,y,ok,size):
    """Cross out each unresolved seed, including those in nearly neutral areas."""
    j,i=np.where(~ok)
    for width,color in ((2.0,"#fffcf0"),(.85,"#191c1c")):
        ax.scatter(x[i],y[j],s=size,marker="x",linewidths=width,color=color,zorder=5)


def plot(out,staircase=None):
    """Render the field of length ratios and the complete before/after lattice."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.collections import LineCollection
    from matplotlib.colors import TwoSlopeNorm
    from matplotlib.ticker import MultipleLocator, FormatStrFormatter

    data = np.load(out/"plane_map.npz")
    x, y = data["x"], data["y"]
    start = np.add.outer(1j*y, x)
    end, ok = data["end"].copy(), data["accepted"]
    scale = data["log2_length"].copy()
    entries=json.loads((staircase or HERE/"staircase.json").read_bytes())["entries"]
    restored=np.zeros(ok.shape,dtype=bool)
    for entry in entries:
        j,i=entry["row"],entry["column"]
        assert not ok[j,i] and not restored[j,i] and [x[i],y[j]]==entry["start"]
        end[j,i]=complex(*(float(arb(v).mid()) for v in entry["end"]))
        scale[j,i]=np.log2(float(arb(entry["length"]).mid()))
        restored[j,i]=True
    assert np.array_equal(restored,~ok)
    track = data["marked_w"]
    trails = data["example_w"]
    accepted, unresolved = int(ok.sum()), int((~ok).sum())
    half_step = (x[1]-x[0])/2
    paper, ink, secondary = "#faf9f5", "#192e38", "#4d6067"
    grid_ink, edge_ink = "#42637d", "#203f54"
    A, B = "#542788", "#ab5310"
    fig_options = {"facecolor":paper, "dpi":105}
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":11,"axes.labelcolor":ink,
        "text.color":ink,"xtick.color":secondary,"ytick.color":secondary,"axes.edgecolor":"#8b9695",
        "axes.spines.right":False,"axes.spines.top":False,"savefig.facecolor":paper})

    def add_label(ax, w, label, xytext, color=ink):
        ax.annotate(label, xy=(w.real,w.imag), xytext=xytext, textcoords="offset points",
                    fontsize=10.5, fontweight="bold", color=color, zorder=13,
                    va="bottom" if xytext[1]>=0 else "top",
                    ha="left" if xytext[0]>=0 else "right",
                    bbox=dict(boxstyle="round,pad=.18",facecolor="white",edgecolor="none",alpha=.89))

    def axes(ax):
        ax.set_aspect("equal", adjustable="box")
        ax.set_xlabel("Real part of w")
        ax.xaxis.set_major_locator(MultipleLocator(.25))
        ax.yaxis.set_major_locator(MultipleLocator(.25))
        ax.yaxis.set_major_formatter(FormatStrFormatter("%.2f"))
        ax.tick_params(length=3.5)

    def marked(ax, labels):
        ax.plot(track.real,track.imag,color="white",lw=4.6,zorder=6)
        ax.plot(track.real,track.imag,color=ink,lw=1.8,zorder=7)
        ax.plot(track[0].real,track[0].imag,"o",ms=6.5,mfc=paper,mec=ink,mew=1.5,zorder=8)
        ax.plot(track[-1].real,track[-1].imag,"*",ms=13,mfc=ink,mec="white",mew=.7,zorder=8)
        if labels:
            add_label(ax,track[0],"Last height minimum",(-8,-6))
            add_label(ax,track[-1],"Sixth zero",(-4,8))

    # Original complete cell extents, including all four outer half-cells.
    fig=plt.figure(figsize=(11.5,7.55),**fig_options)
    fig.text(.065,.938,"How sensitive is the landing to where you start?",fontsize=22,fontweight="bold")
    fig.text(.065,.89,"Follow two very close starts through the final 1.59083° clockwise. The color measures their change in separation.",fontsize=12,color=secondary)
    ax=fig.add_axes([.085,.242,.585,.585])
    axes(ax)
    ax.set_ylabel("Imaginary part of w")
    cmap=plt.get_cmap("PuOr_r").copy()
    cmap.set_bad("#969fa2")
    im=ax.pcolormesh(x,y,scale,shading="nearest",cmap=cmap,
                     norm=TwoSlopeNorm(vcenter=0,vmin=-2,vmax=3),rasterized=True)
    mark_unresolved(ax,x,y,ok,9)
    ax.set_xlim(x[0]-half_step,x[-1]+half_step)
    ax.set_ylim(y[0]-.023,y[-1]+half_step)
    marked(ax,True)
    for trail,color,text,offset in [(trails[:,0],A,"A",(6,7)),(trails[:,1],B,"B",(7,6))]:
        w=trail[0]
        ax.plot(w.real,w.imag,"o",ms=6,mfc=color,mec="white",mew=1.2,zorder=10)
        add_label(ax,w,text,offset,color)
    ax.text(.02,.976,"Color at the starting point",transform=ax.transAxes,va="top",fontsize=9.5,
            bbox=dict(facecolor=paper,edgecolor="none",alpha=.86,pad=3))
    failed=start[~ok]
    marker=failed[np.argmin(abs(failed-(-.35+36.97j)))]
    ax.annotate("Refined starts",xy=(marker.real,marker.imag),xytext=(-.69,36.95),
                arrowprops=dict(arrowstyle="-|>",color=ink,lw=1),
                bbox=dict(facecolor=paper,edgecolor="none",alpha=.92,pad=2),
                fontsize=9.5,fontweight="bold",zorder=12)
    sidebar=.695
    fig.text(sidebar,.82,"Two nearby starts",fontsize=15,fontweight="bold",va="top")
    fig.text(sidebar,.761,"Purple brings their landings closer.\nOrange spreads them farther apart.\nOff-white keeps their distance near 1×.",
             fontsize=10.7,linespacing=1.48,color=secondary,va="top")
    fig.text(sidebar,.615,"A   0.286×",fontsize=15,fontweight="bold",color=A,va="top")
    fig.text(sidebar,.563,"A tiny starting gap shrinks to 29%.",fontsize=10.6,va="top")
    fig.text(sidebar,.488,"B   8.075×",fontsize=15,fontweight="bold",color=B,va="top")
    fig.text(sidebar,.435,"The same gap grows eightfold.",fontsize=10.6,va="top")
    fig.text(sidebar,.354,"Why start at the minimum?",fontsize=14,fontweight="bold",va="top")
    fig.text(sidebar,.295,"The black path stops descending here,\nthen rises 0.37035 to the sixth zero.\nAt its start, the gap scales by 0.9391×.",
             fontsize=10.3,linespacing=1.48,color=secondary,va="top")
    fig.text(sidebar,.148,"×   Grid refinement",fontsize=10.8,fontweight="bold",va="top")
    fig.text(sidebar,.109,f"All {unresolved} marked centers, A and B have\nseparate interval certificates.",fontsize=10.25,linespacing=1.4,color=secondary,va="top")
    cbax=fig.add_axes([.108,.131,.544,.025])
    cb=fig.colorbar(im,cax=cbax,orientation="horizontal",ticks=[-2,-1,0,1,2,3],extend="max",extendfrac=.025)
    cb.ax.set_xticklabels(["0.25×","0.5×","1×","2×","4×","8×"])
    cb.ax.tick_params(labelsize=10)
    cb.set_label("Final separation ÷ starting separation, for an infinitesimal gap",labelpad=7,fontsize=10.5)
    fig.savefig(out/"plane_strain.png",dpi=220)
    plt.close(fig)

    # The actual rectangular lattice and every accepted destination share
    # the same two axis ranges. Rows/columns and perimeter lines connect
    # immediate neighbors only. Drop suspect edges rather than joining
    # the two sides of an unresolved break.
    fig=plt.figure(figsize=(11.65,8.05),**fig_options)
    fig.text(.065,.940,"Where the full starting grid goes",fontsize=24,fontweight="bold")
    fig.text(.065,.895,"The same angle change, from 13.40917° to 15° clockwise. Each panel uses identical axis limits.",
             fontsize=12.2,color=secondary)
    left=fig.add_axes([.087,.187,.40,.626])
    right=fig.add_axes([.557,.187,.40,.626])
    for p in (left,right):
        axes(p)
        p.set_facecolor("#f7f7f2")
        p.xaxis.set_major_locator(MultipleLocator(.5))
        p.yaxis.set_major_locator(MultipleLocator(.5))
        p.yaxis.set_major_formatter(FormatStrFormatter("%.1f"))
        p.set_axisbelow(True)
        p.grid(True,color="#dcdfda",lw=.5)
    left.set_ylabel("Imaginary part of w")
    left.set_title(f"The {len(x)} × {len(y)} starting grid",loc="left",fontsize=15,fontweight="bold",pad=8)
    right.set_title(f"All {start.size:,} destinations",loc="left",fontsize=15,fontweight="bold",pad=8)
    left.scatter(start.real.ravel(),start.imag.ravel(),s=1.2,color="#7795a0",alpha=.50,
                 edgecolors="none",zorder=2)
    cloud=end[ok]
    right.scatter(cloud.real,cloud.imag,s=1.85,color="#477989",alpha=.54,edgecolors="none",zorder=2)
    for p,points in ((left,start[restored]),(right,end[restored])):
        p.scatter(points.real,points.imag,s=11.5,marker="D",color="#98504d",
                  edgecolors="white",linewidths=.22,zorder=4)

    safe=ok.copy()
    for i,j in zip(*np.where(~ok)):
        safe[max(0,i-1):min(len(y),i+2),max(0,j-1):min(len(x),j+2)]=False

    def segments(pos,allowed,stretch):
        good=allowed[:-1]&allowed[1:]
        if stretch is not None:
            step=abs(np.diff(pos))
            bound=3*(x[1]-x[0])*np.maximum(stretch[:-1],stretch[1:])
            good &= (step <= np.minimum(.105,bound))
        z0,z1=pos[:-1][good],pos[1:][good]
        return np.stack([np.column_stack([z0.real,z0.imag]),np.column_stack([z1.real,z1.imag])],axis=1)

    def lattice(p,positions,allowed,stretch):
        for axis,length in ((0,len(y)),(1,len(x))):
            for k in sorted(set([0,length-1,*range(0,length,12)])):
                selection=(k,slice(None)) if axis==0 else (slice(None),k)
                perimeter=k in (0,length-1)
                edges=segments(positions[selection],allowed[selection],
                               None if stretch is None else stretch[selection])
                p.add_collection(LineCollection(edges,colors=edge_ink if perimeter else grid_ink,
                                 linewidths=1.30 if perimeter else .75,
                                 alpha=.9 if perimeter else .66,zorder=3))

    lattice(left,start,np.ones(ok.shape,dtype=bool),None)
    lattice(right,end,safe,2**data["log2_length"])
    ref=track[0]
    left.plot(ref.real,ref.imag,"o",ms=6.5,mfc=paper,mec=ink,mew=1.5,zorder=8)
    add_label(left,ref,"Trough",(5,6))
    marked(right,False)
    add_label(right,track[-1],"Sixth zero",(-3,8))
    for i,(color,label) in enumerate([(A,"A"),(B,"B")]):
        trail=trails[:,i]
        for p,w,offset in ((left,trail[0],(4,5)),(right,trail[-1],(4,-5))):
            p.plot(w.real,w.imag,"o",ms=6,mfc=color,mec="white",mew=.9,zorder=7)
            add_label(p,w,label,offset,color)
        right.plot(trail.real,trail.imag,color="white",lw=2.8,zorder=4)
        right.plot(trail.real,trail.imag,color=color,lw=1.2,zorder=5)
        k=int(.56*len(trail))
        right.annotate("",xy=(trail[k+5].real,trail[k+5].imag),xytext=(trail[k-5].real,trail[k-5].imag),
                       arrowprops=dict(arrowstyle="-|>",color=color,mutation_scale=12),zorder=6)

    # Mark the extreme horizontal destinations. All other endpoints, including
    # those from the outer rows and columns, also participate in the limits.
    cloud=end.ravel()
    for name,idx,offset in (("Leftmost",np.argmin(cloud.real),(5,-6)),
                            ("Rightmost",np.argmax(cloud.real),(-6,5))):
        w=cloud[idx]
        right.plot(w.real,w.imag,"D",ms=4.8,mfc=edge_ink,mec="white",mew=.6,zorder=5)
        add_label(right,w,name,offset)
    combined=np.r_[start.ravel(),cloud,trails.ravel(),track]
    xlim=(combined.real.min()-.13,combined.real.max()+.13)
    ylim=(combined.imag.min()-.13,combined.imag.max()+.13)
    for p in (left,right):
        p.set_xlim(*xlim)
        p.set_ylim(*ylim)
    assert np.all((xlim[0]<cloud.real)&(cloud.real<xlim[1])&(ylim[0]<cloud.imag)&(cloud.imag<ylim[1]))
    from matplotlib.lines import Line2D
    handles=[Line2D([],[],marker="o",ls="",color="#477989",ms=4,label=f"{accepted:,} grid solutions"),
             Line2D([],[],color=grid_ink,lw=1,label="Sample rows and columns"),
             Line2D([],[],color=edge_ink,lw=2,label="Starting grid perimeter, tracked"),
             Line2D([],[],marker="D",ls="",color="#98504d",ms=5,label=f"{unresolved} interval-verified additions")]
    fig.legend(handles=handles,loc="lower center",bbox_to_anchor=(.5,.087),ncol=4,frameon=False,
               handlelength=1.5,columnspacing=1.6,fontsize=10.0)
    fig.text(.065,.045,"A and B follow two independently verified paths. The black path carries the marked zero. "
             "Mesh lines break near sharply separated destinations.",fontsize=10.5,color=secondary)
    fig.savefig(out/"plane_grid.png",dpi=220)
    plt.close(fig)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=HERE)
    parser.add_argument("--plot-only",action="store_true")
    parser.add_argument("--refined",type=Path,default=HERE/"staircase.json",help="Directed fine-grid refinement")
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    if not args.plot_only: compute(args.output)
    plot(args.output,args.refined)
