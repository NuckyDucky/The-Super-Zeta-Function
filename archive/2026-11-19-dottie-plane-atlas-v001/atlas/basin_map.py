"""Endpoint basins for two lifts of the same Dottie multiplier.

Run next to phase_lift.json. Classifications require agreement at two step sizes.
Every seed and both raw classifications are saved. The separate inverse-disk
certificate verifies a representative example independently of this plot.
"""
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap, BoundaryNorm
from matplotlib.patches import Patch
import numpy as np
from flint import arb, acb, acb_series, ctx

HERE = Path(__file__).resolve().parent
FACTOR = np.log(2.)
XMIN, XMAX, YMIN, YMAX = -5, 5, 24, 51


class Spectrum:
    """Local Taylor polynomials, including the derivative from the same series."""
    def __init__(self):
        nx, ny = XMAX-XMIN+1, YMAX-YMIN+1
        self.coeffs = np.zeros((17,ny,nx),complex)
        for j,y in enumerate(range(YMIN,YMAX+1)):
            for i,x in enumerate(range(XMIN,XMAX+1)):
                w = acb_series([acb(x,y),1],17)
                a = (w*arb(2).log()).exp()
                h = a*(a-1)*w.zeta()
                self.coeffs[:,j,i] = [complex(h[k]) for k in range(17)]

    def field(self,z):
        x=np.clip(np.rint(z.real).astype(int),XMIN,XMAX)
        y=np.clip(np.rint(z.imag).astype(int),YMIN,YMAX)
        coeff=self.coeffs[:,y-YMIN,x-XMIN]
        d=z-(x+1j*y)
        val=coeff[-1]
        der=np.zeros_like(val)
        for row in coeff[-2::-1]:
            der=der*d+val
            val=val*d+row
        return val/der


def inside(z):
    return (z.real>XMIN-.1)&(z.real<XMAX+.1)&(z.imag>YMIN-.1)&(z.imag<YMAX+.1)


def follow(spec,seeds,lift,roots,base_dt,max_step_length):
    z=seeds.ravel().copy()
    t=np.zeros(len(z))
    active=np.arange(len(z))
    classes=np.full(len(z),-1,dtype=np.int16)
    for _ in range(1900):
        if not len(active):
            break
        current=z[active]
        speed=lift*spec.field(current)
        dt=np.minimum(base_dt,max_step_length/np.maximum(np.abs(speed),1e-12))
        mid=current+dt*speed/2
        end=current+dt*lift*spec.field(mid)
        close=np.abs(end[:,None]-roots[None,:])
        idx=np.argmin(close,axis=1)
        found=close[np.arange(len(end)),idx]<.004
        classes[active[found]]=idx[found]
        t[active]+=dt
        z[active]=end
        active=active[(~found)&inside(end)&(t[active]<8)]
    return classes.reshape(seeds.shape)


def main():
    ctx.prec,ctx.cap=144,17
    phase=json.loads((HERE/'phase_lift.json').read_text())
    ell=complex(*[float(arb(v)) for v in phase['lifted_log_multiplier']])
    logs=[ell+2j*np.pi,ell]
    ys=np.linspace(34.65,39,117)
    xs=np.linspace(-1.25,1.25,95)
    seeds=xs[None,:]+1j*ys[:,None]
    entries=[(complex(acb.zeta_zero(k)),f'Riemann #{k}') for k in range(3,12)]
    entries.extend((2j*np.pi*k/FACTOR,f'Elementary k={k}') for k in range(3,7))
    roots=np.array([r for r,label in entries])
    spec=Spectrum()
    raw=[]; classes=[]
    for lift in logs:
        coarse=follow(spec,seeds,lift,roots,.055,.05)
        fine=follow(spec,seeds,lift,roots,.022,.018)
        raw.extend([coarse,fine])
        classes.append(np.where(coarse==fine,fine,-1))
    valid=(classes[0]>=0)&(classes[1]>=0)
    diff=valid&(classes[0]!=classes[1])
    cases={}
    for w in [0+37j,.25+37j,.25+36.75j,-.25+37j,.5+36.75j,0+36.75j,.75+37j,-.5+37j]:
        labels=[]
        for lift in logs:
            idx=follow(spec,np.array([w]),lift,roots,.015,.012)[0]
            labels.append(entries[idx][1] if idx>=0 else 'unresolved')
        cases[str(w)]=labels
    pairs={}
    for i,j in zip(classes[0][diff],classes[1][diff]):
        k=entries[i][1]+' to '+entries[j][1]
        pairs[k]=pairs.get(k,0)+1
    summary=dict(grid=[len(xs),len(ys)],x_limits=[xs[0],xs[-1]],T_limits=[ys[0],ys[-1]],
                 labels=[e[1] for e in entries],both_resolved=int(valid.sum()),different=int(diff.sum()),
                 comparisons=pairs,probes=cases,
                 steps=[.055,.022],max_step_lengths=[.05,.018],max_laps=8,terminal_radius=.004,
                 display='matching classifications at both step sizes; numerical samples')
    np.savez_compressed(HERE/'basins.npz',xs=xs,ys=ys,raw=np.array(raw),classes=classes,roots=roots)
    (HERE/'basin-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)
    ids=sorted(set(np.unique(classes))|{-1})
    palette={'Riemann #5':'#E2D3A2','Riemann #6':'#267D87','Riemann #7':'#8170A8',
             'Elementary k=4':'#E59A55','Riemann #8':'#6687A2','Elementary k=5':'#DB827D'}
    names=['Unresolved' if i<0 else entries[i][1] for i in ids]
    colors=['#d5d6d8' if name=='Unresolved' else palette.get(name,plt.get_cmap('tab20')(k)) for k,name in enumerate(names)]
    cmap=ListedColormap(colors)
    fig=plt.figure(figsize=(12.8,6.9))
    grid=fig.add_gridspec(1,3,width_ratios=[1,1,1.02],left=.067,right=.98,top=.81,bottom=.13,wspace=.115)
    left=fig.add_subplot(grid[0,0])
    axs=[left,fig.add_subplot(grid[0,1],sharey=left)]
    axs[1].tick_params(labelleft=False)
    key=fig.add_subplot(grid[0,2])
    key.set_axis_off()
    for ax,data,lift,title in zip(axs,classes,logs,['Principal angle  ·  +45°','Ordered stages  ·  −315°']):
        ax.pcolormesh(xs,ys,np.searchsorted(ids,data),cmap=cmap,norm=BoundaryNorm(np.arange(len(ids)+1)-.5,len(ids)),shading='nearest',rasterized=True)
        path=[37j]
        dt=.008
        vel=lambda z: lift*spec.field(np.array([z]))[0]
        for _ in range(500):
            w=path[-1]
            k1=vel(w)
            k2=vel(w+dt*k1/2)
            k3=vel(w+dt*k2/2)
            k4=vel(w+dt*k3)
            path.append(w+dt*(k1+2*k2+2*k3+k4)/6)
        path=np.array(path)
        ax.plot(path.real,path.imag,color='#172D36',lw=3)
        ax.plot(path.real,path.imag,color='white',lw=1.35)
        for w,label in entries:
            if xs[0]<w.real<xs[-1] and ys[0]<w.imag<ys[-1]:
                ax.plot(w.real,w.imag,'*',mec='#142d3b',mfc='white',ms=12)
        ax.plot(0,37,'o',mec='white',mfc='#142D3B',ms=6)
        ax.set(xlabel='Real part of starting point',title=title,xlim=(xs[0],xs[-1]),ylim=(ys[0],ys[-1]))
    axs[0].set_ylabel('Starting height')
    fig.suptitle('Which zero does each starting point approach?',fontweight='bold',fontsize=18,y=.967)
    fig.text(.5,.901,'Each pixel is one starting point. Its color gives the limiting zero estimated for that angle convention.',ha='center',fontsize=10.5)
    key.text(.035,1.005,'Destination colors',size=12,weight='bold',transform=key.transAxes)
    display_labels=['Riemann #5','Riemann #6','Riemann #7','Riemann #8','Elementary k=4','Unresolved']
    for i,name in enumerate(display_labels):
        if name not in names: continue
        y=.92-i*.133
        color=colors[names.index(name)]
        key.add_patch(plt.Rectangle((.035,y-.015),.065,.042,fc=color,ec='#384650',lw=.45,transform=key.transAxes))
        if name=='Unresolved':
            title='Numerically undecided'
            detail='Step-size checks did not settle a label.'
        else:
            w=next(w for w,label in entries if label==name)
            title=name.replace('Riemann #','Riemann zero #').replace('Elementary k=4','Zero of 2ʷ − 1   (k = 4)')
            coordinate=f'½ + {w.imag:.5f}i' if w.real else f'{w.imag:.5f}i'
            detail=coordinate+('   ·   off plot' if w.imag<ys[0] or w.imag>ys[-1] else '')
        key.text(.13,y+.008,title,transform=key.transAxes,va='center',size=9.6,weight='bold')
        key.text(.13,y-.047,detail,transform=key.transAxes,va='center',size=8.9,color='#394A52')
    key.text(.035,.10,'●  Shared start at 37i\n━  White trace follows that start\n★  Zero inside the displayed rectangle',transform=key.transAxes,va='top',size=8.8,linespacing=1.5)
    fig.text(.067,.041,'Colors between sampled points are for display. The two limits from the disk of radius 0.000001 about 37i are interval-certified.',fontsize=9,color='#394A52')
    fig.savefig(HERE/'basins.png',dpi=190)
    plt.close(fig)


if __name__=='__main__':
    main()
