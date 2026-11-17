"""Headless scientific figures from the retained verified records."""
from pathlib import Path
import json
import re
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'figures';OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,
    'axes.spines.top':False,'axes.spines.right':False,'axes.titleweight':'bold',
    'savefig.dpi':220,'figure.facecolor':'white','axes.facecolor':'white'})
BLUE='#126782';ORANGE='#C65B21';GRAY='#62717E'

def center(s):
    return float(re.search(r'[-+]?\d+(?:\.\d*)?(?:e[-+]?\d+)?',s).group())

def save(fig,name):
    fig.savefig(OUT/(name+'.png'),bbox_inches='tight')
    fig.savefig(OUT/(name+'.svg'),bbox_inches='tight')
    plt.close(fig)

def normalization():
    j=json.loads((ROOT/'computations/binomial-normalization-results.json').read_text())
    rows=j['finite_cutoff_checks'];N=[x['N'] for x in rows]
    S=[center(x['direct_normalized_product']) for x in rows]
    C=center(j['exact_limit_constant'])
    fig,ax=plt.subplots(figsize=(9,4.8),layout='constrained')
    ax.plot(N,S,'o-',color=BLUE,lw=2,ms=7,label='Actual quartet product')
    ax.axhline(C,color=ORANGE,lw=1.8,ls='--',label=r'Exact limit $e^{\sin d/2}/G(3/2)^2$')
    ax.set_xscale('log',base=2);ax.set_xticks(N,[str(n) for n in N])
    ax.set(xlabel='Quartet cutoff N',ylabel=r'$N^{1/4}\prod_{n=1}^{N}(R_nB_n^2/2)$',
        title='The central-binomial normalization has an exact Barnes–Dottie limit',ylim=(1.11,1.234))
    ax.grid(axis='y',alpha=.18);ax.legend(loc='lower right',frameon=False)
    ax.annotate('1.225001707314…',xy=(N[-1],C),xytext=(-10,14),
                textcoords='offset points',ha='right',color=ORANGE)
    fig.text(.02,-.035,'Points: 384-bit directed arithmetic. N=1024 with controlled tail correction gives the limit within 3.10 × 10⁻¹⁵.',
             fontsize=9,color=GRAY)
    save(fig,'barnes-dottie-normalization')

def signed_orbit():
    j=json.loads((ROOT/'computations/signed-histories-results.json').read_text())
    f=j['four_stage_fold'];points=[]
    for s in f['stage_phases']:
        parts=s.split(' + ')
        points.append(complex(center(parts[0]),center(parts[1])))
    fig,axes=plt.subplots(1,2,figsize=(11.8,4.8),layout='constrained',gridspec_kw={'width_ratios':[1.2,1]})
    ax=axes[0]
    labels=['z₀','z₁','z₂ = conjugate(z₀)','z₃ = conjugate(z₁)']
    for k,(z,label) in enumerate(zip(points,labels)):
        nz=points[(k+1)%4]
        ax.annotate('',xy=(nz.real,nz.imag),xytext=(z.real,z.imag),
                    arrowprops={'arrowstyle':'->','lw':1.7,'color':BLUE if k<2 else ORANGE,'shrinkA':10,'shrinkB':10})
        ax.scatter([z.real],[z.imag],s=55,color=BLUE,zorder=3)
        ax.annotate(label,(z.real,z.imag),xytext=(8,10 if k<2 else -21),textcoords='offset points',fontsize=10)
        mid=(z+nz)/2
        ax.text(mid.real,mid.imag+(.09 if k<2 else -.13),['+','+','−','−'][k],
                fontsize=15,ha='center',color=BLUE if k<2 else ORANGE,
                bbox={'facecolor':'white','edgecolor':'none','pad':1})
    ax.axhline(0,color=GRAY,lw=.7,alpha=.5)
    ax.set(xlabel='Real phase',ylabel='Imaginary phase',title='Certified four-stage history ++−−',
           xlim=(-.2,2.7),ylim=(-1.18,1.18));ax.set_aspect('equal')
    ax.text(.02,.02,'Arrows show the discrete stage order.',transform=ax.transAxes,fontsize=8,color=GRAY)
    ax=axes[1]
    neg=center(f['iterative_residue']);pos=center(f['alternating_equal_count_history']['iterative_residue'])
    bars=ax.bar(['++−−\nL = 0.7501969723… i','+−+−\nDottie parameter'],[neg,pos],color=[ORANGE,BLUE],width=.56)
    ax.axhline(0,color=GRAY,lw=.8);ax.set(ylabel='Iterative residue ρ',title='Equal sign counts, different parabolic germs')
    ax.set_ylim(-.037,.09);ax.grid(axis='y',alpha=.15)
    for b,v in zip(bars,[neg,pos]):
        ax.annotate(f'{v:.9f}',(b.get_x()+b.get_width()/2,v),
                    xytext=(0,7 if v>0 else -16),textcoords='offset points',ha='center',fontsize=10)
    fig.text(.02,-.04,'Each bar uses its displayed parameter and actual four-stage return. ++−− is primitive; +−+− repeats its two-stage history.',fontsize=9,color=GRAY)
    save(fig,'ordered-four-stage-fold')

if __name__=='__main__':
    normalization();signed_orbit();print('Saved two PNG/SVG scientific figures from verified JSON records.')
