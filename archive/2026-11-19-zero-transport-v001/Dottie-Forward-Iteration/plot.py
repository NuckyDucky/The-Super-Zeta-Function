"""Render the three sealed paths. All coordinates come from the continuation."""
from fractions import Fraction
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from flint import arb

here=Path(__file__).resolve().parent
colors=['#17675D','#275E98','#9C491F']
labels=[r'$\rho_3\ \to\ \rho_4$',r'$\rho_4\ \to\ 8\pi i/\log 2$',r'$8\pi i/\log 2\ \to\ \rho_7$']
plt.rcParams.update({'font.size':12,'axes.spines.right':False,'axes.spines.top':False})
fig,(plane,angle)=plt.subplots(1,2,figsize=(11.7,5.6),gridspec_kw={'width_ratios':[1,1.28]})
fig.subplots_adjust(left=.075,right=.975,top=.85,bottom=.14,wspace=.30)
fig.suptitle('Where the same clockwise turn takes the third zero',x=.075,ha='left',fontsize=18,weight='bold')
plane.axvline(.5,color='#8F9AA4',ls='--',lw=1)
angle.axhline(.5,color='#8F9AA4',ls='--',lw=1)
for i in range(3):
    pts=json.loads((here/f'sweep_{i+1}.json').read_bytes())['checkpoints']
    xy=[tuple(float(arb(row['zero'][k]).mid()) for k in ['real','imag']) for row in pts]
    x,t=zip(*xy)
    a=[90-180*float(Fraction(row['shift'])) for row in pts]
    color=colors[i]
    plane.plot(x,t,color=color,lw=2.3)
    angle.plot(a,x,color=color,lw=2.2,label=labels[i])
    for ax,xx,yy in [(plane,x,t),(angle,a,x)]:
        j=146
        ax.annotate('',xy=(xx[j+4],yy[j+4]),xytext=(xx[j-4],yy[j-4]),
                    arrowprops=dict(arrowstyle='-|>',color=color,mutation_scale=15,lw=1.6))
    plane.scatter([x[0],x[-1]],[t[0],t[-1]],s=32,color='white',edgecolors=color,zorder=4)
    if i==0:
        plane.annotate(r'$\rho_3$',xy=xy[0],xytext=(7,-2),textcoords='offset points')
    dest=[r'$\rho_4$',r'$8\pi i/\log 2$',r'$\rho_7$'][i]
    plane.annotate(dest,xy=xy[-1],xytext=((0,-18) if i==1 else (8,3)),textcoords='offset points',
                   bbox=dict(facecolor='white',edgecolor='none',pad=.4,alpha=.9))
plane.set(xlabel='Real part of moving zero',ylabel='Height on the Riemann scale',xlim=(-.33,1.05))
angle.set(xlabel='Angle during each sweep (degrees)',ylabel='Real part of moving zero',
          xlim=(60.05,44.95),xticks=[60,57,54,51,48,45],ylim=(-.25,1.03))
angle.legend(frameon=False,loc='upper left',ncol=3,fontsize=9.4,columnspacing=1.1,handlelength=1.4)
for ax in (plane,angle):
    ax.grid(axis='y',alpha=.16)
fig.savefig(here/'successor-paths.png',dpi=200)
plt.close(fig)
