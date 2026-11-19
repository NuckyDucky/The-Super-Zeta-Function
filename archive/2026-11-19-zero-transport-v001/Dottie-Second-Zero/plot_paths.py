"""Plot the original reference paths and the two frozen seed tests."""
import json
from fractions import Fraction
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from flint import arb

here=Path(__file__).resolve().parent
old=here.parent/'Dottie-Off-Axis-Return'
def load(path):
    data=json.loads(path.read_text())
    rows=(data.get('paths') or [data])[0]['checkpoints']
    def mid(value): return float(arb(value).mid())
    return [(90-180*float(Fraction(p.get('b') or p['shift'])),mid(p['zero']['real']),mid(p['zero']['imag'])) for p in rows]
paths=[load(old/'arithmetic_braid_lattice.json'), load(old/'arithmetic_braid_riemann.json'),
       load(here/'dyadic_continuation.json'), load(here/'triadic_endpoint.json'),
       load(old/'arithmetic_escape_match.json')]
colors=['#14796f','#89587c','#234f97','#b36624','#983b3a']
fig,(left,right)=plt.subplots(1,2,figsize=(12.1,6),layout='constrained',width_ratios=(1,1.12))
for axis in (left,right):
    axis.spines[['top','right']].set_visible(False)
    axis.tick_params(color='#849098',labelcolor='#2e3742')
    axis.grid(axis='y',color='#e2e5e7',linewidth=0.8)
left.set_title("Three turns, one chain",loc='left',weight='bold',fontsize=14,pad=12)
left.axvline(.5,color='#74818b',ls='--',lw=1)
for idx in range(3):
    series=paths[idx]
    left.plot([p[1] for p in series],[p[2] for p in series],lw=2.7,c=colors[idx])
    for j in (76,184):
        left.annotate('',xy=series[j+5][1:],xytext=series[j-5][1:],
                      arrowprops=dict(arrowstyle='-|>',color=colors[idx],mutation_scale=14,lw=2))
    left.scatter([series[0][1],series[-1][1]],[series[0][2],series[-1][2]],s=36,
                 color='white', edgecolor=colors[idx],linewidth=1.5,zorder=5)
left.annotate(r'$4\pi i/\log 3$',xy=paths[0][0][1:],xytext=(10,-2),textcoords='offset points',va='center')
left.annotate(r'$\rho_1$',xy=paths[0][-1][1:],xytext=(-18,-1),textcoords='offset points',va='center',fontsize=13)
left.annotate(r'$4\pi i/\log 2$',xy=paths[1][-1][1:],xytext=(-2,12),textcoords='offset points',va='center')
left.annotate(r'$\rho_2$',xy=paths[2][-1][1:],xytext=(8,0),textcoords='offset points',va='center',fontsize=13)
left.set(xlim=(-.055,.63),ylim=(10.85,21.7),xlabel=r'Real part of $w$',ylabel=r'Imaginary part of $w$')
right.set_title("Same clockwise turn, different destinations",loc='left',weight='bold',fontsize=14,pad=12)
right.axhline(.5,color='#74818b',ls='--',lw=1,zorder=1)
right.axhline(0,color='#c2c9cf',lw=1,zorder=1)
for idx in (0,2,3,4):
    series=paths[idx]
    lbl=[r'$4\pi i/\log 3$ → first zero','',r'$4\pi i/\log 2$ → second zero',
         r'$8\pi i/\log 3$ → factor zero',r'$6\pi i/\log 3$ → escapes'][idx]
    right.plot([p[0] for p in series],[p[1] for p in series],color=colors[idx],lw=2.25,label=lbl,zorder=3)
right.annotate('continues to −∞',xy=paths[4][-1][:2],xytext=(-18,9),textcoords='offset points',ha='right',color=colors[4],fontsize=10)
right.set(xlim=(60.25,44.75),ylim=(-3.48,.82),xlabel='Native return angle (degrees)',ylabel=r'Real part of the moving zero')
right.set_xticks([60,57,54,51,48,45])
right.legend(loc='lower left',frameon=True,facecolor='white',edgecolor='none',fontsize=9.2,framealpha=1)
fig.savefig(here/'seed-paths.png',dpi=195,bbox_inches='tight',facecolor='white')
