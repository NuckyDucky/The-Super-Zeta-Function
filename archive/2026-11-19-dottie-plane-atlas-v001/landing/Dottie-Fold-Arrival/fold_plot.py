"""Plot the certified local folds and the two rescaled descending arcs."""
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
from matplotlib import pyplot as plt
from flint import arb


HERE=Path(__file__).resolve().parent


def draw():
    d=json.loads((HERE/'fold-shapes.json').read_bytes())
    background='#fcfbf8'
    ink='#1c323c'
    colors=('#126a70','#a4422b')
    fig,(local,arcs)=plt.subplots(1,2,figsize=(10.3,4.9),layout=None,facecolor=background)
    fig.subplots_adjust(left=.073,right=.975,bottom=.22,top=.80,wspace=.28)
    fig.text(.073,.93,'The four folds on the path to the sixth zero',weight='bold',fontsize=18,color=ink)
    for ax in (local,arcs):
        ax.set_facecolor(background)
        ax.spines[['top','right']].set_visible(False)
        ax.grid(axis='y',color='#e3e3de',lw=.7)
        ax.set_axisbelow(True)
        ax.tick_params(colors=ink,labelsize=9)
    for j,fold in enumerate(d['folds']):
        x,y=zip(*fold['local_plot'])
        local.plot(x,y,color=colors[j//2],ls=('-' if j%2==0 else '--'),lw=1.8,label=fold['name'])
    x=[k*.005 for k in range(-20,21)]
    local.plot(x,[(k/.1)**2 for k in x],color='#42484b',ls=':',lw=1.5,label='Quadratic')
    local.set_title('At each turning point',loc='left',fontsize=13,color=ink)
    local.set(xlabel='Clockwise angle from the fold (degrees)',ylabel='Normalized height change',xlim=(-.102,.102),ylim=(-.03,1.50))
    local.set_xticks([-.1,-.05,0,.05,.1])
    local.legend(frameon=False,ncol=2,loc='upper center',fontsize=8,handlelength=1.5,columnspacing=1)
    for i,(arc,name) in enumerate(zip(d['descending_arcs'],('Lower hump','Upper hump'))):
        x=[0]+[row['u'] for row in arc['samples']]+[1]
        y=[1]+[float(arb(row['profile']).mid()) for row in arc['samples']]+[0]
        # Plot fraction of the total fall, beginning at zero.
        y=[1-p for p in y]
        arcs.plot(x,y,color=colors[i],lw=2.4,label=name)
        arcs.scatter([.5],[y[50]],color=colors[i],edgecolors='white',s=34,zorder=5)
        arcs.annotate(f'{100*y[50]:.1f}%',(.5,y[50]),xytext=((7,-14) if i==0 else (-7,10)),
                      textcoords='offset points',fontsize=9,color=colors[i],
                      ha='left' if i==0 else 'right',weight='bold')
    arcs.axvline(.5,color='#a9b5b2',lw=.9,ls=':',zorder=0)
    arcs.set_title('From crest to trough',loc='left',fontsize=13,color=ink)
    arcs.set(xlabel='Fraction of the turn from crest to trough',ylabel='Fraction of total height fallen',xlim=(0,1),ylim=(-.035,1.035))
    arcs.legend(frameon=False,loc='upper left',fontsize=9)
    fig.text(.073,.085,'Left: all four folds are centered and divided by their own quadratic height change at 0.10°.',
             fontsize=9,color='#465a61')
    fig.text(.073,.041,'Right: each complete descent is scaled to the same width and height. Dots mark halfway in angle.',
             fontsize=9,color='#465a61')
    fig.savefig(HERE/'fold-shapes.png',dpi=170,facecolor=background)
    plt.close(fig)


if __name__=='__main__':draw()
