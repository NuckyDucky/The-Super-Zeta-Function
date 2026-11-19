"""Revisit the original 37 unresolved displayed seeds by directed continuation."""
import argparse
from pathlib import Path
import json
import numpy as np
from flint import acb,arb,ctx
from plane_anchors import proof

HERE=Path(__file__).resolve().parent


def main(folder):
    ctx.prec,ctx.cap=192,3
    ref=json.loads((HERE/'plane_reference.json').read_bytes())
    h=arb(ref['trough']['alpha'])
    b=(arb(1)/6+h/180).union(arb(1/6+float(h.mid())/180))
    results=[]
    with np.load(HERE/'plane_map.npz',allow_pickle=False) as grid:
        rows,cols=np.nonzero(~grid['accepted'])
        for row,col in zip(rows,cols):
            x,y=float(grid['x'][col]),float(grid['y'][row])
            entry=proof(x,y,x,b)
            entry.update(row=int(row),column=int(col),
                         original_step_error=float(grid['node_error'][row,col]),
                         original_level_error=float(grid['level_error'][row,col]))
            assert not arb(entry['length']).contains(0)
            results.append(entry)
            print(len(results),x,y,entry['cells'],entry['length'],flush=True)
    assert len(results)==37
    summary=dict(precision_bits=192,coordinates='exact stored binary grid points',
                 compared_step_error=2e-5,compared_level_drift=5e-7,
                 step_failures=sum(p['original_step_error']>2e-5 for p in results),
                 drift_failures=sum(p['original_level_error']>=5e-7 for p in results),
                 total_tubes=sum(p['cells'] for p in results),entries=results,
                 two_adjacent_starts=adjacent_distances(results))
    (folder/'staircase.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')


def adjacent_distances(results):
    # Two adjacent marked cells in the same grid row. Keep the finite
    # separation across the two continuations distinct from the local scale
    # at either seed, which measures an infinitesimal displacement.
    ordered=[]
    for x in (-.2375,-.225):
        matches=[p for p in results if abs(p['start'][0]-x)<1e-12
                 and abs(p['start'][1]-36.7875)<1e-12]
        assert len(matches)==1
        ordered.append(matches[0])
    z=lambda coords:acb(*(arb(v) for v in coords))
    initial=abs(z(ordered[1]['start'])-z(ordered[0]['start']))
    final=abs(z(ordered[1]['end'])-z(ordered[0]['end']))
    assert final>arb('1.70') and all(arb(p['length'])<1 for p in ordered)
    return dict(row=ordered[0]['row'],columns=[p['column'] for p in ordered],
                initial_distance=initial.str(16),final_distance=final.str(16),
                distance_ratio=(final/initial).str(15),local_length_factors=[p['length'] for p in ordered])


if __name__=='__main__':
    if not __debug__: raise RuntimeError('Enable assertions')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE)
    main(parser.parse_args().output)
