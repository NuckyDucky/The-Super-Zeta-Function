# 32-level Super Zeta screen and one directed count

Research date 17 November 2026. This deposit uses the scripts and window geometry from the [three-window off-center experiment](../2026-11-17-offcenter-superzeta-v001/README.md), preserved at tag `offcenter-superzeta-v001`. [Provenance](provenance.json) records both script hashes and the five new source hashes.

## Frozen screen and selection

The finite predictor scanned levels 954985468720 through 954985468751 and returned 32 roots in the broad windows. All 32 predicted roots were on the model's critical line. The screen therefore supplied zero positive split forecasts. [Complete forecast](offcenter-superzeta-batch32.json)

The selection rule carries all windows with a right-of-line predicted root into a directed check and also carries the window with the smallest adjacent predicted line gap, with ties settled by level and lower height. Here it selected level 954985468722, whose closest forecast pair had gap $0.10051111818699052$. The input row and source forecast hash were frozen before the contour check. [Ranking script](rank_offcenter_screen.py) · [Selected input](offcenter-superzeta-selected32.json)

## Directed result at level 954985468722

The 192-bit directed contour check counted two reconstructed superzeta zeros in the broad window. Two disjoint Hardy sign brackets account for both zeros on the critical line. The reconstructed response had zero roots in the right off-center window, and the cosine determinant had one there. The remaining 31 windows are finite forecasts. [Directed certificate](offcenter-superzeta-checked32.json)

The signed pair predictor gives $q=-0.002525621219799794$. The disjoint brackets yield the exact interval
$
-\frac{181990217640625}{72057594037927936}\le q\le-\frac{181990163679129}{72057594037927936}.
$
Its outward-rounded decimal endpoints are $-0.002525621624$ and $-0.002525620874$. The two certified zeros have distinct heights. [Signed forecast](offcenter-superzeta-signed32.json)

## Replay

Use Python 3.12 and the [dependency versions](../2026-11-17-offcenter-superzeta-v001/requirements.txt) pinned with the earlier snapshot. Copy its two Python files and this deposit's five research files to a new scratch directory. Run the commands below in that directory. The rank, signed and contour replays read the frozen inputs, preserving the exact input hashes. Output names must be new.

```text
python -B offcenter_superzeta.py predict batch32-replay.json --first 954985468720 --levels 32
python -B rank_offcenter_screen.py offcenter-superzeta-batch32.json selected32-replay.json
python -B signed_superzeta_split.py predict offcenter-superzeta-selected32.json signed32-replay.json
python -B offcenter_superzeta.py check offcenter-superzeta-selected32.json checked32-replay.json
python -B signed_superzeta_split.py check offcenter-superzeta-signed32.json checked32-replay.json
```
