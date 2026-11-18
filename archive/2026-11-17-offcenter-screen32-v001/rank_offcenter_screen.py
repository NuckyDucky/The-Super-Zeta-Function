"""Select windows from a frozen complex forecast before opening the contour verifier.

Send every window with a predicted right-of-line root to the verifier. Also
send the window with the smallest positive spacing of adjacent predicted line
heights; resolve ties by level, then lower height. Record the original input
hash, using the unmodified forecast rows as the verifier's input. The spacing
rank focuses checks near projected collisions. It implies no bifurcation.
"""
import argparse
import hashlib
import json
from pathlib import Path


def rank(rows):
    positive=[]
    gaps=[]
    for row in rows:
        if any(r["beta"]>.5 for r in row["predicted_roots"]):
            positive.append(row["level"])
        heights=sorted(r["height_offset"] for r in row["predicted_roots"] if r["beta"]==.5)
        gaps.extend((y-x,row["level"],x,y) for x,y in zip(heights,heights[1:]) if y>x)
    selected=set(positive)
    nearest=None
    if gaps:
        gap,n,x,y=min(gaps)
        selected.add(n)
        nearest={"level":n,"predicted_line_offsets":[x,y],"gap":gap,"signed_square":-(gap/2)**2}
    return sorted(selected),positive,nearest


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("frozen_forecast",type=Path)
    parser.add_argument("selected_forecast",type=Path)
    args=parser.parse_args()
    raw=args.frozen_forecast.read_bytes()
    data=json.loads(raw)
    rows=data["levels"]
    ids,positive,nearest=rank(rows)
    data["levels"]=[r for r in rows if r["level"] in ids]
    data["selection"]={"batch_sha256":hashlib.sha256(raw).hexdigest(),"screened":len(rows),
                       "forecast_root_count":sum(len(r["predicted_roots"]) for r in rows),
                       "positive_split_levels":positive,"smallest_gap":nearest}
    with args.selected_forecast.open("x",encoding="utf-8",newline="\n") as out:
        out.write(json.dumps(data,indent=2)+"\n")
    print(json.dumps(data["selection"],indent=2))
