"""Build a self-contained start-to-landing explorer from the saved complex grid."""
import argparse
import base64
import json
from pathlib import Path

import numpy as np
from flint import arb


HERE = Path(__file__).resolve().parent


def float_block(values):
    return base64.b64encode(np.asarray(values, dtype="<f8").tobytes(order="C")).decode("ascii")


def data_payload(folder):
    with np.load(folder / "plane_map.npz") as grid:
        x, y = grid["x"], grid["y"]
        accepted = grid["accepted"].copy()
        end = grid["end"].copy()
        scale = 2**grid["log2_length"]
    rows = json.loads((folder / "staircase.json").read_bytes())["entries"]
    anchors = json.loads((folder / "plane_anchors.json").read_bytes())["certificates"]
    restored = []
    examples = []
    for k, row in enumerate([*rows, *anchors]):
        x0, y0 = (float(v) for v in row["start"])
        i, j = np.argmin(abs(x-x0)), np.argmin(abs(y-y0))
        assert abs(x[i]-x0) < 1e-14 and abs(y[j]-y0) < 1e-14
        index = int(j*len(x) + i)
        if k < len(rows):
            assert [int(j), int(i)] == [row["row"],row["column"]] and not accepted[j, i]
            restored.append(index)
        else:
            assert accepted[j, i]
            examples.append(index)
        end[j, i] = complex(*(float(arb(v).mid()) for v in row["end"]))
        scale[j, i] = float(arb(row["length"]).mid())
    assert sorted(restored) == np.flatnonzero(~accepted).tolist()
    assert len(examples) == 2 and end.size == 10961 and len(restored)==37
    assert np.all(np.isfinite(end)) and np.all(np.isfinite(scale) & (scale>0))
    assert np.all((end.real>-.85)&(end.real<1.15)&(end.imag>36.1)&(end.imag<38.8))
    return dict(x=float_block(x), y=float_block(y), re=float_block(end.real),
                im=float_block(end.imag), scale=float_block(scale), restored=restored, examples=examples)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data",type=Path,default=HERE,help="Directory containing the atlas NPZ and the two certificates.")
    parser.add_argument("--output",type=Path,default=HERE/"complex_explorer.html")
    args=parser.parse_args()
    template=(HERE/"complex_explorer.template.html").read_text(encoding="utf-8")
    token="__GRID_PAYLOAD__"
    assert template.count(token)==1
    payload=json.dumps(data_payload(args.data), separators=(",",":"))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(template.replace(token,payload).encode("utf-8"))
    print(f"{args.output.name}: {args.output.stat().st_size:,} bytes, 10,961 paired complex points")


if __name__=="__main__":
    main()
