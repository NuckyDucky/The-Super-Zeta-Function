"""Rebuild and compare the eleven plotted series and three critical-line markers.

Run python -B replay.py from any working directory after installing python-flint
0.9.0. The default compares with order-of-the-turns.html at the archive root.
Use --html PATH for the inline fragment or its standalone export, and --out
PATH to write the reconstructed display values to JSON.
"""
from argparse import ArgumentParser
from fractions import Fraction
from html import unescape
import json
from pathlib import Path
import re
import sys

from flint import acb, arb, ctx

ROOT = Path(__file__).resolve().parents[2]
OLD = "Dottie-Off-Axis-Return"
SECOND = "Dottie-Second-Zero"
FORWARD = "Dottie-Forward-Iteration"
REVERSE = "Dottie-Transport-Reversibility"
SOURCES = {
    "triadicFirst": f"{OLD}/arithmetic_braid_lattice.json",
    "firstOut": f"{OLD}/arithmetic_braid_riemann.json",
    "bridgeSecond": f"{SECOND}/dyadic_continuation.json",
    "secondOut": "Dottie-Third-Zero/sweep_1.json",
    "thirdOut": f"{FORWARD}/sweep_1.json",
    "fourthOut": f"{FORWARD}/sweep_2.json",
    "bridgeOut": f"{FORWARD}/sweep_3.json",
    "triadicControl": f"{SECOND}/triadic_endpoint.json",
    "triadicEscape": f"{OLD}/arithmetic_escape_match.json",
    "found5": f"{REVERSE}/rho5-replay.json",
    "found6": f"{REVERSE}/rho6-replay.json",
}
sys.path.insert(0, str(ROOT / OLD))
from arithmetic_holdout_replay import centered_tube


def row(b, z):
    theta = float(90 - 180*b)
    return [round(theta, 9), round(float(z.real.mid()), 9), round(float(z.imag.mid()), 9)]


def generate():
    ctx.prec, ctx.cap = 256, 3
    legs = {}
    inserted = 0
    for key, source in SOURCES.items():
        record = json.loads((ROOT/source).read_bytes())
        checkpoints = (record.get("paths") or [record])[0]["checkpoints"]
        pts = []
        for idx, checkpoint in enumerate(checkpoints):
            b = Fraction(checkpoint.get("shift") or checkpoint["b"])
            box = checkpoint["zero"]
            z = acb(arb(box["real"]), arb(box["imag"]))
            pts.append(row(b,z))
            if key != "fourthOut" or not (101 <= idx < 107 or 212 <= idx < 222):
                continue
            next_b = Fraction(checkpoints[idx+1]["shift"])
            node, radius = z.mid(), arb("1e-15")
            assert abs(z-node) < radius
            for j in range(1,16):
                a = b+(next_b-b)*Fraction(j-1,16)
                end = b+(next_b-b)*Fraction(j,16)
                proof = centered_tube(node, radius, a, end)
                assert proof is not None
                node = proof[0]
                pts.append(row(end,node))
                inserted += 1
        legs[key] = pts
    assert inserted == 240
    crossings = json.loads((ROOT/REVERSE/"blue-crossings.json").read_bytes())["interior_crossings"]
    contacts = []
    for crossing in crossings:
        a,t,z = [float(arb(crossing[k]).mid()) for k in ("angle","height","abs_riemann_zeta")]
        contacts.append({"a":a, "t":t, "z":z})
        legs["fourthOut"].append([a,0.5,t])
    legs["fourthOut"].sort(reverse=True)
    return {"series": legs, "crossings": contacts}


def read_display(path):
    s=path.read_text(encoding="utf8")
    anchor='<script type="application/json" id="turn-data">'
    if anchor not in s:
        s=unescape(s)
    series=json.loads(s.split(anchor,1)[1].split("</script>",1)[0])
    contacts=json.loads(re.search(r"contacts=(\[.*?\]);",s).group(1))
    return {"series":series,"crossings":contacts}


if __name__ == "__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--html",type=Path,default=ROOT/"order-of-the-turns.html")
    parser.add_argument("--out",type=Path)
    args=parser.parse_args()
    rebuilt=generate()
    assert rebuilt==read_display(args.html)
    if args.out:
        args.out.write_text(json.dumps(rebuilt,separators=(",",":"))+"\n",encoding="utf8")
    print(f"Matched {len(rebuilt['series'])} series, "
          f"{sum(map(len,rebuilt['series'].values()))} plotted locations and "
          f"{len(rebuilt['crossings'])} certified interior crossings.")
