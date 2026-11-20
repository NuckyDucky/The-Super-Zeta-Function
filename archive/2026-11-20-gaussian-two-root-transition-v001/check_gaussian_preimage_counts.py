"""Argument principle for nonzero targets excluded from both contour gaps.

Each output record covers a *disk* of target values. No interpolation
or inferred sign for the missing Gaussian zero contour is needed.
"""
from pathlib import Path
import json
from flint import acb, arb, ctx


def main():
    ctx.prec = 160
    root = Path(__file__).parent
    arcs = json.loads((root/"gaussian-loop-arcs.json").read_text())
    bound = json.loads((root/"gaussian-strip-image.json").read_text())
    gap_radius = arb(bound["uniform_image_bounds"][0]["radius_upper"]).upper()
    edges = [arcs["edges"][name] for name in ("bottom","right","top")]
    pt = lambda p: acb(p["x"],p["y"])
    right_nodes = [pt(p) for e in edges for p in e["nodes"]]
    nodes = right_nodes + [p.conjugate() for p in reversed(right_nodes)] + right_nodes[:1]
    right_disks = [(pt(p),arb(p["r"])) for e in edges for p in e["segments"]]
    disks = right_disks + [(p.conjugate(),r) for p,r in right_disks]
    assert all(abs(p) < gap_radius for p in (right_nodes[0], right_nodes[-1]))
    # Target disk centers and certified uniform target radii, all decimal rationals.
    targets = [("0.5","0","0.3"),("0","0.91","0.01"),("1.2","0","0.2"),
               ("6e-16","0","2e-17"),("-6e-16","0","2e-17")]
    results = []
    for x,y,radius in targets:
        a = acb(arb(x),arb(y))
        # Covers the closed input-boundary image plus straight chords where the
        # unresolved passages join their conjugates (all inside the gap disk).
        clearance = min([(abs(a)-gap_radius).lower()]
                        + [(abs(a-p)-r).lower() for p,r in disks])
        assert clearance > arb(radius)
        arg = sum(((q-a)/(p-a)).arg() for p,q in zip(nodes,nodes[1:]))
        turns = arg/(2*arb.pi())
        count = turns.unique_fmpz()
        assert count is not None and count >= 0
        results.append(dict(target_center_re=x,target_center_im=y,target_radius=radius,
                            verified_clearance_lower=str(clearance),
                            preimages_with_multiplicity=int(count)))
    out = dict(precision_bits=ctx.prec,input_real_bounds=[-1,2],
               height_offsets=["-1/16","1/16"],target_units=arcs["normalized_output"],
               target_origin_count=None, regions=results)
    (root/"gaussian-preimage-counts.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf8")
    print(json.dumps(results,indent=2))


if __name__=="__main__":
    main()
