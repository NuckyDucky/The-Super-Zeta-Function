"""Post-score local length and angle changes for the two held-out level paths."""
import argparse
import hashlib
import json
from pathlib import Path
from flint import acb, acb_series, arb, ctx

def derivative(w,b):
    t=acb_series([w,1],2)
    return (t.zeta(b)+t.zeta(1-b))[1]

def report(path):
    ctx.prec,ctx.cap=224,3
    rows=[]
    for row in json.loads(path.read_bytes())["rows"]:
        k,index=row["k"],row["index"]
        z=acb(0,2*k*arb.pi()/arb(3).log())
        u=acb(0,2*index*arb.pi()/arb(2).log()) if row["true_type"]=="dyadic" else acb.zeta_zero(index)
        last=row["cutoff_position"]
        cutoff=acb(arb(last["re"]),arb(last["im"]))
        initial_slope=(acb(2)**z-1)*arb(3).log()*z.zeta()
        final_slope=(arb(2).log()*u.zeta() if row["true_type"]=="dyadic" else
                     (acb(4)**u-acb(2)**u)*acb_series([u,1],2).zeta()[1])
        assert initial_slope.overlaps(derivative(z,arb(1)/6))
        assert final_slope.overlaps(derivative(u,arb(1)/4))
        assert not final_slope.contains(0)
        item={"k":k}
        for label,slope in [("entire_turn",initial_slope),("last_eighth_degree",derivative(cutoff,arb(1)/6+arb(119)/(8*180)))]:
            relative=slope/final_slope
            item[label]={"length_factor":abs(relative).str(20),
                         "orientation_change_principal_degrees":(relative.arg()*180/arb.pi()).str(20)}
        rows.append(item)
    return {"scope":"post-scoring, unweighted symmetric Hurwitz level chart; principal rotation modulo 360 degrees",
            "precision_bits":ctx.prec,"score_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"rows":rows}

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dir",type=Path,default=Path(__file__).resolve().parent)
    directory=parser.parse_args().dir
    data=report(directory/"score.json")
    (directory/"local_scale.json").write_bytes((json.dumps(data,indent=2)+"\n").encode())
