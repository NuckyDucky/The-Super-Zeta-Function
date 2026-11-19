"""Evaluate the sealed coordinate forecasts against independent FLINT ordinary zeta zeros."""
import json
from hashlib import sha256
from flint import acb,arb,ctx
from freeze_protocol import HERE,checked

def num(v):
    return acb(arb(v["real"]),arb(v["imag"]))

def fmt(v):
    return v.str(20)

def mean(values):
    return sum(values,arb(0))/len(values)

def median(values):
    # Sorted lower and upper bounds enclose the median even for overlaps.
    n=len(values)
    lo=sorted((x.lower() for x in values),key=float)
    hi=sorted((x.upper() for x in values),key=float)
    i,j=(n-1)//2,n//2
    return ((lo[i]+lo[j])/2).union((hi[i]+hi[j])/2)

def winner(a,b):
    if a<b: return True
    if a>b: return False
    raise ArithmeticError("overlapping comparison")

def run():
    ctx.prec=224
    protocol=checked("protocol.json")
    p=checked("predictions.json")
    assert p["protocol_sha256"]==sha256((HERE/"protocol.json").read_bytes()).hexdigest()
    targets=[acb.zeta_zero(i) for i in range(1,12)]
    scores={}
    details=[]
    methods=protocol["models"]
    thresholds=[arb(x) for x in protocol["thresholds"]]
    for row in p["cases"]:
        rank,label=row["case"],row["cutoff"]
        true=targets[rank-1]
        z=num(row["z"])
        measured=true.imag-z.imag
        out={"case":rank,"cutoff":label,"true_w":{"real":fmt(true.real),"imag":fmt(true.imag)},
             "observed_height_gain":fmt(measured),"methods":{}}
        for m in methods:
            est=num(row["forecast"][m])
            error=est-true
            complex_error=abs(error)
            herror=abs(error.imag)
            entry={"complex_error":fmt(complex_error),"height_error":fmt(error.imag),
                   "real_error":fmt(error.real),"predicted_height_gain":fmt(est.imag-z.imag)}
            if label=="trough":
                assert est.imag>0 and est.imag<targets[-1].imag
                dist=[abs(est-target) for target in targets]
                k=min(range(len(dist)),key=lambda i:float(dist[i].mid()))
                assert all(dist[k]<d for i,d in enumerate(dist) if i!=k)
                entry["nearest_positive_Riemann_ordinal"]=k+1
            predicted_gain=est.imag-z.imag
            if m=="constant" or (m=="linear" and rank==6 and label=="trough"):
                predicted_gain=arb(0)
            scores[rank,label,m]=complex_error,herror,measured,predicted_gain
            out["methods"][m]=entry
        details.append(out)
    cohorts={"all_ten":list(range(1,11)),"other_nine":[i for i in range(1,11) if i!=6],
             "historically_forward":protocol["forward_archive_cases"],"historically_backward":protocol["backward_archive_cases"]}
    # Descriptive split by the speed change at the arrival. It never enters
    # an individual forecast or a choice of a cutoff or a Taylor coefficient.
    previous=json.loads((HERE.parent/"Dottie-Fold-Arrival"/"arrival.json").read_bytes())
    changes={x["end_rank"]:arb(x["speed_change"]) for x in previous["cases"] if x["end_rank"]}
    assert all(not x.contains(0) for x in changes.values())
    cohorts["accelerating_at_arrival"]=[k for k in range(1,11) if changes[k]>0]
    cohorts["slowing_at_arrival"]=[k for k in range(1,11) if changes[k]<0]
    summaries={}
    for cohort,indices in cohorts.items():
        summaries[cohort]={}
        for label in protocol["cutoff_labels"]:
            metric={}
            for m in methods:
                c,h,actual_gain,predicted_gain=zip(*(scores[k,label,m] for k in indices))
                metric[m]={"mean_complex_error":fmt(mean(c)),"median_complex_error":fmt(median(c)),
                           "mean_absolute_height_error":fmt(mean(h)),"median_absolute_height_error":fmt(median(h)),
                           "mean_height_gain":fmt(mean(actual_gain)), "median_height_gain":fmt(median(actual_gain)),
                           "mean_predicted_height_gain":fmt(mean(predicted_gain)),
                           "median_predicted_height_gain":fmt(median(predicted_gain)),
                           "within_complex_error_thresholds":[sum(winner(y,x) for y in c) for x in thresholds]}
                if m!="constant":
                    metric[m]["beats_constant"]=sum(winner(scores[k,label,m][0],scores[k,label,"constant"][0]) for k in indices)
                if m=="quadratic":
                    metric[m]["beats_linear"]=sum(winner(scores[k,label,m][0],scores[k,label,"linear"][0]) for k in indices)
            summaries[cohort][label]=metric
    return {"protocol_sha256":p["protocol_sha256"],
            "sealed_predictions_sha256":sha256((HERE/"predictions.json").read_bytes()).hexdigest(),
            "thresholds":protocol["thresholds"],"num_cases":len(targets)-1,
            "cohort_members":cohorts,
            "arrival_sign_cohorts":"Descriptive labels from an earlier endpoint-jet study, accessed only by the scorer.",
            "summaries":summaries,"details":details}

if __name__=="__main__":
    if not __debug__: raise RuntimeError("Enable assertions")
    results=run()
    (HERE/"scores.json").write_text(json.dumps(results,indent=2)+"\n",encoding="utf-8")
