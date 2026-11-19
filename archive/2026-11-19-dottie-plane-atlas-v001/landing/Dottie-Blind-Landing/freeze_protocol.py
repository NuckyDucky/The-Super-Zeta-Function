"""Write the local pre-score protocol and its SHA-256 seal. Python 3.12."""
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
FILES=["Dottie-Off-Axis-Return/arithmetic_braid_lattice.json",
       "Dottie-Second-Zero/dyadic_continuation.json","Dottie-Third-Zero/sweep_1.json",
       "Dottie-Forward-Iteration/sweep_1.json","Dottie-Transport-Reversibility/rho5-replay.json",
       "Dottie-Transport-Reversibility/rho6-replay.json","Dottie-Forward-Iteration/sweep_3.json",
       *[f"Dottie-Turn-Geometry/ten/backwards-{k}.json" for k in [8,9,10]]]

def seal(name,record):
    data=(json.dumps(record, ensure_ascii=True, indent=2)+"\n").encode()
    digest=sha256(data).hexdigest()
    path=HERE/name
    if path.exists():
        if path.read_bytes()!=data:
            raise RuntimeError(f"{name} already exists with different content; preserve the sealed run")
    else:
        with path.open("xb") as stream:
            stream.write(data)
    side=HERE/(name+".sha256")
    line=digest+"  "+name+"\n"
    if side.exists():
        assert side.read_text()==line
    else:
        with side.open("x",encoding="ascii") as stream:
            stream.write(line)
    return digest

def checked(name):
    data=(HERE/name).read_bytes()
    assert sha256(data).hexdigest()==(HERE/(name+".sha256")).read_text().split()[0]
    return json.loads(data)

if __name__=="__main__":
    protocol={"study":"one endpoint-masked Taylor extrapolation, historical target-selected archive",
              "cases":list(range(1,11)),"archive_paths":FILES,"forward_archive_cases":list(range(1,8)),
              "backward_archive_cases":[8,9,10],
              "h":"clockwise degrees, b=1/6+h/180, end h=15","cutoff_labels":["trough","1","1/2","1/4","1/8","1/16"],
              "trough_h_bounds":["13.40917360918594367527","13.40917360918594367533"],
              "trough_source":"sixth-passes-v001, jets.json: minimum alpha only. Exact last minimum for sixth landing. Same time for every other track.",
              "models":["constant","linear","quadratic"],"forecast_formula":"z, z+D*v, z+D*v+D^2*a/2, D=15-h",
              "targets":"full complex endpoint, signed height gain; forecast must not set real part to 1/2; thresholds strict 0.1, 0.01, 0.001 on complex distance",
              "thresholds":["0.1","0.01","0.001"],
              "comparison":"unweighted arithmetic mean and standard median of complex and absolute height errors, per-method threshold counts and paired wins at each cutoff. All ten, nine excluding the focal sixth, historical forward seven and backward three. Report sixth separately with signed height gains. At the shared trough classify each frozen forecast by nearest positive-height Riemann zero after scoring, including unchanged-position baseline.",
              "leakage_control":"Extraction sees the frozen archive. Only the nearest marked past checkpoint, parameter interval, opaque ordinal, and cutoff name enter the numerical observation subprocess. It refines the zero in the symmetric Hurwitz family, continues only to the left bound of the cutoff, and encloses local derivatives on the cutoff. No endpoint, arithmetic zero rank lookup, endpoint geometry, future checkpoints, or fitting. The scorer alone uses independent ordinary zeta zeros. Historical endpoint-based inclusion and backward-traced paths 8-10 are disclosed.",
              "verification":"192-bit directed Hurwitz jets and endpoint distances; distinguish endpoint error from input uncertainty and forecast error",
              "forecast_code_sha256":{f:sha256((HERE/f).read_bytes()).hexdigest() for f in ("observe.py","make_predictions.py")}}
    print(seal("protocol.json",protocol))
