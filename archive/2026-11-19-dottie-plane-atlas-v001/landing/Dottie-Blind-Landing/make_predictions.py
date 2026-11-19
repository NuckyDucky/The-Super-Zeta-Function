"""Extract a single past knot per case/cutoff into a fresh, isolated forecast subprocess."""
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
from hashlib import sha256
import json
import subprocess
import sys
from freeze_protocol import HERE,checked,seal

def observation(pkt):
    receipt=subprocess.run([sys.executable,"-B",str(HERE/"observe.py")],input=json.dumps(pkt),
                           text=True,capture_output=True)
    if receipt.returncode: raise RuntimeError(receipt.stderr)
    return json.loads(receipt.stdout)

def run():
    protocol=checked("protocol.json")
    for file,digest in protocol["forecast_code_sha256"].items():
        assert sha256((HERE/file).read_bytes()).hexdigest()==digest
    packets=[]
    archive_hashes={}
    for case,relpath in enumerate(protocol["archive_paths"],1):
        raw=(HERE.parent/relpath).read_bytes()
        archive_hashes[relpath]=sha256(raw).hexdigest()
        root=json.loads(raw)
        knots=(root.get("paths") or [root])[0]["checkpoints"]
        for label in protocol["cutoff_labels"]:
            h=protocol["trough_h_bounds"] if label=="trough" else [str(15-F(label))]*2
            b0=F(1,6)+F(h[0])/180
            # Read only each knot's parameter before deciding eligibility for its coordinate.
            allowed=[(F(k.get("shift") or k["b"]),i) for i,k in enumerate(knots)]
            past,idx=max(x for x in allowed if x[0]<=b0)
            point=knots[idx]["zero"]
            packets.append({"case":case,"cutoff":label,"h_bounds":h,"b_past":str(past),
                            "anchor":{"real":point["real"],"imag":point["imag"]}})
    with ThreadPoolExecutor(max_workers=2) as pool:
        cases=list(pool.map(observation,packets))
    return {"protocol_sha256":sha256((HERE/"protocol.json").read_bytes()).hexdigest(),
            "input_archive_hashes":archive_hashes,"cases":cases}

if __name__=="__main__":
    if not __debug__: raise RuntimeError("Enable assertions")
    print(seal("predictions.json",run()))
