"""Replay the masked landing studies from this checkout using temporary working files."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
MASK=Path("Dottie-Blind-Landing")
FOLD=Path("Dottie-Fold-Arrival")
FWD=Path("Dottie-Forward-From-Trough")
TEN=Path("Dottie-Turn-Geometry/ten")

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_bytes())

def copy_file(source,target):
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,target)

def checkout(explicit):
    if explicit: return explicit.resolve()
    for p in HERE.parents:
        if (p/"archive"/"2026-11-19-zero-transport-v001").is_dir():
            return p
    raise SystemExit("Pass --repo PATH_TO_THE_SUPER_ZETA_FUNCTION.")

def stage(work,repo):
    for rel,digest in read(HERE/"payload-sha256.json").items():
        if sha(HERE/rel)!=digest: raise ValueError("Published file changed: "+rel)
    for group in read(HERE/"dependencies.json").values():
        for entry in group["files"]:
            src=repo/entry["public"]
            if sha(src)!=entry["sha256"]:
                raise ValueError(f"Expected pinned contents of {entry['public']} at {group['commit']}")
            copy_file(src,work/entry["layout"])
    for sub in (MASK,FOLD,FWD,TEN):
        for script in (HERE/sub).glob("*.py"):
            copy_file(script,work/sub/script.name)
    for rel in [FWD/"protocol.json",TEN/"summary-6.json",*[TEN/f"backwards-{n}.json" for n in (8,9,10)]]:
        copy_file(HERE/rel,work/rel)

def saved(work,rel,exact=False):
    original,rerun=HERE/rel,work/rel
    ok=sha(original)==sha(rerun) if exact else read(original)==read(rerun)
    if not ok:
        raise ValueError(f"Replay differs from the published result: {rel}. Check the pinned FLINT version.")
    print(f"Verified {rel.as_posix()}",flush=True)

def execute(work,script,*args):
    # Run original files from an isolated working tree, with no user-supplied
    # import paths and no need for Git credentials or network access.
    env=dict(os.environ)
    env.pop("PYTHONPATH",None)
    env["PYTHONUTF8"]="1"
    cmd=[sys.executable,"-B",str(work/script),*map(str,args)]
    result=subprocess.run(cmd,cwd=work,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(result.stdout.decode("utf-8",errors="replace")[-6000:])

def replay(work,repo,options):
    stage(work,repo)
    if options.backward:
        for n in (8,9,10):
            execute(work,TEN/"trace.py",n)
            rel=TEN/f"backwards-{n}.json"
            saved(work,rel)
            # Input hashes belong to the originally preserved bytes, including
            # their line endings, on every OS.
            copy_file(HERE/rel,work/rel)
    execute(work,MASK/"freeze_protocol.py")
    saved(work,MASK/"protocol.json",exact=True)
    execute(work,MASK/"make_predictions.py")
    saved(work,MASK/"predictions.json",exact=True)
    execute(work,FOLD/"arrival.py")
    saved(work,FOLD/"arrival.json")
    execute(work,MASK/"score.py")
    saved(work,MASK/"scores.json")
    for operation,receipt in (("predict","predicted"),("certify","certified"),("score","scored")):
        execute(work,FWD/"forward.py",operation)
        saved(work,FWD/(receipt+".json"),exact=True)
    execute(work,FWD/"uniform_eighth.py")
    saved(work,FWD/"uniform_eighth.json")
    if options.geometry:
        for script,out in [(FOLD/"fold_shapes.py", "fold-shapes.json"),
                           (FOLD/"final_turn.py","final_turn.json"),
                           (FOLD/"residual_convexity.py","residual_convexity.json"),
                           (FWD/"horizon.py","horizon.json")]:
            execute(work,script)
            saved(work,script.parent/out)

if __name__=="__main__":
    if not __debug__: raise SystemExit("Assertions must be enabled.")
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo",type=Path,help="repository root, inferred within a full checkout")
    p.add_argument("--geometry",action="store_true",help="also reproduce the four folds, speed maximum, residual, and sixth forecast horizons")
    p.add_argument("--backward",action="store_true",help="also retrace the three historically backward-selected branches")
    args=p.parse_args()
    with tempfile.TemporaryDirectory(prefix="super-zeta-landings-") as tmp:
        replay(Path(tmp),checkout(args.repo),args)
