"""Compile the Newton-tube theorem and audit its exported declarations.

Usage: python check_certificate_logic.py PATH_TO_REPOSITORY [--output FILE]
Requires the pinned repository's compiled lean/SuperZeta/Oriented/LiuConnection.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
NAMES = ('newton_lipschitz','reference_derivative_ne_zero','unique_reference_zero',
         'glue_at_endpoint','root_motion','branch_lipschitz','exists_lipschitz_branch')
ALLOWED = {'propext','Classical.choice','Quot.sound'}


def verify(repo):
    project = repo/'lean'
    lake = shutil.which('lake') or str(repo/'.lean-tools/lean-4.19.0-windows/bin/lake.exe')
    probe = 'import os,shutil,json; print(json.dumps([shutil.which("lean"),os.environ["LEAN_PATH"]]))'
    lean, search = json.loads(subprocess.check_output(
        [lake,'env',sys.executable,'-c',probe],cwd=project,text=True))
    with tempfile.TemporaryDirectory(prefix='dottie-tube-') as directory:
        scratch = Path(directory)
        lookups = [str((project/p).resolve()) for p in search.split(os.pathsep) if p]
        env = dict(os.environ,LEAN_PATH=os.pathsep.join([str(scratch),*lookups]))
        source = HERE/'CertificateLogic.lean'
        file = scratch/'CertificateLogic.olean'
        subprocess.run([lean,'-DwarningAsError=true','--root='+str(HERE),'-o',str(file),
                        str(source)],check=True,env=env)
        name_prefix = 'DottieOriented.CertificateLogic.'
        queries = ['import CertificateLogic',*[f'#print axioms {name_prefix}{n}' for n in NAMES]]
        audit = scratch/'Audit.lean'
        audit.write_text('\n'.join(queries)+'\n',encoding='utf8')
        result = subprocess.check_output([lean,'-DwarningAsError=true',str(audit)],
                                         text=True,env=env,encoding='utf8')
        axioms={}
        for n in NAMES:
            found = re.search(r"'"+re.escape(name_prefix+n)+r"' depends on axioms:\s*\[([^\]]*)\]",result)
            assert found is not None, result
            deps = sorted(x.strip() for x in found.group(1).split(',') if x.strip())
            assert set(deps)<=ALLOWED, (n,deps)
            axioms[n]=deps
    return dict(toolchain=subprocess.check_output([lean,'--version'],text=True).strip(),
                repository_revision=subprocess.check_output(['git','rev-parse','HEAD'],
                                                             cwd=repo,text=True).strip(),
                source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),axioms=axioms,
                numerical_assumptions='Bounds on reference derivatives, parameter variation and center residuals are supplied by external interval arithmetic.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repo',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    report=json.dumps(verify(args.repo.resolve()),indent=2)+'\n'
    if args.output:
        args.output.write_text(report,encoding='utf8')
    print(report)
