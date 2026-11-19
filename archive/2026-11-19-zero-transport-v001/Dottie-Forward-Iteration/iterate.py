"""Execute the frozen successor calls. Never request a zeta-zero ordinate."""
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent/'Dottie-Second-Zero'


def main():
    visited = {('Riemann', n) for n in (1,2,3)} | {('dyadic',2)}
    calls = []
    def save(status):
        log = dict(protocol_sha256=sha256((HERE/'protocol.txt').read_bytes()).hexdigest(),
                   status=status,calls=calls)
        (HERE/'results.json').write_text(json.dumps(log,indent=2)+'\n',encoding='utf8')
    sweep = 0
    for target in range(4,9):
        call = dict(start_ordinal=target-1,predicted_ordinal=target,sweeps=[])
        calls.append(call)
        for leg in range(1,7):
            sweep += 1
            sealed = HERE/f'sweep_{sweep}.json'
            subprocess.run([sys.executable,'-B',str(HERE/'follow.py'),str(sweep)],check=True)
            record=json.loads(sealed.read_bytes())
            row=dict(number=sweep,path=sealed.name,sha256=sha256(sealed.read_bytes()).hexdigest(),status=record['status'])
            call['sweeps'].append(row)
            if record['status'] != 'certified finite endpoint':
                save(record['status'])
                return
            identified=HERE/f'identification_{sweep}.json'
            subprocess.run([sys.executable,'-B',str(PREVIOUS/'classify.py'),str(sealed),'--out',str(identified)],check=True)
            result=json.loads(identified.read_bytes())
            address=(('Riemann',result['ordinal']) if result['type']=='Riemann zero'
                     else ('dyadic',result['index']))
            row['address']=address
            print('SCORED',sweep,target,address,flush=True)
            if address in visited:
                save('repeated address')
                return
            visited.add(address)
            if address[0]=='Riemann':
                if address[1]!=target:
                    save('out-of-order Riemann endpoint')
                    return
                call.update(result='hit',direct=(leg==1))
                save('continuing')
                break
            save('continuing')
        else:
            save('six-sweep limit reached')
            return
    save('all five prospective calls hit')

if __name__=='__main__':
    main()
