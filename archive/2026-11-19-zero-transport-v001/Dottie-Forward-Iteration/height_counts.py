"""Post-test: count by height at the identified elementary intermediate address."""
from flint import arb,ctx
from pathlib import Path
import json

here=Path(__file__).resolve().parent
report=json.loads((here/'identification_2.json').read_bytes())
assert report['type']=='Euler factor' and report['index']==4
ctx.prec=320
t=8*arb.pi()/arb(2).log()
lo,hi=t.mid()-arb('1e-8'),t.mid()+arb('1e-8')
assert lo<t and t<hi
counts=[n.zeta_nzeros().unique_fmpz() for n in (lo,hi)]
assert None not in counts and counts[0]==counts[1]
result=dict(height=t.str(32),lower=lo.str(22),upper=hi.str(22),counts=list(map(int,counts)))
(here/'height_counts.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
print(result)
