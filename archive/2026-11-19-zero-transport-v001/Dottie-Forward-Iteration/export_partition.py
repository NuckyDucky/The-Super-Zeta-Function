"""Generate Lean kernel checks of the rational mesh and rounded comparison bounds."""
from fractions import Fraction
from pathlib import Path
from flint import ctx, arb
from audit_forward import replay

here=Path(__file__).resolve().parent
ctx.prec,ctx.cap=320,3
code=['import Init','namespace ForwardMesh','abbrev Row := Nat × Nat × Nat',
      'def valid : Nat → Nat → List Row → Bool',
      '  | left, right, [] => left == right',
      '  | left, right, (a,b,q)::rows =>',
      '    (left == a) && (a < b) && (q < 1000000000) && valid b right rows',
      'set_option maxRecDepth 4096','set_option maxHeartbeats 2000000']
for sweep in (1,2,3):
    rows=[]
    previous=here.parent/'Dottie-Third-Zero'/'sweep_1.json' if sweep==1 else here/f'sweep_{sweep-1}.json'
    def collect(a,b,ratio):
        q=(ratio*arb(10**9)).upper().ceil().unique_fmpz()
        assert q is not None
        rows.append(((a-Fraction(1,6))*12,(b-Fraction(1,6))*12,int(q)))
    replay(previous,here/f'sweep_{sweep}.json',collect)
    denominator=max(t.denominator for a,b,q in rows for t in (a,b))
    # Each rational mesh point is dyadic in normalized sweep time.
    terms=[]
    for a,b,q in rows:
        l,r=a*denominator,b*denominator
        assert l.denominator==r.denominator==1
        terms.append(f'({int(l)},{int(r)},{q})')
    # Short definition blocks keep the proof portable across ordinary Lean stacks.
    groups=[]
    for i in range(0,len(terms),32):
        name=f's{sweep}part{i//32}'
        code.extend([f'def {name} : List Row := [',',\n'.join(terms[i:i+32])+']'])
        groups.append(name)
    name=f'sweep{sweep}'
    code.append(f'def {name} : List Row := '+' ++ '.join(groups))
    code.append(f'theorem {name}_size : {name}.length = {len(rows)} := by decide')
    code.append(f'theorem {name}_covers_with_strict_bounds : valid 0 {denominator} {name} = true := by decide')
    code.append(f'#print axioms {name}_covers_with_strict_bounds')
code.append('end ForwardMesh')
(here/'ForwardMesh.lean').write_text('\n'.join(code)+'\n',encoding='utf8')
