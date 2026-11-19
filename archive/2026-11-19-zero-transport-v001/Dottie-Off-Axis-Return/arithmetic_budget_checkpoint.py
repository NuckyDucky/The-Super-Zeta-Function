"""Recover the last certified disk of the original k=3 budgeted run.

The original verifier printed 22,699 accepted segments after cell 64/256.
Re-evaluate that anchor and rerun only the portion up to the fixed budget.
The independent complete replay supplies a matching anchor at the same b.
"""
import sys
from fractions import Fraction
import json
from pathlib import Path

from flint import acb,arb,ctx
from arithmetic_braid import ball,shrink_root,tube,complex_record

ctx.prec=224
ctx.cap=3
rad=arb('1e-14')
b0,b1=Fraction(1,6),Fraction(1,4)
cell_size=(b1-b0)/256
node=acb(0,6*arb.pi()/arb(3).log()).mid()
for cell in range(1,65):
    node=shrink_root(node,ball(b0+cell_size*cell),5)
anchor=node
accepted=22699
for cell in range(64,256):
    start=b0+cell_size*cell
    todo=[(start,start+cell_size)]
    while todo:
        left,right=todo.pop()
        out=tube(node,rad,left,right)
        if out is None:
            mid=(left+right)/2
            todo.extend(((mid,right),(left,mid)))
            continue
        node=out[0]
        accepted+=1
        if accepted==30000:
            box=node+acb(arb(0,rad),arb(0,rad))
            record={'precision_bits':224,'source':'original k=3 trial; suffix rerun from cell 64',
                    'starting_cell_number':64,'starting_accepted_count':22699,
                    'starting_center':complex_record(anchor),'parameter_b':str(right),
                    'theta_degrees':str((Fraction(1,2)-right)*180),
                    'theta_degrees_approx':float((Fraction(1,2)-right)*180),
                    'last_certified_disk':complex_record(box),'accepted_segments':accepted}
            print(json.dumps(record,indent=2))
            Path(sys.argv[1]).write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
            sys.exit()
raise ArithmeticError('budget never reached')
