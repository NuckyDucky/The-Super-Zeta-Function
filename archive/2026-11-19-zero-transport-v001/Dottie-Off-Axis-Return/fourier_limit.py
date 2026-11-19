"""Check the first displacement of the escaping k=2 path with directed disks."""
import json
from pathlib import Path
from flint import acb, arb, ctx
from arithmetic_reference import reference, derivative_w, disk_check, complex_record

ctx.prec = 448
ctx.cap = 3
ln2 = arb(2).log()
rows = []
for power in (2,3,4,5):
    a = arb(1)/10**power
    h = 1-2*a*a
    b = a.acos()/(2*arb.pi())
    model = acb(1+(a/h).log()/ln2, 4*arb.pi()/ln2)
    center = (model+a/ln2).mid()
    for _ in range(6):
        center = (center-reference(center,b)/derivative_w(center,b)).mid()
    radius = arb('1e-35')
    q, residual, verified = disk_check(center,radius,b)
    assert verified
    assert abs(center-model)+radius < 8*a
    root = center+acb(arb(0,radius),arb(0,radius))
    scaled = (root-model)/a
    rows.append({'a':f'1e-{power}', 'root':complex_record(root),
                 'displacement_over_a':complex_record(scaled),'target':(1/ln2).str(32)})
out = json.dumps({'precision_bits':ctx.prec,'disk_radius':'1e-35','k':2,'rows':rows},indent=2)
Path(__file__).with_name('fourier_limit.json').write_text(out+'\n',encoding='utf8')
print(out)
