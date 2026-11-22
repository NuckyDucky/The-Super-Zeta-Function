"""Recover the fixed pair behind the growing quartet term and check both stage signs."""
from importlib import import_module
from pathlib import Path
import json
from flint import acb, ctx

ctx.prec = 320
u = import_module("reflected-modulus-contrast").first_root()
i = acb(0, 1)


def contains_equality(x, y):
    gap = x - y
    assert gap.contains(0) and abs(gap) < acb("1e-58").real


def recover(root, sign):
    U = sign * i * (-i * root).exp()
    V = 1 / U
    P, Q = U.exp(), V.exp()
    L = U / Q
    contains_equality(root, sign * root.cos())
    contains_equality(L * Q, U)
    contains_equality(-L * P, V)
    contains_equality((L * Q).exp(), P)
    contains_equality((-L * P).exp(), Q)
    contains_equality((U - V) / (2 * i), root)
    contains_equality(Q / P, (V - U).exp())
    return U, V, P, Q, L


U, V, P, Q, L = recover(u, -1)
Us, Vs, Ps, Qs, Ls = recover(-u, 1)
for x, y in ((Us, V), (Vs, U), (Ps, Q), (Qs, P), (Ls, -L)):
    contains_equality(x, y)
contains_equality((u*u).log(), 2*u.log())
assert not (P-Q).contains(0)
result = dict(cosine_sign=-1, upper_root=u.str(24), squared_root=(u*u).str(24),
              positive_exponent_U=U.str(24), negative_exponent_V=V.str(24),
              output_P=P.str(24), output_Q=Q.str(24), logarithmic_lift_L=L.str(24),
              negative_over_positive_output=(Q/P).str(24),
              checks="Both signed fixed pairs; (U,V,P,Q,L) goes to (V,U,Q,P,-L).")
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf8")
print(json.dumps(result, indent=2))
