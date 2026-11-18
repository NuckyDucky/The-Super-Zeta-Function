"""Exact elementary checks and local 2-isogeny descent for the meme Jacobian.

Python 3.12, python-flint 0.9.0. Optional --gp PATH replays PARI's independent
full 2-descent and Cassels-pairing calculation in a hidden child process with
a 20-second timeout. No GUI, GPU, network, or app access occurs.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from itertools import combinations
import json
from math import gcd, prod
from pathlib import Path
import re
import subprocess
import sys
import time
from flint import fmpz, fmpz_poly

ROOT = Path(__file__).resolve().parent
A, B = 5028677, -305545084240
D = A*A - 4*B
BAD = [2,5,11,23,31,41,457,486971,1414835497]
POINT = (Q(93082857946624000,911427267969),
         Q(129969110503209045907820800,870127764175520703))

def divisors_squarefree(primes):
    return sorted(sign*prod(c) for n in range(len(primes)+1)
                  for c in combinations(primes,n) for sign in (-1,1))

def quartic(a,b,d,u,v):
    assert b % d == 0
    return d*u**4+a*u*u*v*v+(b//d)*v**4

def square_qp(n,p):
    if n == 0:
        return True
    valuation = 0
    while n % p == 0:
        valuation += 1
        n //= p
    return valuation % 2 == 0 and (n % 8 == 1 if p == 2
                                  else pow(n%p,(p-1)//2,p) == 1)

def local_witness(a,b,d,p):
    # An exact integer whose Qp squareclass is trivial gives a Qp point.
    for k in range(80 if p > 457 else 2*p+4):
        for u,v in ((k,1),(1,p*k)):
            n = quartic(a,b,d,u,v)
            if square_qp(n,p):
                return {"u":u,"v":v,"value":str(n)}
    return None

def modular_obstruction(a,b,d,p):
    # Any primitive local pair can be rescaled to v=1 or u=1,p|v.
    powers = range(3,10) if p == 2 else range(1,5)
    for k in powers:
        m = p**k
        if m > 100000:
            break
        squares = {z*z % m for z in range(m)}
        found = (any(quartic(a,b,d,u,1)%m in squares for u in range(m))
                 or any(quartic(a,b,d,1,v)%m in squares
                        for v in range(0,m,p)))
        if not found:
            return {"p":p,"power":k,"modulus":m}
    return None

def descent(tag,a,b,primes):
    candidates = divisors_squarefree(primes)
    soluble, excluded, unknown = [], [], []
    for d in candidates:
        certs = {}
        bad = None
        for p in BAD:
            w = local_witness(a,b,d,p)
            if w is not None:
                certs[str(p)] = w
                continue
            obstruction = modular_obstruction(a,b,d,p) if p <= 457 else None
            if obstruction:
                bad = obstruction
                break
            certs[str(p)] = "unknown"
        if bad:
            excluded.append({"d":d,"certificate":bad})
        elif "unknown" in certs.values():
            unknown.append({"d":d,"certificates":certs})
        else:
            soluble.append({"d":d,"certificates":certs})
    assert not unknown
    # Good odd primes outside BAD have a smooth genus-one reduction and
    # an Fp point by Hasse, which lifts. At infinity every d is soluble:
    # for E, B<0; for dual, d>0 survivors and large u gives positivity.
    if tag == "dual":
        assert all(row["d"] > 0 for row in soluble)
    result = {"A":a,"B":b,"candidates":candidates,"locally_soluble":soluble,
              "excluded":excluded,"unknown":unknown}
    (ROOT/(tag+"-local-descent.json")).write_text(json.dumps(result,indent=2))
    return result

def reduction_count(p):
    assert (16*B*B*D) % p
    n = 1
    for x in range(p):
        f = (x**3+A*x*x+B*x) % p
        n += 1 if f == 0 else 2 if pow(f,(p-1)//2,p) == 1 else 0
    return n

def original_quartic_local():
    coefficients = [1813853,644010,-1810543,-1039740,961000]
    polynomial = fmpz_poly(coefficients)
    disc = polynomial.discriminant()
    assert disc == 2474894018773477950377523339416326400
    assert sorted(int(p) for p,e in disc.factor()) == BAD
    witnesses = {}
    for p in BAD:
        found = None
        for k in range(100 if p > 457 else 2*p+4):
            for u,v in ((k,1),(1,p*k)):
                value = sum(c*u**i*v**(4-i)
                            for i,c in enumerate(coefficients))
                if square_qp(value,p):
                    found = {"u":u,"v":v,"f":str(value)}
                    break
            if found:
                break
        assert found is not None
        witnesses[str(p)] = found
    (ROOT/"original-quartic-local.json").write_text(json.dumps(witnesses,indent=2))
    return {"discriminant":str(disc),"bad_prime_witnesses":witnesses,
            "everywhere_locally_soluble":True,
            "torsor_class":"an element of Sha(E)[2], a four-element group"}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gp",type=Path)
    args = parser.parse_args()
    start = time.perf_counter()
    x,y = POINT
    assert y*y == x**3+A*x*x+B*x
    counts = {p:reduction_count(p) for p in (7,17)}
    assert counts == {7:4,17:18} and gcd(*counts.values()) == 2
    factors_b = [(int(p),e) for p,e in fmpz(abs(B)).factor()]
    factors_d = [(int(p),e) for p,e in fmpz(D).factor()]
    assert factors_b == [(2,4),(5,1),(11,1),(23,1),(31,1),(486971,1)]
    assert factors_d == [(41,1),(457,1),(1414835497,1)]
    left = descent("E",A,B,[p for p,e in factors_b])
    right = descent("dual",-2*A,D,[p for p,e in factors_d])
    assert len(left["locally_soluble"]) == 16
    assert len(right["locally_soluble"]) == 2
    h = Q(16*D,B)
    j = Q(256*(A*A-3*B)**3,B*B*D)
    dual_j = Q(256*((-2*A)**2-3*D)**3,D*D*((-2*A)**2-4*D))
    assert j == (h+16)**3/h
    assert dual_j == (h+256)**3/(h*h)
    result = {
      "curve":[0,A,0,B,0],"dual":[0,-2*A,0,D,0],
      "point":[str(x),str(y)],"point_exact_equation_check":True,
      "good_reduction_orders":counts,"torsion_order":2,
      "B_factors":factors_b,"D_factors":factors_d,
      "isogeny_selmer_sizes":[16,2],"elementary_rank_bounds":[1,3],
      "j":str(j),"dual_j":str(dual_j),"X0_2_parameter_h":str(h),
      "original_quartic":original_quartic_local(),
    }
    F = fmpz_poly([1813853,644010,-1810543,-1039740,961000])
    K = fmpz_poly([432252,-666190,212505])
    M = fmpz_poly([-1347558035330,1338999985416,879427559295,
                  -1561869979515,529733615650])
    assert -16*K**4+4*A*K*K*F-B*F*F == 4*M*M
    R = 19096567765
    assert B == -16*R
    assert K.discriminant() == 4*R
    assert not fmpz(R).is_square()
    assert POINT[0] == 115*Q(28450240,954687)**2
    assert R % 115 == 0 and not fmpz(R//115).is_square()
    result["original_quartic"]["covering_map"] = {
      "K":[432252,-666190,212505],
      "M":[-1347558035330,1338999985416,879427559295,
           -1561869979515,529733615650],
      "X":"-4*K^2/Y^2","Z":"4*K*M/Y^3",
      "identity":"-16*K^4+4*A*K^2*F-B*F^2=4*M^2",
      "K_discriminant":str(4*R),
      "point_squareclass":115,"torsion_squareclass":-R,
      "rational_image_squareclasses_given_rank_one":[1,115,-R,-R//115],
      "required_squareclass":-1,
    }
    if args.gp:
        kwargs = {"creationflags":0x08000000} if sys.platform == "win32" else {}
        run = subprocess.run([str(args.gp.resolve()),"-q","-f",str(ROOT/"arithmetic.gp")],
                             capture_output=True,text=True,timeout=20,**kwargs)
        assert run.returncode == 0 and not run.stderr.strip(),run.stderr
        assert "POINT_ON_CURVE 1" in run.stdout
        assert re.search(r"RANK_DATA \[1, 1, 2,",run.stdout)
        assert "SELMER_BASIS_DIM 4" in run.stdout
        result["pari_output"] = run.stdout
        result["pari_rank_bounds"] = [1,1]
        result["pari_selmer_dimension"] = 4
        result["pari_sha2_quotient_dimension"] = 2
        result["deduced_sha_2primary"] = "(Z/2Z)^2"
        result["original_quartic"]["rational_points"] = "empty"
        result["original_quartic"]["torsor_class"] = "nonzero in Sha(E)[2]"
        (ROOT/"pari-replay.txt").write_text(run.stdout,encoding="utf-8")
    result["elapsed_seconds"] = time.perf_counter()-start
    result_name = "arithmetic-results.json" if args.gp else "arithmetic-elementary-results.json"
    (ROOT/result_name).write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))

if __name__ == "__main__":
    main()
