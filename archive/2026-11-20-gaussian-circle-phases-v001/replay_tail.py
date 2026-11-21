"""Recompute the uniform 2^28 tail majorant using the archived integral estimates."""
from collections import defaultdict
import json

from flint import acb, arb, ctx

from replay import HERE, arc
from gaussian_inputs import Q, height, prime_ideals


def tail_bound():
    ctx.prec = 384
    T = arc.T = height()
    B = arc.B = arb(Q).sqrt() / (2 * arb.pi())
    s0 = acb(arb(1) / 2, T)
    gamma0 = ((s0 - 2) * B.log() + s0.lgamma() - acb(2, T).lgamma().real).exp()
    N, X = arb(2**28), arb(7417868472142536246)
    grouped = defaultdict(list)
    for p, sign in prime_ideals(100000)[1]:
        grouped[p].append(sign)
    sieve = sorted(p for p, signs in grouped.items() if sorted(signs) == [-1, 1])[:404]
    assert len(sieve) == 404
    D, E = arb.pi() / 4, arb(1)
    for p in sieve:
        D *= arb(p - 1) / (p + 1)
        root = arb(p).sqrt()
        E *= (root + 1) / (root - 1)

    def below_split(c, low):
        result = arb(0)
        for exponent, coefficient in ((arb(1), D), (arb(1) / 2, E)):
            h = exponent - c
            result += coefficient * (X**h + c * (X**h - low**h) / h)
        return result

    def above_split(b):
        return D * b * X**(1 - b) / (b - 1) + E * b * X**(arb(1)/2 - b) / (b - arb(1)/2)

    xi = arb(1) / 25
    log_bound = arb.pi()/64 + 3/(16*(T - 1)) + xi * abs((B*T/X).log())
    residue = 2 * abs(gamma0) * log_bound.exp() * X**xi * below_split(arb(1)/2 + xi, N)
    left = min(2 * arc.integral_bound(a) * below_split(a, arb(1))
               for a in (arb(j)/32 for j in range(2, 14)))
    right = min(2 * arc.integral_bound(b) * above_split(b)
                for b in (1 + arb(j)/32 for j in range(1, 17)))
    return (residue + left + right).upper()


if __name__ == "__main__":
    observed = tail_bound()
    recorded = arb(json.loads((HERE / "tail-bound.json").read_text())["total_modulus_error"])
    assert observed.overlaps(recorded) and observed < arb("7.557639e-19")
    print(observed)
