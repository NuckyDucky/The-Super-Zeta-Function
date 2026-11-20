"""Enclose a right-hand preimage for signed Gaussian targets by a log-derivative bound."""
from collections import Counter
from pathlib import Path
import json

from flint import acb, acb_series, arb, ctx, dirichlet_char
from gaussian_inputs import LIMIT, Q, height, prime_ideals


def main():
    ctx.prec = 160
    T = height()
    log_b = (arb(Q).sqrt()/(2*arb.pi())).log()
    scale = 2*log_b + acb(2,T).lgamma().real
    _, ideals = prime_ideals(LIMIT)
    counts = Counter(ideals)
    primes = [(arb(q).log(), (acb(0,-T)*arb(q).log()).exp(), chi, n)
              for (q,chi),n in counts.items()]

    def evaluate(sigma, dt):
        w = acb(sigma,T+dt)
        v_log = w*log_b + w.lgamma()-scale
        derivative = log_b+w.digamma()
        zeta_k = acb(sigma).zeta()*acb(sigma).dirichlet_l(dirichlet_char(4,3))
        positive_product = arb(1)
        for logq, phase, chi, n in primes:
            magnitude = (-sigma*logq).exp()
            positive_product *= (1-magnitude)**n
            if chi:
                u = chi*phase*magnitude*acb(0,-dt*logq).exp()
                v_log -= n*(1-u).log()
                derivative -= n*logq*u/(1-u)
        return v_log.exp(), derivative, (zeta_k.real*positive_product).log().upper()

    targets = ("6e-16","6e-17","2e-17","8e-18","4e-18","2e-18","1e-18")
    rows = []
    for sign in (1,-1):
        for literal in targets:
            a = sign*arb(literal)
            # The approximate guesses only choose disk centers. All existence
            # and simplicity assertions below use fresh interval calculations.
            sigma = arb(2)+abs(a).log()/44
            dt = arb("0.025") if sign==1 else arb("-0.045")
            for _ in range(3):
                value, derivative, _ = evaluate(sigma,dt)
                step = ((value/a).log()/derivative)
                sigma = arb(float((sigma-step.real).mid()))
                dt = arb(float((dt-step.imag).mid()))
            value, _, tail = evaluate(sigma,dt)
            residual = abs((value/a).log())+tail
            row = {"target":("+" if sign==1 else "-")+literal,"center_re":float(sigma),
                   "center_dt":float(dt),"truncated_log_residual_plus_tail":str(residual.upper())}
            for k in range(1,80):
                r = arb(k)/2000
                smin = sigma-r
                if not (smin>1 and sigma+r<2 and abs(dt)+r<arb(1)/16):
                    break
                zs = acb_series([smin,1],prec=2).zeta()
                eps = (arb(1)/2+arb.pi()/4)/(T-1)
                m = log_b+(T-1).log()+2*(zs[1]/zs[0]).real-eps
                if m*r > residual:
                    row.update(certified=True,radius=f"{k}/2000",
                               real_logder_lower=str(m.lower()))
                    break
            row.setdefault("certified",False)
            rows.append(row)
            print(row["target"], row["center_re"], row["center_dt"], row.get("radius","unresolved"),flush=True)
    expected = {"+6e-16", "+6e-17", "+2e-17", "+8e-18", "+4e-18",
                "-6e-16", "-6e-17", "-2e-17", "-8e-18"}
    assert expected <= {row["target"] for row in rows if row["certified"]}
    out={"bits":ctx.prec,"prime_norm_cutoff":LIMIT,"height_offsets":"offset from T_D",
         "window":"-1 < Re w < 2, |Im w-T_D| < 1/16","positions":rows}
    Path(__file__).with_name("branch-positions.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")


if __name__=="__main__":
    main()
