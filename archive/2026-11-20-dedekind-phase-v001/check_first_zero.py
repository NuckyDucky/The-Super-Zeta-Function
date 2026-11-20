"""Enclose both quadratic Dirichlet factors at the very same Riemann zero."""
import json

from flint import acb, acb_series, ctx, dirichlet_char


def estimate():
    ctx.prec = 160
    rho = acb.zeta_zero(1)
    chi3 = dirichlet_char(3, 2)
    chi4 = dirichlet_char(4, 3)
    assert [chi3(k) for k in range(3)] == [0, 1, -1]
    assert [chi4(k) for k in range(4)] == [0, 1, 0, -1]
    values = {
        "zeta_derivative": acb_series([rho, 1], prec=2).zeta()[1],
        "L_chi_minus3": rho.dirichlet_l(chi3),
        "L_chi_minus4": rho.dirichlet_l(chi4),
    }
    # Repeat the L-values using the periodic residue-class Hurwitz sums.
    for q, key in [(3, "L_chi_minus3"), (4, "L_chi_minus4")]:
        alternate = (rho.zeta(acb(1)/q) - rho.zeta(acb(q-1)/q)) * acb(q)**(-rho)
        assert alternate.overlaps(values[key]) and abs(alternate) > 1
    assert abs(values["zeta_derivative"]) > acb(3).real / 4
    assert all(abs(values[key]) > 1 for key in ["L_chi_minus3", "L_chi_minus4"])
    return {
        "precision_bits": ctx.prec,
        "riemann_zero_index": 1,
        "zero_ball": str(rho),
        "absolute_value_enclosures": {key: str(abs(value)) for key, value in values.items()},
        "quadratic_field_orders_at_this_point": {"-3": 1, "-4": 1},
    }


if __name__ == "__main__":
    print(json.dumps(estimate(), indent=2))
