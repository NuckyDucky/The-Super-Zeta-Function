"""Interval diagnostic for a constant axis on one ordinary-zeta contour."""

from flint import acb, arb, ctx


def signed_turn(a: acb, b: acb) -> arb:
    return (a.conjugate() * b).imag / (abs(a) * abs(b))


def check() -> None:
    ctx.prec = 144
    center = acb(arb(3) / 4, 100000001)
    radius = arb(31) / 128
    points = (center + radius, center + radius * acb(arb(3) / 5, arb(4) / 5),
              center - radius)
    readings = [
        (-arb.pi().log() * w / 2).exp() * (w / 2).gamma() * w.zeta() for w in points
    ]
    turns = tuple(signed_turn(x, y) for x, y in zip(readings, readings[1:] + readings[:1]))
    for turn in turns:
        print(turn)
    if not all(t > arb(1) / 4 for t in turns):
        raise ArithmeticError("The three positive oriented determinants were not enclosed.")
    # Positive multiples of the three readings sum to zero. The multipliers
    # are the unnormalized determinants of the other two readings in order.
    print("Each normalized determinant exceeds 1/4.")


if __name__ == "__main__":
    check()
