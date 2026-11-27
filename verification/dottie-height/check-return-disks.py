"""Certify sampled cap periods with FLINT complex balls.

For each coordinate the even return is an iterate of z ↦ exp(a exp(-a z)).
Enclose its derivative on a square containing the closed disk. A return
derivative bound less than one and the center residual imply contraction and
self-mapping on the disk. Cap entry therefore gives convergence to the
cycle. Comparing the disk image at period / p for each prime p dividing the
period excludes all smaller periods.
"""

from dataclasses import dataclass
import json

from flint import acb, arb, ctx, fmpz


@dataclass(frozen=True)
class Sample:
    real: tuple[int, int]
    imag_pi: tuple[int, int]
    period: int
    entry: int
    centers: tuple[tuple[str, str], tuple[str, str]]
    radius: str
    derivative_ceiling: str


SAMPLES = (
    Sample(
        (837, 178), (171, 112), 40, 320,
        (
            ("0.99999197935678294863453199955952065", "-0.00000090900130550503562034730932959378066"),
            ("0.022235204049339188907923396469877161", "-0.13365518820420801646462750318507222"),
        ),
        "1e-15", "0.005",
    ),
    Sample(
        (3, 178), (33, 112), 168, 840,
        (
            ("1.00007083822555772593432065985358585688646337",
             "-0.000123487052754782353119212160748049525860538635"),
            ("1", "0"),
        ),
        "1e-32", "1e-6",
    ),
    Sample(
        (3, 178), (249, 560), 234, 468,
        (
            ("1.00000000000252969537536262197725353673280835",
             "0.0000000000015070274304873534695635377675149151104212946"),
            ("1", "0"),
        ),
        "1e-32", "1e-149",
    ),
    Sample(
        (3, 178), (621, 560), 300, 900,
        (
            ("1.00012264486593049476759014269379594611120761",
             "0.00011183133557158175364101070871821631933816196"),
            ("0.999999999999999999999998955403543952131874887",
             "5.40995543831094316365566209817752086702149814e-24"),
        ),
        "1e-32", "1e-16",
    ),
)


def advance(lift, point):
    p, q = point
    return (lift * q).exp(), (-lift * p).exp()


def bound_scalar_return(coefficient, center, box, iterations):
    z, center_image, derivative = center + box, center, acb(1)
    for _ in range(iterations):
        inner = (-coefficient * z).exp()
        z = (coefficient * inner).exp()
        derivative *= -coefficient**2 * inner * z
        center_image = (coefficient * (-coefficient * center_image).exp()).exp()
    return abs(derivative), abs(center_image - center)


def require(enclosed, message):
    if not enclosed:
        raise ArithmeticError(message)


def certify(sample):
    lift = acb(arb(sample.real[0]) / sample.real[1],
               sample.imag_pi[0] * arb.pi() / sample.imag_pi[1])
    radius, ceiling = arb(sample.radius), arb(sample.derivative_ceiling)
    zero_interval = arb("0 +/- " + sample.radius)
    box = acb(zero_interval, zero_interval)
    centers = tuple(acb(arb(x), arb(y)) for x, y in sample.centers)

    state = acb(1), acb(1)
    for _ in range(sample.entry):
        state = advance(lift, state)
    for value, center in zip(state, centers):
        require(abs(value - center) < radius, f"period {sample.period}: cap entry")

    for coefficient, center in zip((lift, -lift), centers):
        derivative, residual = bound_scalar_return(coefficient, center, box, sample.period // 2)
        require(derivative < ceiling < 1, f"period {sample.period}: derivative")
        require(residual + ceiling * radius < radius, f"period {sample.period}: self-map")

    proper_returns = {sample.period // int(p) for p, _ in fmpz(sample.period).factor()}
    state = tuple(z + box for z in centers)
    for n in range(1, max(proper_returns) + 1):
        state = advance(lift, state)
        if n in proper_returns:
            require(any(abs(z - center) > arb(1) / 10 for z, center in zip(state, centers)),
                    f"period {sample.period}: shorter return at {n}")

    return {
        "Re L": "/".join(map(str, sample.real)),
        "Im L / pi": "/".join(map(str, sample.imag_pi)),
        "least period": sample.period,
        "cap entry update": sample.entry,
        "return derivative strictly below": sample.derivative_ceiling,
        "excluded proper returns": sorted(proper_returns),
    }


if __name__ == "__main__":
    ctx.prec = 1536
    for sample in SAMPLES:
        print(json.dumps(certify(sample)))
