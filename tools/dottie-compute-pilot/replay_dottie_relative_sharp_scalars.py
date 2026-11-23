"""Generate rational candidate caps for the sharp-circle relative model.

This directed Arb replay uses the two frozen moment lists. Its scalar caps
can be checked by Lean, with enclosures for the actual moment lists and the
model terms supplied separately. Endpoints are turns and exclude the left
endpoint in the final angular partition.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpq


TARGET = Fraction(19037, 100)
SCALE = 2**64
HEIGHT = ("4526119322477.945393315398", "4526119322477.945393329807")
LOG_THETA = ("14.30953739532295338557", "14.30953739532295338559")
PHASE = ("3.92292369", "3.92292670")
REFERENCE_CUTOFF = 276824064
SHARP_CUTOFF = 1442840576


def interval(lo, hi):
    return arb(lo).union(arb(hi))


def arc_moments(data, label):
    moments = data["moments"]
    if len(moments) != 17 or data.get("divided_by_factorial") is not True:
        raise ValueError(f"Expected 17 factorial-divided moments for {label}")
    return [acb(arb(x), arb(y)) for x, y in moments]


def horner(coefficients, value):
    result = acb(0)
    for coefficient in reversed(coefficients):
        result = result * value + coefficient
    return result


def upper_ticks(value):
    return int(str((value.upper() * SCALE).ceil().fmpq()))


def lower_ticks(value):
    return int(str((value.lower() * SCALE).floor().fmpq()))


class RelativeModel:
    def __init__(self, sharp, reference):
        self.moments = sharp
        self.shift = arb(1)/512
        self.reference = acb(arb(1)/2, interval(*HEIGHT) - self.shift)
        theta = interval(*PHASE)
        self.unit = acb(theta.cos(), theta.sin())
        self.exponent_slope = acb(interval(*LOG_THETA), 0) + self.reference.log()
        ref_poly = horner(reference, acb(0, -self.shift))
        ref_error = arb(0, arb(3)/10**30)
        self.reference_projection = abs((self.unit * (ref_poly + acb(ref_error, ref_error))).real)
        self.reference_ticks = upper_ticks(self.reference_projection)

    def factor(self, delta):
        z = self.reference + delta
        q = delta / self.reference
        if not abs(q) <= arb(1)/2 or not z.real > 0 or not abs(z.imag) >= 1:
            raise ArithmeticError("Relative factor left the proved Stirling domain")
        error = (1/(3*abs(self.reference.imag)) + 1/(3*abs(z.imag))
                 + abs(z - arb(1)/2)*abs(q)**2)
        error_rect = arb(0, error.upper())
        correction = self.exponent_slope*delta + (delta-arb(1)/2)*q
        return (correction + acb(error_rect, error_rect)).exp()

    def caps(self, lo, hi):
        degrees = interval(fmpq(lo.numerator, lo.denominator),
                           fmpq(hi.numerator, hi.denominator))
        theta = 2*arb.pi()*degrees
        x = arb(1)/64 + (arb(31)/2048)*theta.cos()
        y = (arb(31)/2048)*theta.sin()
        if not x > 0:
            raise ArithmeticError("An angular interval crossed the half-line")
        plus, minus = acb(x, y), acb(-x, y)
        f_plus, f_minus = self.factor(plus), self.factor(minus)
        P_plus = horner(self.moments, plus - acb(0, self.shift))
        P_minus = horner(self.moments, minus - acb(0, self.shift))
        projection = (self.unit*(f_plus*P_plus-f_minus*P_minus)).imag
        tail = abs(f_plus)+abs(f_minus)
        return lower_ticks(x), upper_ticks(x), upper_ticks(projection), upper_ticks(tail)


def collect_caps(model):
    initial = 512
    pending = [(Fraction(k, initial), Fraction(k+1, initial), 0)
               for k in range(initial - 1, -1, -1)]
    rows = []
    minimum = None
    while pending:
        lo, hi, depth = pending.pop()
        x_lower, x, projected, norm_sum = model.caps(lo, hi)
        signed_upper = Fraction(projected, SCALE) + Fraction(norm_sum, SCALE*10**11)
        reference_product = Fraction(2*x*model.reference_ticks, SCALE**2)
        if x_lower > 0 and reference_product > 0 and signed_upper <= -TARGET*reference_product:
            reading_lower = -signed_upper/reference_product
            minimum = reading_lower if minimum is None else min(minimum, reading_lower)
            rows.append({"lo": str(lo), "hi": str(hi), "x_upper_ticks": x,
                         "model_upper_ticks": projected, "norm_upper_ticks": norm_sum})
        else:
            if depth >= 30:
                raise ArithmeticError(f"No passing scalar caps on {(lo, hi)}")
            mid = (lo + hi)/2
            pending.extend(((mid, hi, depth+1), (lo, mid, depth+1)))
    if (not rows or rows[0]["lo"] != "0" or rows[-1]["hi"] != "1"
            or any(p["hi"] != q["lo"] for p, q in zip(rows, rows[1:]))):
        raise ArithmeticError("The candidate arc partition is not contiguous")
    return rows, minimum


def lean_source(report):
    rows = report["arcs"]
    terms = []
    for row in rows:
        lo, hi = Fraction(row["lo"]), Fraction(row["hi"])
        terms.append(f"  ⟨{lo}, {hi}, {row['x_upper_ticks']}, "
                     f"{row['model_upper_ticks']}, {row['norm_upper_ticks']}⟩")
    chunks = []
    names = []
    for start in range(0, len(terms), 64):
        name = f"dottieSharpArchiveArcBlock{start // 64}"
        body = ",\n".join(terms[start:start + 64])
        chunks.append(f"private def {name} : List DottieSharpArcCaps := [\n{body}\n]")
        names.append(name)
    data_terms = "\n\n".join(chunks)
    block_names = ",\n  ".join(names)
    return f'''import DottieSharpArcCaps

namespace QuarticModel

open SuperZeta.StirlingCorrection
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 32000

/-! Rational caps for the archived 17-moment model. The two model
enclosure inputs in the final declaration still refer to the real model. -/

def dottieSharpArchiveRefTicks : ℤ := {report['reference_projection_upper_ticks']}

{data_terms}

def dottieSharpArchiveArcCaps : List DottieSharpArcCaps := [
  {block_names}
].flatten

theorem dottie_sharp_archive_arc_caps_cover :
    dottieSharpArcCover 0 dottieSharpArchiveArcCaps = true := by
  decide +kernel

theorem dottie_sharp_archive_arc_caps_pass :
    dottieSharpArchiveArcCaps.all (dottieSharpArcPass dottieSharpArchiveRefTicks) = true := by
  decide +kernel

theorem dottie_sharp_margin_of_archive_caps_enclosures
    (href : dottieRelativeReferenceProjection ≤
      (dottieSharpArchiveRefTicks : ℝ)/(dottieSharpArcScale : ℝ))
    (hcaps : ∀ a ∈ dottieSharpArchiveArcCaps, ∀ t : ℝ, t ∈ Set.Ioc (a.lo : ℝ) (a.hi : ℝ) →
      DottieSharpArcCapsAt a (dottieSharpPointAtTurn t)) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) :=
  dottie_sharp_margin_of_checked_arc_caps dottieSharpArchiveArcCaps dottieSharpArchiveRefTicks
    dottie_sharp_archive_arc_caps_cover dottie_sharp_archive_arc_caps_pass href hcaps

#print axioms dottie_sharp_archive_arc_caps_cover
#print axioms dottie_sharp_archive_arc_caps_pass
#print axioms dottie_sharp_margin_of_archive_caps_enclosures

end QuarticModel
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--sharp-moments", type=Path, required=True)
    parser.add_argument("--reference-table", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--lean-out", type=Path, help="emit the exact Lean scalar and cover checks")
    args = parser.parse_args()
    ctx.prec = 224

    raw_sharp = args.sharp_moments.read_bytes()
    raw_reference = args.reference_table.read_bytes()
    sharp_data = json.loads(raw_sharp)
    if sharp_data["cutoff"] != SHARP_CUTOFF:
        raise ValueError("Wrong sharp-moment cutoff")
    ref_data = json.loads(raw_reference)["cutoffs"][str(REFERENCE_CUTOFF)]
    model = RelativeModel(arc_moments(sharp_data, "sharp"), arc_moments(ref_data, "reference"))
    caps, min_lower = collect_caps(model)
    report = {
        "format": "dottie-relative-sharp-scalar-caps-v1",
        "status": "directed Arb with frozen moment inputs",
        "height_interval": HEIGHT,
        "log_theta_interval": LOG_THETA,
        "phase_interval": PHASE,
        "precision_bits": ctx.prec,
        "sharp_cutoff": SHARP_CUTOFF,
        "reference_cutoff": REFERENCE_CUTOFF,
        "sharp_moment_sha256": hashlib.sha256(raw_sharp).hexdigest(),
        "reference_table_sha256": hashlib.sha256(raw_reference).hexdigest(),
        "target": str(TARGET),
        "scale": SCALE,
        "reference_projection_upper_ticks": model.reference_ticks,
        "minimum_lower": str(min_lower),
        "arcs": caps,
    }
    args.out.write_text(json.dumps(report, separators=(",", ":")) + "\n", encoding="utf-8")
    if args.lean_out is not None:
        args.lean_out.write_text(lean_source(report), encoding="utf-8", newline="\n")
    print(f"{len(caps)} arcs, rational lower bound {float(min_lower):.12f}")


if __name__ == "__main__":
    main()
