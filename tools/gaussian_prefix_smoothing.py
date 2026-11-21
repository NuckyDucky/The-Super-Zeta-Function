"""Bound the difference between the smooth and weight-one Gaussian prefixes."""

from fractions import Fraction
from pathlib import Path
import sys

from flint import arb, ctx

ARCHIVE = Path(__file__).resolve().parents[1] / "archive"
sys.path.insert(0, str(ARCHIVE / "2026-11-20-gaussian-reflected-disks-v001"))
from gaussian_inputs import Q, height


def prefix_bounds(cutoff, shift):
    """Raw modulus on the padded rectangle and raw derivative on the original.

    Also bounds any fixed subset of the norms through cutoff. Both reflected
    terms use G(z) = exp(z^2 - i*pi*z/2). The proof is in gaussian-prefix-smoothing.md.
    """
    if not isinstance(shift, int) or shift < 1:
        raise ValueError("The contour shift must be a positive integer")
    if not isinstance(cutoff, int) or cutoff < 1:
        raise ValueError("The cutoff must be a positive integer")
    with ctx.workprec(256):
        pi = arb.pi()
        t = height()
        b = arb(Q).sqrt() / (2 * pi)
        limit = arb(cutoff)
        if not limit > b:
            raise ValueError("Use a majorizing cutoff greater than B")
        pad = arb(1) / 8192
        eta = arb(35) / 2048 + pad
        sigma_min = arb(1) / 2 - arb(63) / 2048 - pad
        split = t / 2 - eta
        k = arb(shift)
        gamma_denominator = b**2 * (2 * pi * t * (1 + t**2)).sqrt()

        # There is one first-quadrant representative per nonzero Gaussian ideal.
        prefactor = (24 * pi.sqrt() / (2 * pi * k) * limit * (b / limit)**sigma_min
                     * (1 + 2 * pi * (t + eta)).sqrt() / gamma_denominator)
        common = pi * eta / 2 + k**2
        near = prefactor * (common + 2 * k * eta / t
                            + (2 * k + arb(1) / 2)**2 / (4 * t**2)
                            + k * (limit / (b * t)).log()).exp()

        # Compare the two exponentially small terms in logarithms before exponentiation.
        log_far = ((3 * arb(2).sqrt() * prefactor).log() + common
                   + k * (limit / b).log() - split**2 / 2 + 1 / (8 * t**2))
        log_residues = ((4 * limit * k / ((t - eta) * gamma_denominator)).log()
                        + common + k * (limit / b).log() - (t - eta)**2)
        negligible = arb(10)**(-1000)
        if log_far < negligible.log() and log_residues < negligible.log():
            total = near + 2 * negligible
        else:
            total = near + log_far.exp() + log_residues.exp()
        return total.upper(), (total / pad).upper()


def main():
    with ctx.workprec(256):
        # In the published scale check S0 exceeds this explicit positive number.
        reference = arb(17) / arb(10)**30
        for cutoff, shift, target in ((360710144, 12, "4.0e-47"), (2**30, 11, "2.67e-41")):
            modulus, derivative = prefix_bounds(cutoff, shift)
            if not derivative < reference * arb(target):
                raise ArithmeticError(f"Smoothing derivative bound failed at {cutoff}")
            print(f"Through norm {cutoff} with shift {shift}:")
            print("  padded rectangle modulus divided by 1.70e-29 <", (modulus / reference).upper())
            print("  rectangle derivative divided by 1.70e-29 <", (derivative / reference).upper())

    # The archived verifier uses a wider box than the low-prefix weight test.
    # Only its sum of positive omitted-residue bounds depends on the cutoff.
    sys.path.insert(0, str(ARCHIVE / "2026-11-20-gaussian-circle-phases-v001"))
    with ctx.workprec(384):
        from replay_tail import tail_bound

        radius = Fraction(1, 25) - Fraction(63, 2048)
        if Fraction(35, 2048) + radius > Fraction(1, 32):
            raise ArithmeticError("Cauchy circle extends beyond the height range")
        absolute_tail = tail_bound()
        pad = arb(radius.numerator) / radius.denominator
        full_derivative = absolute_tail / (pad * reference)
        if not full_derivative < arb("4.813e12"):
            raise ArithmeticError("Full remainder exceeds the stated derivative estimate")
        print("Full minus sharp, rectangle derivative divided by 1.70e-29 <", full_derivative.upper())


if __name__ == "__main__":
    main()
