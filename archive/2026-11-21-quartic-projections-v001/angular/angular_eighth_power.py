"""Test the doubled phase before using its predicted slope."""

from flint import arb

from balanced_angular_theta import PRECISION, SIDE, enclosure


real, imag, rounding, tail = enclosure(SIDE, PRECISION, degree=8)
assert real > 0 or real < 0
phase = (imag / real).atan()
print(f"Real part: {real.str(21, more=True)}")
print(f"Imaginary part: {imag.str(21, more=True)}")
print(f"Signed angle modulo pi: {phase.str(19, more=True)} rad")
print(f"Weight rounding error per component: < {rounding.upper()}")
print(f"Omitted lattice tail per component: < {tail.upper()}")

# The two branch lines are conjugates. Build delta^4 exactly.
a, b = -5_045_155, 1_027_708
real_fourth = a**4 - 6*a*a*b*b + b**4
imag_fourth = 4*a*b*(a*a-b*b)
slope = arb(imag_fourth)/real_fourth
assert (imag / real).contains(slope)
assert not (imag / real).overlaps(-slope)
print("The second angular measurement agrees with its predicted branch.")
