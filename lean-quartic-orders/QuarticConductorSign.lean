import GaussSign
import QuarticMurphyBridge

/-! Murphy's sign theorem specialized to the arithmetic character of the quartic. -/
namespace QuarticConductorSign
open QuarticFiniteFourier

theorem root_number : quarticCharacter.rootNumber = 1 :=
  DBN.Gen.rootNumber_eq_one_of_real_primitive quarticCharacter
    quarticCharacter_primitive QuarticMurphyBridge.character_real

theorem amplitude : gaussAmplitude = (Real.sqrt D : ℂ) :=
  QuarticMurphyBridge.amplitude root_number

theorem reflection {t : ℝ} (ht : 0 < t) :
    QuarticKernel.theta (t/QuarticKernel.scale) =
      t⁻¹ * QuarticKernel.theta (t⁻¹/QuarticKernel.scale) :=
  QuarticMurphyBridge.theta_reflection amplitude ht

/-- Pairwise quadratic residue signs among the three odd conductor primes. -/
theorem pairwise_residues :
    jacobiSym 457 41 = -1 ∧ jacobiSym 41 457 = -1 ∧
    jacobiSym 1414835497 41 = -1 ∧ jacobiSym 41 1414835497 = -1 ∧
    jacobiSym 1414835497 457 = 1 ∧ jacobiSym 457 1414835497 = 1 := by
  norm_num

end QuarticConductorSign
#print axioms QuarticConductorSign.root_number
#print axioms QuarticConductorSign.amplitude
#print axioms QuarticConductorSign.reflection
#print axioms QuarticConductorSign.pairwise_residues
