import ArchivedDottieRing
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! The Dirichlet slot from HiddenQuarticQuaternion.lean at
7053444979826a20e4393085454a38835602c48f. -/
namespace SuperZeta.HiddenQuarticQuaternion
noncomputable section
abbrev disc : ℕ := 41 * 457 * 1414835497
local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
set_option maxRecDepth 60000 in
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

def atPrime (p : ℕ) [Fact (Nat.Prime p)] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

def A : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
def B : DirichletCharacter ℂ disc :=
  DirichletCharacter.changeLevel (show 41 ∣ disc by decide) (atPrime 41) *
  DirichletCharacter.changeLevel (show 457 ∣ disc by decide) (atPrime 457) *
  DirichletCharacter.changeLevel (show 1414835497 ∣ disc by decide) (atPrime 1414835497)
def AB : DirichletCharacter ℂ (4 * disc) :=
  DirichletCharacter.changeLevel (show 4 ∣ 4 * disc by decide) A *
  DirichletCharacter.changeLevel (show disc ∣ 4 * disc by decide) B

def total (w : ℂ) := (riemannZeta w * AB.LFunction w + A.LFunction w * B.LFunction w) / 2
end
end SuperZeta.HiddenQuarticQuaternion
