import RequestProject.Section31.QuadraticEnergyCompletion
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! The actual completed quadratic energy on the whole ambient Hilbert space:
finite on its constructed closed domain, infinity elsewhere. -/

namespace IGS.Sec31.QuadraticEnergySpace

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)

noncomputable def closedExtendedEnergy (target : H) : ℝ≥0∞ := by
  classical
  exact if membership : target ∈ closedDomain domain form nonnegative then
    ENNReal.ofReal (closedForm domain form nonnegative closable ⟨target, membership⟩)
  else ⊤

theorem closedExtendedEnergy_of_mem (target : H)
    (membership : target ∈ closedDomain domain form nonnegative) :
    closedExtendedEnergy domain form nonnegative closable target =
      ENNReal.ofReal (closedForm domain form nonnegative closable ⟨target, membership⟩) := by
  rw [closedExtendedEnergy, dif_pos membership]

theorem closedExtendedEnergy_of_not_mem (target : H)
    (membership : target ∉ closedDomain domain form nonnegative) :
    closedExtendedEnergy domain form nonnegative closable target = ⊤ := by
  rw [closedExtendedEnergy, dif_neg membership]

theorem closedExtendedEnergy_ne_top_iff (target : H) :
    closedExtendedEnergy domain form nonnegative closable target ≠ ⊤ ↔
      target ∈ closedDomain domain form nonnegative := by
  classical
  by_cases membership : target ∈ closedDomain domain form nonnegative
  · simp [closedExtendedEnergy, membership]
  · simp [closedExtendedEnergy, membership]

theorem closedExtendedEnergy_original (target : domain) :
    closedExtendedEnergy domain form nonnegative closable (target : H) = ENNReal.ofReal (form target) := by
  rw [closedExtendedEnergy_of_mem domain form nonnegative closable (target : H)
    (original_mem_closedDomain domain form nonnegative target), closedForm_extends]

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedExtendedEnergy_of_mem
#print axioms IGS.Sec31.QuadraticEnergySpace.closedExtendedEnergy_of_not_mem
#print axioms IGS.Sec31.QuadraticEnergySpace.closedExtendedEnergy_ne_top_iff
#print axioms IGS.Sec31.QuadraticEnergySpace.closedExtendedEnergy_original
