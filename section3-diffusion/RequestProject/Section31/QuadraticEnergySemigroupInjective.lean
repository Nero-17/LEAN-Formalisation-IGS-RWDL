import RequestProject.Section31.SelfAdjointSemigroupInjective
import RequestProject.Section31.QuadraticEnergySemigroupSymmetry

/-! Injectivity and strictly positive quadratic pairings for the actual closed
semigroup. Every semigroup property is filled by its construction.
Candidate source, awaiting whole-file compilation. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

theorem closedSemigroup_injective (time : ℝ≥0) :
    Function.Injective (closedSemigroup domain form nonnegative closable domainDense time) :=
  selfAdjoint_continuous_semigroup_injective _
    (closedSemigroup_zero domain form nonnegative closable domainDense)
    (closedSemigroup_add domain form nonnegative closable domainDense)
    (closedSemigroup_selfAdjoint domain form nonnegative closable domainDense)
    (fun values => (closedSemigroup_joint_continuous domain form nonnegative closable domainDense).comp
      (continuous_const.prodMk continuous_id)) time

theorem closedSemigroup_pairing_pos (time : ℝ≥0) (values : H) (nonzero : values ≠ 0) :
    0 < inner ℝ values (closedSemigroup domain form nonnegative closable domainDense time values) :=
  selfAdjoint_continuous_semigroup_pairing_pos _
    (closedSemigroup_zero domain form nonnegative closable domainDense)
    (closedSemigroup_add domain form nonnegative closable domainDense)
    (closedSemigroup_selfAdjoint domain form nonnegative closable domainDense)
    (fun values => (closedSemigroup_joint_continuous domain form nonnegative closable domainDense).comp
      (continuous_const.prodMk continuous_id)) time values nonzero

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_injective
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_pairing_pos
