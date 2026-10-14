import RequestProject.Section31.SelfAdjointSemigroupInjective
import RequestProject.Section31.QuadraticEnergySemigroupSymmetry

/-! Injectivity and strictly positive quadratic pairings for the actual closed
semigroup. Every semigroup property is filled by its construction.
Candidate source, awaiting whole-file compilation. -/

namespace IGS.Sec31.QuadraticEnergySpace

open scoped NNReal
set_option maxHeartbeats 1000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

private theorem closedSemigroup_orbit_continuous_for_injectivity (values : H) :
    Continuous (fun time : ℝ≥0 => closedSemigroup domain form nonnegative closable domainDense time values) := by
  have inputContinuous : Continuous (fun time : ℝ≥0 => (values, time)) :=
    continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using
    (closedSemigroup_joint_continuous domain form nonnegative closable domainDense).comp inputContinuous

theorem closedSemigroup_injective (time : ℝ≥0) :
    Function.Injective (closedSemigroup domain form nonnegative closable domainDense time) := by
  exact selfAdjoint_continuous_semigroup_injective
    (closedSemigroup domain form nonnegative closable domainDense)
    (closedSemigroup_zero domain form nonnegative closable domainDense)
    (closedSemigroup_add domain form nonnegative closable domainDense)
    (closedSemigroup_selfAdjoint domain form nonnegative closable domainDense)
    (closedSemigroup_orbit_continuous_for_injectivity domain form nonnegative closable domainDense) time

theorem closedSemigroup_pairing_pos (time : ℝ≥0) (values : H) (nonzero : values ≠ 0) :
    0 < inner ℝ values (closedSemigroup domain form nonnegative closable domainDense time values) := by
  exact selfAdjoint_continuous_semigroup_pairing_pos
    (closedSemigroup domain form nonnegative closable domainDense)
    (closedSemigroup_zero domain form nonnegative closable domainDense)
    (closedSemigroup_add domain form nonnegative closable domainDense)
    (closedSemigroup_selfAdjoint domain form nonnegative closable domainDense)
    (closedSemigroup_orbit_continuous_for_injectivity domain form nonnegative closable domainDense) time values nonzero
end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_injective
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_pairing_pos
