import RequestProject.Section31.QuadraticEnergySemigroup
import RequestProject.Section31.QuadraticEnergyGeneratorDensity

/-! Symmetry of the actual small-step resolvents, their Yosida exponentials,
and the constructed strong-limit semigroup. Only strong convergence is used
to pass the inner-product identity to the limit. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

theorem smallStepResolvent_selfAdjoint
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1) :
    IsSelfAdjoint (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro first second
  let firstSolution := (smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm first
  let secondSolution := (smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm second
  have firstEquation := smallStepSolution_identity domain form nonnegative closable domainDense step stepPositive stepAtMostOne first
  have secondEquation := smallStepSolution_identity domain form nonnegative closable domainDense step stepPositive stepAtMostOne second
  have firstPairing := congrArg (fun vector : H => inner ℝ vector (secondSolution : H)) firstEquation
  have secondPairing := congrArg (fun vector : H => inner ℝ (firstSolution : H) vector) secondEquation
  change inner ℝ ((firstSolution : H) + step • closedGenerator domain form nonnegative closable domainDense firstSolution)
      (secondSolution : H) = inner ℝ first (secondSolution : H) at firstPairing
  change inner ℝ (firstSolution : H)
      ((secondSolution : H) + step • closedGenerator domain form nonnegative closable domainDense secondSolution) =
    inner ℝ (firstSolution : H) second at secondPairing
  rw [inner_add_left, real_inner_smul_left] at firstPairing
  rw [inner_add_right, inner_smul_right] at secondPairing
  rw [closedGenerator_symmetric] at firstPairing
  change inner ℝ (firstSolution : H) second = inner ℝ first (secondSolution : H)
  linarith

theorem yosidaSemigroup_selfAdjoint
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1) (time : ℝ) :
    IsSelfAdjoint (yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time) := by
  have resolventSelfAdjoint := smallStepResolvent_selfAdjoint domain form nonnegative closable domainDense step stepPositive stepAtMostOne
  have generatorSelfAdjoint : IsSelfAdjoint
      (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne) :=
    (IsSelfAdjoint.all (step⁻¹)).smul ((IsSelfAdjoint.one (H →L[ℝ] H)).sub resolventSelfAdjoint)
  rw [yosidaSemigroup_eq_exp]
  exact ((IsSelfAdjoint.all (-time)).smul generatorSelfAdjoint).exp

theorem closedSemigroup_selfAdjoint (time : ℝ≥0) :
    IsSelfAdjoint (closedSemigroup domain form nonnegative closable domainDense time) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro first second
  have approximationSymmetry : ∀ index,
      inner ℝ (closedSemigroupApproximation domain form nonnegative closable domainDense index time first) second =
        inner ℝ first (closedSemigroupApproximation domain form nonnegative closable domainDense index time second) := by
    intro index
    exact (yosidaSemigroup_selfAdjoint domain form nonnegative closable domainDense
      (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
      time).isSymmetric first second
  have leftLimit := (closedSemigroup_approximation_limit domain form nonnegative closable domainDense time first).inner (𝕜 := ℝ)
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => second) atTop (nhds second))
  have rightLimit := (tendsto_const_nhds : Tendsto (fun _ : ℕ => first) atTop (nhds first)).inner (𝕜 := ℝ)
    (closedSemigroup_approximation_limit domain form nonnegative closable domainDense time second)
  simp_rw [approximationSymmetry] at leftLimit
  exact tendsto_nhds_unique leftLimit rightLimit

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.smallStepResolvent_selfAdjoint
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSemigroup_selfAdjoint
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_selfAdjoint
