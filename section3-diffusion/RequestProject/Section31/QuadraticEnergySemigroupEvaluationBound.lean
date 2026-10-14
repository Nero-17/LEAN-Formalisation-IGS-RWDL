import RequestProject.Section31.QuadraticEnergySemigroupSmoothing

/-! Apply a proved closed-domain point-evaluation estimate to the actual
constructed semigroup. Positive-time domain membership and its energy
bound are supplied internally from the Yosida construction. -/

namespace IGS.Sec31.QuadraticEnergySpace

open scoped NNReal

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]

theorem closedSemigroup_exists_evaluation_bound
    (domain : Submodule ℝ Hilbert) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set Hilbert))
    (evaluation : closedDomain domain form nonnegative →ₗ[ℝ] ℝ)
    (normConstant energyConstant : ℝ) (energyNonnegative : 0 ≤ energyConstant)
    (evaluationBound : ∀ target : closedDomain domain form nonnegative,
      evaluation target ^ 2 ≤ normConstant * ‖target.val‖ ^ 2 +
        energyConstant * closedForm domain form nonnegative closable target)
    (time : ℝ≥0) (timePositive : 0 < time) (forcing : Hilbert) :
    ∃ lifted : closedDomain domain form nonnegative,
      lifted.val = closedSemigroup domain form nonnegative closable domainDense time forcing ∧
      evaluation lifted ^ 2 ≤
        normConstant * ‖closedSemigroup domain form nonnegative closable domainDense time forcing‖ ^ 2 +
        energyConstant * (‖forcing‖ ^ 2 / (2 * (time : ℝ))) := by
  obtain ⟨lifted, liftedEquality, energyBound⟩ :=
    closedSemigroup_exists_energy_bound domain form nonnegative closable domainDense time timePositive forcing
  refine ⟨lifted, liftedEquality, ?_⟩
  have bound := (evaluationBound lifted).trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left energyBound energyNonnegative))
  rw [liftedEquality] at bound
  exact bound

theorem closedSemigroup_exists_evaluation_bounds
    (domain : Submodule ℝ Hilbert) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set Hilbert))
    (evaluation : closedDomain domain form nonnegative →ₗ[ℝ] ℝ)
    (normCoefficient energyCoefficient : ℕ → ℝ)
    (energyNonnegative : ∀ level, 0 ≤ energyCoefficient level)
    (evaluationBounds : ∀ level (target : closedDomain domain form nonnegative),
      evaluation target ^ 2 ≤ normCoefficient level * ‖target.val‖ ^ 2 +
        energyCoefficient level * closedForm domain form nonnegative closable target)
    (time : ℝ≥0) (timePositive : 0 < time) (forcing : Hilbert) :
    ∃ lifted : closedDomain domain form nonnegative,
      lifted.val = closedSemigroup domain form nonnegative closable domainDense time forcing ∧
      ∀ level, evaluation lifted ^ 2 ≤
        normCoefficient level * ‖closedSemigroup domain form nonnegative closable domainDense time forcing‖ ^ 2 +
        energyCoefficient level * (‖forcing‖ ^ 2 / (2 * (time : ℝ))) := by
  obtain ⟨lifted, liftedEquality, energyBound⟩ :=
    closedSemigroup_exists_energy_bound domain form nonnegative closable domainDense time timePositive forcing
  refine ⟨lifted, liftedEquality, ?_⟩
  intro level
  have bound := (evaluationBounds level lifted).trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left energyBound (energyNonnegative level)))
  rw [liftedEquality] at bound
  exact bound

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_exists_evaluation_bound
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_exists_evaluation_bounds
