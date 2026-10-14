import RequestProject.Section31.QuadraticEnergyClosureRecovery

/-! A Poincare bound expressed by a bounded linear projection passes from
the original form domain to its constructed closure with the same constant.
In particular, zero closed energy forces that projection to vanish. The
actual mean-zero projection and its original bound must be supplied by a
model consumer; these statements alone do not assert irreducibility. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem closedForm_projection_bound
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)
    (closable : SequentiallyClosable domain form)
    (projection : H →L[ℝ] H) (constant : ℝ)
    (originalBound : ∀ values : domain, ‖projection values.val‖ ^ 2 ≤ constant * form values)
    (target : closedDomain domain form nonnegative) :
    ‖projection target.val‖ ^ 2 ≤
      constant * closedForm domain form nonnegative closable target := by
  obtain ⟨sequence, stateConvergence, energyConvergence⟩ :=
    exists_original_state_energy_approximation domain form nonnegative closable target
  have projectedConvergence :=
    projection.continuous.continuousAt.tendsto.comp stateConvergence
  exact le_of_tendsto_of_tendsto (projectedConvergence.norm.pow 2)
    (tendsto_const_nhds.mul energyConvergence)
    (Filter.Eventually.of_forall (fun index => originalBound (sequence index)))

theorem closedForm_projection_eq_zero_of_energy_zero
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)
    (closable : SequentiallyClosable domain form)
    (projection : H →L[ℝ] H) (constant : ℝ)
    (originalBound : ∀ values : domain, ‖projection values.val‖ ^ 2 ≤ constant * form values)
    (target : closedDomain domain form nonnegative)
    (zeroEnergy : closedForm domain form nonnegative closable target = 0) :
    projection target.val = 0 := by
  have bound := closedForm_projection_bound domain form nonnegative closable
    projection constant originalBound target
  rw [zeroEnergy, mul_zero] at bound
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (projection target.val)]

end
end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_projection_bound
#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_projection_eq_zero_of_energy_zero
