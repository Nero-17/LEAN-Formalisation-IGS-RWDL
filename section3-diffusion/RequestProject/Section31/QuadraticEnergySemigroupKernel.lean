import RequestProject.Section31.QuadraticEnergySemigroup
import RequestProject.Section31.QuadraticEnergyResolventMinimum

/-! Zero-energy core vectors are fixed by the actual closed-form semigroup.
This supplies the operator part of conservativeness once the actual constant
vectors are substituted. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

theorem resolventState_fixed_of_original_energy_zero (values : domain)
    (energyZero : form values = 0) :
    resolventState domain form nonnegative closable (values : H) = (values : H) := by
  let test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable) :=
    ⟨⟨(values : H), original_mem_closedDomain domain form nonnegative values⟩⟩
  have bound := resolvent_minimizes domain form nonnegative closable (values : H) test
  have testEnergy : closedForm domain form nonnegative closable test.value = 0 := by
    exact (closedForm_extends domain form nonnegative closable values).trans energyZero
  change closedForm domain form nonnegative closable
      (resolventLift domain form nonnegative closable (values : H)).value +
      ‖resolventState domain form nonnegative closable (values : H) - (values : H)‖ ^ 2 ≤
    closedForm domain form nonnegative closable test.value + ‖(values : H) - (values : H)‖ ^ 2 at bound
  rw [testEnergy, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at bound
  have energyNonnegative := closedForm_nonnegative domain form nonnegative closable
    (resolventLift domain form nonnegative closable (values : H)).value
  have normZero : ‖resolventState domain form nonnegative closable (values : H) - (values : H)‖ = 0 := by
    nlinarith [norm_nonneg (resolventState domain form nonnegative closable (values : H) - (values : H))]
  exact sub_eq_zero.mp (norm_eq_zero.mp normZero)

theorem closedSemigroup_fixed_of_generator_zero
    (values : generatorDomain domain form nonnegative closable)
    (generatorZero : closedGenerator domain form nonnegative closable domainDense values = 0)
    (time : ℝ≥0) :
    closedSemigroup domain form nonnegative closable domainDense time values = (values : H) := by
  have approximationFixed : ∀ index,
      closedSemigroupApproximation domain form nonnegative closable domainDense index time values = (values : H) := by
    intro index
    have bound := yosidaSemigroup_domain_time_bound domain form nonnegative closable domainDense
      (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
      time time.coe_nonneg values
    rw [generatorZero, norm_zero, mul_zero] at bound
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm bound (norm_nonneg _)))
  apply tendsto_nhds_unique (closedSemigroup_approximation_limit domain form nonnegative closable domainDense time (values : H))
  simpa only [approximationFixed] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (values : H)) atTop (nhds (values : H)))

theorem closedSemigroup_fixed_of_original_energy_zero (values : domain)
    (energyZero : form values = 0) (time : ℝ≥0) :
    closedSemigroup domain form nonnegative closable domainDense time (values : H) = (values : H) := by
  have resolventFixed := resolventState_fixed_of_original_energy_zero domain form nonnegative closable values energyZero
  have generatorZero : closedGenerator domain form nonnegative closable domainDense
      (resolventRangeEquiv domain form nonnegative closable domainDense (values : H)) = 0 := by
    rw [closedGenerator_resolvent, resolventFixed, sub_self]
  have fixed := closedSemigroup_fixed_of_generator_zero domain form nonnegative closable domainDense
    (resolventRangeEquiv domain form nonnegative closable domainDense (values : H)) generatorZero time
  change closedSemigroup domain form nonnegative closable domainDense time
    (resolventState domain form nonnegative closable (values : H)) =
      resolventState domain form nonnegative closable (values : H) at fixed
  simpa only [resolventFixed] using fixed

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.resolventState_fixed_of_original_energy_zero
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_fixed_of_generator_zero
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_fixed_of_original_energy_zero
