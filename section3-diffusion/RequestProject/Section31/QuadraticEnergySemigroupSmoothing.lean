import RequestProject.Section31.QuadraticEnergyYosidaEnergy
import RequestProject.Section31.QuadraticEnergyClosedSublevel

/-! Positive-time finite energy for the actually constructed semigroup.
This proves membership in the closed energy domain, without claiming a
continuous representative of every closed-domain element. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

theorem closedSemigroup_exists_energy_bound (time : ℝ≥0) (timePositive : 0 < time)
    (forcing : H) :
    ∃ lifted : closedDomain domain form nonnegative,
      (lifted : H) = closedSemigroup domain form nonnegative closable domainDense time forcing ∧
      closedForm domain form nonnegative closable lifted ≤ ‖forcing‖ ^ 2 / (2 * (time : ℝ)) := by
  let orbit : ℕ → H := fun index =>
    closedSemigroupApproximation domain form nonnegative closable domainDense index time forcing
  let approximations : ℕ → closedDomain domain form nonnegative := fun index =>
    (smallStepLift domain form nonnegative closable domainDense
      (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
      (orbit index)).value
  have orbitLimit : Tendsto orbit atTop
      (nhds (closedSemigroup domain form nonnegative closable domainDense time forcing)) :=
    closedSemigroup_approximation_limit domain form nonnegative closable domainDense time forcing
  have errorBound : ∀ index,
      ‖smallStepResolvent domain form nonnegative closable domainDense
          (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) (orbit index) -
        smallStepResolvent domain form nonnegative closable domainDense
          (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
          (closedSemigroup domain form nonnegative closable domainDense time forcing)‖ ≤
      ‖orbit index - closedSemigroup domain form nonnegative closable domainDense time forcing‖ := by
    intro index
    rw [← map_sub]
    exact smallStepResolvent_norm domain form nonnegative closable domainDense _ _ _ _
  have errorLimit : Tendsto (fun index =>
      smallStepResolvent domain form nonnegative closable domainDense
          (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) (orbit index) -
        smallStepResolvent domain form nonnegative closable domainDense
          (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
          (closedSemigroup domain form nonnegative closable domainDense time forcing)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) errorBound
      (tendsto_iff_norm_sub_tendsto_zero.mp orbitLimit)
  have ambientLimit : Tendsto (fun index => (approximations index : H)) atTop
      (nhds (closedSemigroup domain form nonnegative closable domainDense time forcing)) := by
    have fixedLimit := smallStepResolvent_strong_limit domain form nonnegative closable domainDense
      canonicalYosidaStep canonicalYosidaStep_positive canonicalYosidaStep_le_one canonicalYosidaStep_tendsto
      (closedSemigroup domain form nonnegative closable domainDense time forcing)
    simpa only [sub_add_cancel, zero_add, approximations, smallStepLift_value]
      using errorLimit.add fixedLimit
  have timeRealPositive : 0 < (time : ℝ) := timePositive
  have energyBound : ∀ index,
      closedForm domain form nonnegative closable (approximations index) ≤
        ‖forcing‖ ^ 2 / (2 * (time : ℝ)) := by
    intro index
    have estimate := yosidaSmoothed_energy_time_bound domain form nonnegative closable domainDense
      (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
      forcing time time.coe_nonneg
    change 2 * (time : ℝ) * closedForm domain form nonnegative closable (approximations index) ≤
      ‖forcing‖ ^ 2 at estimate
    exact (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) timeRealPositive)).mpr
      (by simpa only [mul_comm] using estimate)
  exact closedForm_sublevel_limit domain form nonnegative closable approximations
    (closedSemigroup domain form nonnegative closable domainDense time forcing)
    (‖forcing‖ ^ 2 / (2 * (time : ℝ))) (by positivity) ambientLimit
      (Eventually.of_forall energyBound)

theorem closedSemigroup_mem_closedDomain (time : ℝ≥0) (timePositive : 0 < time)
    (forcing : H) :
    closedSemigroup domain form nonnegative closable domainDense time forcing ∈ closedDomain domain form nonnegative := by
  obtain ⟨lifted, same, _⟩ := closedSemigroup_exists_energy_bound domain form nonnegative closable domainDense
    time timePositive forcing
  rw [← same]
  exact lifted.property

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_exists_energy_bound
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_mem_closedDomain
