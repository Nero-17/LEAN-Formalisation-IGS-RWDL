import RequestProject.Section31.QuadraticEnergyYosidaFormBound
import RequestProject.Section31.QuadraticEnergySemigroupSmoothing

/-! The actual constructed semigroup contracts its original closed energy.
The sublevel limit supplies the positive-time closed-domain representative;
the target need not lie in the original core or the generator domain. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNReal
set_option maxHeartbeats 2000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

theorem closedSemigroup_exists_energy_contraction (time : ℝ≥0)
    (target : closedDomain domain form nonnegative) :
    ∃ lifted : closedDomain domain form nonnegative,
      lifted.val = closedSemigroup domain form nonnegative closable domainDense time target.val ∧
      closedForm domain form nonnegative closable lifted ≤ closedForm domain form nonnegative closable target := by
  let orbit : ℕ → H := fun index =>
    closedSemigroupApproximation domain form nonnegative closable domainDense index time target.val
  let approximations : ℕ → closedDomain domain form nonnegative := fun index =>
    (smallStepLift domain form nonnegative closable domainDense
      (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
      (orbit index)).value
  have orbitLimit : Tendsto orbit atTop
      (nhds (closedSemigroup domain form nonnegative closable domainDense time target.val)) :=
    closedSemigroup_approximation_limit domain form nonnegative closable domainDense time target.val
  have errorBound : ∀ index,
      ‖smallStepResolvent domain form nonnegative closable domainDense
          (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) (orbit index) -
        smallStepResolvent domain form nonnegative closable domainDense
          (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
          (closedSemigroup domain form nonnegative closable domainDense time target.val)‖ ≤
      ‖orbit index - closedSemigroup domain form nonnegative closable domainDense time target.val‖ := by
    intro index
    rw [← map_sub]
    exact smallStepResolvent_norm domain form nonnegative closable domainDense _ _ _ _
  have errorLimit : Tendsto (fun index =>
      smallStepResolvent domain form nonnegative closable domainDense
          (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) (orbit index) -
        smallStepResolvent domain form nonnegative closable domainDense
          (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
          (closedSemigroup domain form nonnegative closable domainDense time target.val)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) errorBound
      (tendsto_iff_norm_sub_tendsto_zero.mp orbitLimit)
  have ambientLimit : Tendsto (fun index => (approximations index : H)) atTop
      (nhds (closedSemigroup domain form nonnegative closable domainDense time target.val)) := by
    have fixedLimit := smallStepResolvent_strong_limit domain form nonnegative closable domainDense
      canonicalYosidaStep canonicalYosidaStep_positive canonicalYosidaStep_le_one canonicalYosidaStep_tendsto
      (closedSemigroup domain form nonnegative closable domainDense time target.val)
    simpa only [sub_add_cancel, zero_add, approximations, smallStepLift_value]
      using errorLimit.add fixedLimit
  have energyBound : ∀ index,
      closedForm domain form nonnegative closable (approximations index) ≤
        closedForm domain form nonnegative closable target := by
    intro index
    simpa only [approximations, orbit, closedSemigroupApproximation] using
      yosidaSmoothed_energy_le_closed_energy domain form nonnegative closable domainDense
        (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
        target (time : ℝ) time.coe_nonneg
  exact closedForm_sublevel_limit domain form nonnegative closable approximations
    (closedSemigroup domain form nonnegative closable domainDense time target.val)
    (closedForm domain form nonnegative closable target)
    (closedForm_nonnegative domain form nonnegative closable target) ambientLimit
      (Eventually.of_forall energyBound)

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_exists_energy_contraction
