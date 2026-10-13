import RequestProject.Section31.QuadraticEnergySmallStepLimit

/-! Actual bounded Yosida generators, their relation to the unbounded
operator, and commutation of all constructed small-step resolvents. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)

noncomputable def yosidaGenerator : H →L[ℝ] H :=
  step⁻¹ • (ContinuousLinearMap.id ℝ H -
    smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne)

theorem yosidaGenerator_eq_closedGenerator (forcing : H) :
    yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing =
      closedGenerator domain form nonnegative closable domainDense
        ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing) := by
  have identity := smallStepSolution_identity domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing
  change smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing +
    step • closedGenerator domain form nonnegative closable domainDense
      ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing) = forcing at identity
  have difference : forcing -
      smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing =
      step • closedGenerator domain form nonnegative closable domainDense
        ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using identity.symm
  change step⁻¹ • (forcing -
    smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing) = _
  rw [difference, smul_smul, inv_mul_cancel₀ (ne_of_gt stepPositive), one_smul]

theorem yosidaGenerator_on_domain (values : generatorDomain domain form nonnegative closable) :
    yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne values =
      smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne
        (closedGenerator domain form nonnegative closable domainDense values) := by
  have identity := smallStepResolvent_inverse domain form nonnegative closable domainDense step stepPositive stepAtMostOne values
  rw [map_add, map_smul] at identity
  have difference : (values : H) -
      smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne values =
      step • smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne
        (closedGenerator domain form nonnegative closable domainDense values) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using identity.symm
  change step⁻¹ • ((values : H) -
    smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne values) = _
  rw [difference, smul_smul, inv_mul_cancel₀ (ne_of_gt stepPositive), one_smul]

theorem smallStepSolution_generator_commute (values : generatorDomain domain form nonnegative closable) :
    closedGenerator domain form nonnegative closable domainDense
        ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm (values : H)) =
      smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne
        (closedGenerator domain form nonnegative closable domainDense values) := by
  rw [← yosidaGenerator_eq_closedGenerator, yosidaGenerator_on_domain]

theorem smallStepResolvent_commute
    (otherStep : ℝ) (otherPositive : 0 < otherStep) (otherAtMostOne : otherStep ≤ 1) :
    Commute
      (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
      (smallStepResolvent domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne) := by
  apply ContinuousLinearMap.ext
  intro forcing
  let otherSolution :=
    (smallStepEquiv domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne).symm forcing
  let firstSolution :=
    (smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm (otherSolution : H)
  have otherEquation := smallStepSolution_identity domain form nonnegative closable domainDense
    otherStep otherPositive otherAtMostOne forcing
  have mappedEquation := congrArg
    (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne) otherEquation
  rw [map_add, map_smul] at mappedEquation
  have commutation := smallStepSolution_generator_commute domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne otherSolution
  change (firstSolution : H) + otherStep •
    smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne
      (closedGenerator domain form nonnegative closable domainDense otherSolution) = _ at mappedEquation
  rw [← commutation] at mappedEquation
  have mappedInverse := congrArg
    (smallStepResolvent domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne) mappedEquation
  change smallStepResolvent domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne
    ((firstSolution : H) + otherStep • closedGenerator domain form nonnegative closable domainDense firstSolution) = _ at mappedInverse
  rw [smallStepResolvent_inverse] at mappedInverse
  exact mappedInverse

theorem yosidaGenerator_on_domain_limit
    (steps : ℕ → ℝ) (stepsPositive : ∀ index, 0 < steps index)
    (stepsAtMostOne : ∀ index, steps index ≤ 1) (stepsLimit : Tendsto steps atTop (nhds 0))
    (values : generatorDomain domain form nonnegative closable) :
    Tendsto (fun index => yosidaGenerator domain form nonnegative closable domainDense
      (steps index) (stepsPositive index) (stepsAtMostOne index) values) atTop
      (nhds (closedGenerator domain form nonnegative closable domainDense values)) := by
  simp_rw [yosidaGenerator_on_domain]
  exact smallStepResolvent_strong_limit domain form nonnegative closable domainDense
    steps stepsPositive stepsAtMostOne stepsLimit _

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaGenerator_eq_closedGenerator
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaGenerator_on_domain
#print axioms IGS.Sec31.QuadraticEnergySpace.smallStepSolution_generator_commute
#print axioms IGS.Sec31.QuadraticEnergySpace.smallStepResolvent_commute
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaGenerator_on_domain_limit
