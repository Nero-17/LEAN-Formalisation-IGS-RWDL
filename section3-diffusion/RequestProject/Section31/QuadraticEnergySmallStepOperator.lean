import RequestProject.Section31.QuadraticEnergySmallStepResolvent

/-! The bounded small-step resolvent and its quantitative approximation on
the actual generator domain. No semigroup existence is assumed. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)

noncomputable def smallStepEquiv :
    generatorDomain domain form nonnegative closable ≃ₗ[ℝ] H :=
  LinearEquiv.ofBijective
    ((generatorDomain domain form nonnegative closable).subtype +
      step • closedGenerator domain form nonnegative closable domainDense)
    ⟨positiveStep_resolvent_injective domain form nonnegative closable domainDense step stepPositive.le,
      smallStep_resolvent_surjective domain form nonnegative closable domainDense step stepPositive stepAtMostOne⟩

theorem smallStepSolution_identity (forcing : H) :
    ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing : H) +
        step • closedGenerator domain form nonnegative closable domainDense
          ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing) =
      forcing :=
  (smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).apply_symm_apply forcing

theorem smallStepSolution_norm (forcing : H) :
    ‖((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing : H)‖ ≤
      ‖forcing‖ := by
  have bound := positiveStep_resolvent_norm_bound domain form nonnegative closable domainDense step stepPositive.le
    ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing)
  rwa [smallStepSolution_identity] at bound

noncomputable def smallStepResolvent : H →L[ℝ] H :=
  ((generatorDomain domain form nonnegative closable).subtype.comp
    (smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm.toLinearMap).mkContinuous 1
    (fun forcing => by simpa only [one_mul] using
      smallStepSolution_norm domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing)

theorem smallStepResolvent_norm (forcing : H) :
    ‖smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing‖ ≤ ‖forcing‖ :=
  smallStepSolution_norm domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing

theorem smallStepResolvent_operator_norm :
    ‖smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro forcing
  simpa only [one_mul] using
    smallStepResolvent_norm domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing

theorem smallStepResolvent_inverse (values : generatorDomain domain form nonnegative closable) :
    smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne
        ((values : H) + step • closedGenerator domain form nonnegative closable domainDense values) =
      (values : H) := by
  exact congrArg (fun point : generatorDomain domain form nonnegative closable => (point : H))
    ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm_apply_apply values)

theorem smallStepResolvent_domain_error (values : generatorDomain domain form nonnegative closable) :
    ‖(values : H) - smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne values‖ ≤
      step * ‖closedGenerator domain form nonnegative closable domainDense values‖ := by
  have identity := smallStepResolvent_inverse domain form nonnegative closable domainDense step stepPositive stepAtMostOne values
  rw [map_add, map_smul] at identity
  have difference : (values : H) -
      smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne values =
      step • smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne
        (closedGenerator domain form nonnegative closable domainDense values) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using identity.symm
  rw [difference, norm_smul, Real.norm_eq_abs, abs_of_pos stepPositive]
  exact mul_le_mul_of_nonneg_left
    (smallStepResolvent_norm domain form nonnegative closable domainDense step stepPositive stepAtMostOne _) stepPositive.le

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.smallStepSolution_identity
#print axioms IGS.Sec31.QuadraticEnergySpace.smallStepResolvent_norm
#print axioms IGS.Sec31.QuadraticEnergySpace.smallStepResolvent_operator_norm
#print axioms IGS.Sec31.QuadraticEnergySpace.smallStepResolvent_inverse
#print axioms IGS.Sec31.QuadraticEnergySpace.smallStepResolvent_domain_error
