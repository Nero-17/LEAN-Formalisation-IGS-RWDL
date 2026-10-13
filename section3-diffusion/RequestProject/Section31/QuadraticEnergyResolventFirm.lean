import RequestProject.Section31.QuadraticEnergyResolvent

/-! Positivity and the complementary contraction estimate for the actual
unit resolvent, directly from its variational energy identity. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)

theorem resolvent_firm (forcing : H) :
    ‖resolventState domain form nonnegative closable forcing‖ ^ 2 ≤
      inner ℝ forcing (resolventState domain form nonnegative closable forcing) := by
  have identity := resolvent_energy_identity domain form nonnegative closable forcing
  have energyNonnegative := closedForm_nonnegative domain form nonnegative closable
    (resolventLift domain form nonnegative closable forcing).value
  linarith

theorem resolvent_inner_nonnegative (forcing : H) :
    0 ≤ inner ℝ forcing (resolventState domain form nonnegative closable forcing) :=
  (sq_nonneg _).trans (resolvent_firm domain form nonnegative closable forcing)

theorem identity_sub_resolvent_norm_le (forcing : H) :
    ‖forcing - resolventState domain form nonnegative closable forcing‖ ≤ ‖forcing‖ := by
  have bound := resolvent_firm domain form nonnegative closable forcing
  have expansion := norm_sub_sq_real forcing (resolventState domain form nonnegative closable forcing)
  nlinarith [norm_nonneg (forcing - resolventState domain form nonnegative closable forcing),
    norm_nonneg forcing, sq_nonneg ‖resolventState domain form nonnegative closable forcing‖]

theorem identity_sub_resolvent_operator_norm_le :
    ‖ContinuousLinearMap.id ℝ H - resolventState domain form nonnegative closable‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro forcing
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, one_mul] using
    identity_sub_resolvent_norm_le domain form nonnegative closable forcing

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.resolvent_firm
#print axioms IGS.Sec31.QuadraticEnergySpace.resolvent_inner_nonnegative
#print axioms IGS.Sec31.QuadraticEnergySpace.identity_sub_resolvent_norm_le
#print axioms IGS.Sec31.QuadraticEnergySpace.identity_sub_resolvent_operator_norm_le
