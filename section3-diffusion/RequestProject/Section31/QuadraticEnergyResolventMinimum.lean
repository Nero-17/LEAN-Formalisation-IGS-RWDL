import RequestProject.Section31.QuadraticEnergyResolvent

/-! The actual resolvent is the unique minimizer of closed energy plus squared
distance to the forcing, with an exact energy-space remainder. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)

theorem resolvent_minimum_gap (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)) :
    closedForm domain form nonnegative closable test.value + ‖(test.value : H) - forcing‖ ^ 2 =
      closedForm domain form nonnegative closable (resolventLift domain form nonnegative closable forcing).value +
        ‖resolventState domain form nonnegative closable forcing - forcing‖ ^ 2 +
          ‖test - resolventLift domain form nonnegative closable forcing‖ ^ 2 := by
  have testNorm := norm_sq (closedDomain domain form nonnegative)
    (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable) test
  have solutionNorm := norm_sq (closedDomain domain form nonnegative)
    (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)
    (resolventLift domain form nonnegative closable forcing)
  have pairing := resolvent_variational domain form nonnegative closable forcing test
  change inner ℝ (resolventLift domain form nonnegative closable forcing) test =
    inner ℝ forcing (test.value : H) at pairing
  have solutionPairing := resolvent_variational domain form nonnegative closable forcing
    (resolventLift domain form nonnegative closable forcing)
  change inner ℝ (resolventLift domain form nonnegative closable forcing)
      (resolventLift domain form nonnegative closable forcing) =
    inner ℝ forcing (resolventState domain form nonnegative closable forcing) at solutionPairing
  rw [real_inner_self_eq_norm_sq] at solutionPairing
  change ‖resolventLift domain form nonnegative closable forcing‖ ^ 2 =
    _ + ‖resolventState domain form nonnegative closable forcing‖ ^ 2 at solutionNorm
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real,
    real_inner_comm forcing (test.value : H),
    real_inner_comm forcing (resolventState domain form nonnegative closable forcing),
    real_inner_comm (resolventLift domain form nonnegative closable forcing) test, pairing]
  linarith

theorem resolvent_minimizes (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)) :
    closedForm domain form nonnegative closable (resolventLift domain form nonnegative closable forcing).value +
      ‖resolventState domain form nonnegative closable forcing - forcing‖ ^ 2 ≤
        closedForm domain form nonnegative closable test.value + ‖(test.value : H) - forcing‖ ^ 2 := by
  rw [resolvent_minimum_gap]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem resolvent_minimizer_unique (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable))
    (minimal : closedForm domain form nonnegative closable test.value + ‖(test.value : H) - forcing‖ ^ 2 ≤
      closedForm domain form nonnegative closable (resolventLift domain form nonnegative closable forcing).value +
        ‖resolventState domain form nonnegative closable forcing - forcing‖ ^ 2) :
    test = resolventLift domain form nonnegative closable forcing := by
  rw [resolvent_minimum_gap] at minimal
  have zero : ‖test - resolventLift domain form nonnegative closable forcing‖ = 0 := by
    nlinarith [norm_nonneg (test - resolventLift domain form nonnegative closable forcing)]
  exact sub_eq_zero.mp (norm_eq_zero.mp zero)

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.resolvent_minimum_gap
#print axioms IGS.Sec31.QuadraticEnergySpace.resolvent_minimizes
#print axioms IGS.Sec31.QuadraticEnergySpace.resolvent_minimizer_unique
