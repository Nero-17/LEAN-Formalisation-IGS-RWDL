import RequestProject.Section31.BoundedSemigroupDerivativeBound
import RequestProject.Section31.QuadraticEnergyYosidaEnergy

/-! The uniform first-derivative estimate for the actual closed-form Yosida
operators. Positivity of these generators is proved from the actual closed
energy comparison; it is not an additional model premise. Candidate source:
whole-file compilation has not yet been requested or completed. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)

theorem yosidaGenerator_pairing_nonnegative (forcing : H) :
    0 ≤ inner ℝ (yosidaGenerator domain form nonnegative closable domainDense
      step stepPositive stepAtMostOne forcing) forcing := by
  exact (closedForm_nonnegative domain form nonnegative closable
    (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value).trans
    (smallStepLift_energy_le_yosida_pairing domain form nonnegative closable domainDense
      step stepPositive stepAtMostOne forcing)

theorem yosidaGenerator_semigroup_apply_norm_le (forcing : H)
    (time : ℝ) (timePositive : 0 < time) :
    ‖yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne
      (yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time forcing)‖ ≤
        ‖forcing‖ / time := by
  rw [yosidaSemigroup_eq_exp]
  exact BoundedSemigroupEnergy.generator_exp_apply_norm_le _
    (yosidaGenerator_selfAdjoint domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    (yosidaGenerator_pairing_nonnegative domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    forcing time timePositive

theorem yosidaGenerator_semigroup_norm_le
    (time : ℝ) (timePositive : 0 < time) :
    ‖yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne *
      yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time‖ ≤ time⁻¹ := by
  rw [yosidaSemigroup_eq_exp]
  exact BoundedSemigroupEnergy.generator_exp_norm_le _
    (yosidaGenerator_selfAdjoint domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    (yosidaGenerator_pairing_nonnegative domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    time timePositive

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaGenerator_pairing_nonnegative
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaGenerator_semigroup_apply_norm_le
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaGenerator_semigroup_norm_le
