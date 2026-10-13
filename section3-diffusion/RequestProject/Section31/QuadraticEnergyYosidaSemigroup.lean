import RequestProject.Section31.QuadraticEnergyYosida
import RequestProject.Section31.BoundedYosidaSemigroup

/-! The bounded exponential approximations attached to the actual closed
form, including the commutation needed for their strong-limit construction. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)

noncomputable def yosidaSemigroup (time : ℝ) : H →L[ℝ] H :=
  BoundedYosida.semigroup
    (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne) step time

theorem yosidaSemigroup_eq_exp (time : ℝ) :
    yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time =
      NormedSpace.exp ((-time) • yosidaGenerator domain form nonnegative closable domainDense
        step stepPositive stepAtMostOne) := rfl

theorem yosidaGenerator_commute
    (otherStep : ℝ) (otherPositive : 0 < otherStep) (otherAtMostOne : otherStep ≤ 1) :
    Commute
      (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
      (yosidaGenerator domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne) := by
  have commuting := smallStepResolvent_commute domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne otherStep otherPositive otherAtMostOne
  have differencesCommute : Commute
      (1 - smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
      (1 - smallStepResolvent domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne) :=
    (Commute.one_left _).sub_left ((Commute.one_right _).sub_right commuting)
  exact (differencesCommute.smul_left step⁻¹).smul_right otherStep⁻¹

theorem yosidaSemigroup_norm (time : ℝ) (timeNonnegative : 0 ≤ time) :
    ‖yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time‖ ≤ 1 :=
  BoundedYosida.semigroup_norm_le_one _
    (smallStepResolvent_operator_norm domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    step stepPositive time timeNonnegative

theorem yosidaSemigroup_apply_norm (time : ℝ) (timeNonnegative : 0 ≤ time) (values : H) :
    ‖yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time values‖ ≤ ‖values‖ :=
  BoundedYosida.semigroup_apply_norm_le _
    (smallStepResolvent_operator_norm domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    step stepPositive time timeNonnegative values

@[simp] theorem yosidaSemigroup_zero :
    yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne 0 = 1 :=
  BoundedYosida.semigroup_zero _ _

theorem yosidaSemigroup_add (firstTime secondTime : ℝ) :
    yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne (firstTime + secondTime) =
      yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne firstTime *
      yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne secondTime :=
  BoundedYosida.semigroup_add _ _ _ _

theorem yosidaSemigroup_continuous :
    Continuous (yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne) :=
  BoundedYosida.semigroup_continuous _ _

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaGenerator_commute
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSemigroup_norm
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSemigroup_apply_norm
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSemigroup_zero
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSemigroup_add
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSemigroup_continuous
