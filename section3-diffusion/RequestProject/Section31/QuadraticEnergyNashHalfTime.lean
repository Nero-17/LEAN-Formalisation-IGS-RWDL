import RequestProject.Section31.QuadraticEnergySemigroupSmoothing
import RequestProject.Section31.PositiveL2IntegralContraction

/-! A half-time Nash recurrence for the actual constructed closed semigroup.
It uses its proved positive-time energy bound; no norm derivative of the
unbounded generator or ultracontractive conclusion is assumed. -/

namespace IGS.Sec31.QuadraticEnergySpace

open MeasureTheory Filter Topology
open scoped NNReal
noncomputable section

variable {Space : Type*} [MeasurableSpace Space] (law : Measure Space) [IsFiniteMeasure law]

theorem closedSemigroup_nash_half_time_bound
    (domain : Submodule ℝ (Lp ℝ 2 law)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set (Lp ℝ 2 law)))
    (energyConstant : ℝ) (coefficient : ℝ → ℝ)
    (coefficientNonnegative : ∀ tolerance, 0 < tolerance → 0 ≤ coefficient tolerance)
    (epsilonNash : ∀ (target : closedDomain domain form nonnegative) (tolerance : ℝ),
      0 < tolerance → tolerance ≤ energyConstant →
      ‖target.val‖ ^ 2 ≤ tolerance * closedForm domain form nonnegative closable target +
        coefficient tolerance * (∫ point, |target.val point| ∂law) ^ 2)
    (l1Contraction : ∀ (time : ℝ≥0) (values : Lp ℝ 2 law),
      (∫ point, |closedSemigroup domain form nonnegative closable domainDense time values point| ∂law) ≤
        ∫ point, |values point| ∂law)
    (time : ℝ≥0) (timePositive : 0 < time) (theta : ℝ) (thetaPositive : 0 < theta)
    (toleranceAtMost : theta * (time : ℝ) ≤ energyConstant) (values : Lp ℝ 2 law) :
    ‖closedSemigroup domain form nonnegative closable domainDense time values‖ ^ 2 ≤
      theta * ‖closedSemigroup domain form nonnegative closable domainDense (time / 2) values‖ ^ 2 +
        coefficient (theta * (time : ℝ)) * (∫ point, |values point| ∂law) ^ 2 := by
  have halfPositive : 0 < time / 2 := by positivity
  obtain ⟨lifted, liftedEquality, energyBound⟩ := closedSemigroup_exists_energy_bound domain form nonnegative
    closable domainDense (time / 2) halfPositive
    (closedSemigroup domain form nonnegative closable domainDense (time / 2) values)
  have timeSplit : time / 2 + time / 2 = time := by
    apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat]
    ring
  have liftedTime : lifted.val = closedSemigroup domain form nonnegative closable domainDense time values := by
    rw [liftedEquality, ← ContinuousLinearMap.comp_apply, ← closedSemigroup_add, timeSplit]
  have timeRealPositive : 0 < (time : ℝ) := timePositive
  have tolerancePositive : 0 < theta * (time : ℝ) := mul_pos thetaPositive timeRealPositive
  have bound := epsilonNash lifted (theta * (time : ℝ)) tolerancePositive toleranceAtMost
  rw [liftedTime] at bound
  have normEnergy : theta * (time : ℝ) * closedForm domain form nonnegative closable lifted ≤
      theta * ‖closedSemigroup domain form nonnegative closable domainDense (time / 2) values‖ ^ 2 := by
    have estimate := mul_le_mul_of_nonneg_left energyBound tolerancePositive.le
    have denominator : (2 : ℝ) * ((time / 2 : ℝ≥0) : ℝ) = (time : ℝ) := by
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      ring
    rw [denominator] at estimate
    have cancellation : theta * (time : ℝ) *
        (‖closedSemigroup domain form nonnegative closable domainDense (time / 2) values‖ ^ 2 / (time : ℝ)) =
        theta * ‖closedSemigroup domain form nonnegative closable domainDense (time / 2) values‖ ^ 2 := by
      field_simp [ne_of_gt timeRealPositive]
    simpa only [cancellation] using estimate
  have integralNonnegative : 0 ≤ ∫ point,
      |closedSemigroup domain form nonnegative closable domainDense time values point| ∂law :=
    integral_nonneg (fun _ => abs_nonneg _)
  have integralSquared := mul_self_le_mul_self integralNonnegative (l1Contraction time values)
  have massBound := mul_le_mul_of_nonneg_left integralSquared
    (coefficientNonnegative (theta * (time : ℝ)) tolerancePositive)
  simpa only [← pow_two] using bound.trans (add_le_add normEnergy massBound)

end
end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_nash_half_time_bound
