import RequestProject.Section31.QuadraticEnergySemigroupEnergyIncrement
import RequestProject.Section31.QuadraticEnergySemigroupFormContraction
import RequestProject.Section31.NashTwoScaleOptimization

/-! A full-scale closed-domain point estimate controls the actual constructed
semigroup increment at that point. The ambient increment and closed-energy
contraction are invoked from their constructions, not supplied as hypotheses.
The same closed-domain lift is used for the evaluation and its difference.
No spectral representation is required. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNReal
noncomputable section
set_option maxHeartbeats 4000000

theorem nonnegative_quadraticForm_sub_le
    {Vector : Type*} [AddCommGroup Vector] [Module ℝ Vector]
    (form : QuadraticForm ℝ Vector) (nonnegative : ∀ values, 0 ≤ form values)
    (first second : Vector) : form (first - second) ≤ 2 * form first + 2 * form second := by
  obtain ⟨companion, companionIdentity⟩ := form.exists_companion
  have sumIdentity := companionIdentity first second
  have differenceIdentity := companionIdentity first (-second)
  simp only [← sub_eq_add_neg, QuadraticMap.map_neg, map_neg] at differenceIdentity
  have sumNonnegative := nonnegative (first + second)
  linarith

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]

theorem closedSemigroup_exists_point_energy_increment
    (domain : Submodule ℝ Hilbert) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set Hilbert))
    (evaluation : closedDomain domain form nonnegative →ₗ[ℝ] ℝ)
    (timeRate growthRate decayRate exponent normConstant energyConstant : ℝ)
    (timeRateGreaterThanOne : 1 < timeRate)
    (growthPositive : 0 < growthRate) (decayPositive : 0 < decayRate)
    (timeScaleIdentity : timeRate = growthRate * decayRate)
    (exponentNonnegative : 0 ≤ exponent) (exponentStrict : exponent < 1)
    (growthIdentity : growthRate = timeRate ^ exponent)
    (normNonnegative : 0 ≤ normConstant) (energyNonnegative : 0 ≤ energyConstant)
    (pointBounds : ∀ (values : closedDomain domain form nonnegative) (level : ℕ),
      evaluation values ^ 2 ≤ normConstant * growthRate ^ level * ‖values.val‖ ^ 2 +
        energyConstant / decayRate ^ level * closedForm domain form nonnegative closable values)
    (time : ℝ≥0) (timePositive : 0 < (time : ℝ)) (timeAtMostOne : (time : ℝ) ≤ 1)
    (target : closedDomain domain form nonnegative) :
    ∃ lifted : closedDomain domain form nonnegative,
      lifted.val = closedSemigroup domain form nonnegative closable domainDense time target.val ∧
      closedForm domain form nonnegative closable lifted ≤ closedForm domain form nonnegative closable target ∧
      |evaluation lifted - evaluation target| ^ 2 ≤
        ((2 * normConstant + 4 * energyConstant) * growthRate) *
          (time : ℝ) ^ (1 - exponent) * closedForm domain form nonnegative closable target := by
  obtain ⟨lifted, liftedAgreement, liftedEnergyBound⟩ :=
    closedSemigroup_exists_energy_contraction domain form nonnegative closable domainDense time target
  refine ⟨lifted, liftedAgreement, liftedEnergyBound, ?_⟩
  have initialEnergyNonnegative := closedForm_nonnegative domain form nonnegative closable target
  have differenceEnergyBound : closedForm domain form nonnegative closable (lifted - target) ≤
      4 * closedForm domain form nonnegative closable target := by
    have differenceBound := nonnegative_quadraticForm_sub_le
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable) lifted target
    linarith
  have ambientIncrementBound : ‖(lifted - target).val‖ ^ 2 ≤
      2 * (time : ℝ) * closedForm domain form nonnegative closable target := by
    simpa only [Submodule.coe_sub, liftedAgreement] using
      closedSemigroup_energy_increment_sq_le domain form nonnegative closable domainDense time target
  obtain ⟨level, timeBound, growthBound⟩ := IGS.Sec31.geometric_two_scale_choice
    timeRate growthRate exponent 1 (time : ℝ) timeRateGreaterThanOne exponentNonnegative
    growthIdentity (by norm_num) timePositive timeAtMostOne
  have timeRatePositive : 0 < timeRate := zero_lt_one.trans timeRateGreaterThanOne
  have reciprocalScaleBound : 1 / decayRate ^ level ≤ (time : ℝ) * growthRate ^ level := by
    apply (div_le_iff₀ (pow_pos decayPositive level)).mpr
    have productScaleBound : 1 ≤ (time : ℝ) * timeRate ^ level :=
      (div_le_iff₀ (pow_pos timeRatePositive level)).mp timeBound
    calc
      1 ≤ (time : ℝ) * timeRate ^ level := productScaleBound
      _ = ((time : ℝ) * growthRate ^ level) * decayRate ^ level := by
        rw [timeScaleIdentity, mul_pow]
        ring
  have scaledGrowthBound : (time : ℝ) * growthRate ^ level ≤
      growthRate * (time : ℝ) ^ (1 - exponent) := by
    calc
      (time : ℝ) * growthRate ^ level ≤ (time : ℝ) * (timeRate * 1 / (time : ℝ)) ^ exponent :=
        mul_le_mul_of_nonneg_left growthBound time.coe_nonneg
      _ = growthRate * (time : ℝ) ^ (1 - exponent) := by
        rw [mul_one, Real.div_rpow timeRatePositive.le timePositive.le, ← growthIdentity,
          Real.rpow_sub timePositive 1 exponent, Real.rpow_one]
        ring
  have pointBound := pointBounds (lifted - target) level
  rw [map_sub] at pointBound
  have normTermBound := mul_le_mul_of_nonneg_left ambientIncrementBound
    (mul_nonneg normNonnegative (pow_pos growthPositive level).le)
  have energyTermBound := mul_le_mul_of_nonneg_left differenceEnergyBound
    (div_nonneg energyNonnegative (pow_pos decayPositive level).le)
  have combinedBound : (evaluation lifted - evaluation target) ^ 2 ≤
      (2 * normConstant * (time : ℝ) * growthRate ^ level +
        4 * energyConstant / decayRate ^ level) *
          closedForm domain form nonnegative closable target := by
    exact (pointBound.trans (add_le_add normTermBound energyTermBound)).trans_eq (by ring)
  have reciprocalTermBound := mul_le_mul_of_nonneg_left reciprocalScaleBound
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) energyNonnegative)
  have coefficientBound : 2 * normConstant * (time : ℝ) * growthRate ^ level +
      4 * energyConstant / decayRate ^ level ≤
        (2 * normConstant + 4 * energyConstant) * ((time : ℝ) * growthRate ^ level) := by
    simp only [mul_one_div] at reciprocalTermBound
    nlinarith
  have exponentCoefficientBound := mul_le_mul_of_nonneg_left scaledGrowthBound
    (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) normNonnegative)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) energyNonnegative))
  rw [sq_abs]
  exact (combinedBound.trans (mul_le_mul_of_nonneg_right coefficientBound initialEnergyNonnegative)).trans
    ((mul_le_mul_of_nonneg_right exponentCoefficientBound initialEnergyNonnegative).trans_eq (by ring))

end
end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.nonnegative_quadraticForm_sub_le
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_exists_point_energy_increment
