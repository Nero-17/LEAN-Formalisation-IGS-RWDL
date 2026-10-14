import RequestProject.Section31.QuadraticEnergySemigroupPointIncrement

/-! A genuine semigroup increment estimate applied to a constructed cutoff
forces a Riesz evaluation row to have large norm. Only the cutoff value,
norm and energy estimates and the Riesz representation remain generic inputs;
closeness of the semigroup to the cutoff is proved internally. The scalar
scale choice gives a later power-law consumer without diagonal monotonicity. -/

namespace IGS.Sec31

theorem geometric_cutoff_lower_scale_choice
    (timeRate growthRate exponent cutoffTime time : ℝ)
    (timeRateGreaterThanOne : 1 < timeRate)
    (exponentNonnegative : 0 ≤ exponent)
    (growthIdentity : growthRate = timeRate ^ exponent)
    (timePositive : 0 < time) (timeAtMostCutoff : time ≤ cutoffTime) :
    ∃ level : ℕ, time ≤ cutoffTime / timeRate ^ level ∧
      (cutoffTime / (timeRate * time)) ^ exponent ≤ growthRate ^ level := by
  have timeRatePositive : 0 < timeRate := zero_lt_one.trans timeRateGreaterThanOne
  obtain ⟨level, lower, upper⟩ := exists_nat_pow_near
    ((one_le_div timePositive).mpr timeAtMostCutoff) timeRateGreaterThanOne
  refine ⟨level, ?_, ?_⟩
  · apply (le_div_iff₀ (pow_pos timeRatePositive level)).mpr
    have multiplied := (le_div_iff₀ timePositive).mp lower
    nlinarith
  · have lowerScale : cutoffTime / (timeRate * time) ≤ timeRate ^ level := by
      apply (div_le_iff₀ (mul_pos timeRatePositive timePositive)).mpr
      have multiplied := (div_lt_iff₀ timePositive).mp upper
      rw [pow_succ] at multiplied
      nlinarith
    calc
      (cutoffTime / (timeRate * time)) ^ exponent ≤ (timeRate ^ level) ^ exponent :=
        Real.rpow_le_rpow (div_nonneg (timePositive.le.trans timeAtMostCutoff)
          (mul_pos timeRatePositive timePositive).le) lowerScale exponentNonnegative
      _ = growthRate ^ level := by
        rw [growthIdentity, ← Real.rpow_natCast_mul timeRatePositive.le,
          mul_comm (level : ℝ) exponent, Real.rpow_mul_natCast timeRatePositive.le]

end IGS.Sec31

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNReal
noncomputable section
set_option maxHeartbeats 5000000

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]

theorem closedSemigroup_rieszRow_norm_sq_lower_at_cutoff_scale
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
    (cutoffNormConstant cutoffEnergyConstant cutoffTime : ℝ)
    (cutoffNormPositive : 0 < cutoffNormConstant) (cutoffEnergyNonnegative : 0 ≤ cutoffEnergyConstant)
    (cutoffTimePositive : 0 < cutoffTime)
    (smallTimeBound : ((2 * normConstant + 4 * energyConstant) * growthRate) * cutoffEnergyConstant *
      cutoffTime ^ (1 - exponent) ≤ (1 / 4 : ℝ))
    (level : ℕ) (cutoff : closedDomain domain form nonnegative)
    (cutoffValue : evaluation cutoff = 1)
    (cutoffNormBound : ‖cutoff.val‖ ^ 2 ≤ cutoffNormConstant / growthRate ^ level)
    (cutoffEnergyBound : closedForm domain form nonnegative closable cutoff ≤
      cutoffEnergyConstant * decayRate ^ level)
    (time : ℝ≥0) (timePositive : 0 < (time : ℝ)) (timeAtMostOne : (time : ℝ) ≤ 1)
    (timeAtScale : (time : ℝ) ≤ cutoffTime / timeRate ^ level)
    (row : Hilbert)
    (rowRepresents : ∀ lifted : closedDomain domain form nonnegative,
      lifted.val = closedSemigroup domain form nonnegative closable domainDense time cutoff.val →
        evaluation lifted = inner ℝ row cutoff.val) :
    growthRate ^ level / (4 * cutoffNormConstant) ≤ ‖row‖ ^ 2 := by
  obtain ⟨lifted, liftedAgreement, _, incrementBound⟩ := closedSemigroup_exists_point_energy_increment
    domain form nonnegative closable domainDense evaluation timeRate growthRate decayRate exponent
    normConstant energyConstant timeRateGreaterThanOne growthPositive decayPositive timeScaleIdentity
    exponentNonnegative exponentStrict growthIdentity normNonnegative energyNonnegative pointBounds
    time timePositive timeAtMostOne cutoff
  have timeRatePositive : 0 < timeRate := zero_lt_one.trans timeRateGreaterThanOne
  have holderExponentNonnegative : 0 ≤ 1 - exponent := (sub_pos.mpr exponentStrict).le
  have decayIdentity : decayRate = timeRate ^ (1 - exponent) := by
    rw [Real.rpow_sub timeRatePositive 1 exponent, Real.rpow_one, ← growthIdentity]
    apply (eq_div_iff growthPositive.ne').mpr
    rw [timeScaleIdentity]
    ring
  have decayPowerIdentity : decayRate ^ level = (timeRate ^ level) ^ (1 - exponent) := by
    rw [decayIdentity, ← Real.rpow_mul_natCast timeRatePositive.le,
      mul_comm (1 - exponent) (level : ℝ), Real.rpow_natCast_mul timeRatePositive.le]
  have scaledTimeBound : (time : ℝ) ^ (1 - exponent) * decayRate ^ level ≤
      cutoffTime ^ (1 - exponent) := by
    rw [decayPowerIdentity, ← Real.mul_rpow time.coe_nonneg (pow_pos timeRatePositive level).le]
    exact Real.rpow_le_rpow (mul_nonneg time.coe_nonneg (pow_pos timeRatePositive level).le)
      ((le_div_iff₀ (pow_pos timeRatePositive level)).mp timeAtScale) holderExponentNonnegative
  have pointCoefficientNonnegative : 0 ≤ (2 * normConstant + 4 * energyConstant) * growthRate :=
    mul_nonneg (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) normNonnegative)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) energyNonnegative)) growthPositive.le
  have multipliedEnergyBound :
      ((2 * normConstant + 4 * energyConstant) * growthRate) * (time : ℝ) ^ (1 - exponent) *
          closedForm domain form nonnegative closable cutoff ≤
        ((2 * normConstant + 4 * energyConstant) * growthRate) * (time : ℝ) ^ (1 - exponent) *
          (cutoffEnergyConstant * decayRate ^ level) :=
    mul_le_mul_of_nonneg_left cutoffEnergyBound
      (mul_nonneg pointCoefficientNonnegative (Real.rpow_nonneg time.coe_nonneg (1 - exponent)))
  have multipliedTimeBound :
      (((2 * normConstant + 4 * energyConstant) * growthRate) * cutoffEnergyConstant) *
          ((time : ℝ) ^ (1 - exponent) * decayRate ^ level) ≤
        (((2 * normConstant + 4 * energyConstant) * growthRate) * cutoffEnergyConstant) *
          cutoffTime ^ (1 - exponent) :=
    mul_le_mul_of_nonneg_left scaledTimeBound
      (mul_nonneg pointCoefficientNonnegative cutoffEnergyNonnegative)
  have quarterIncrement : |evaluation lifted - evaluation cutoff| ^ 2 ≤ (1 / 4 : ℝ) := by
    apply incrementBound.trans
    calc
      ((2 * normConstant + 4 * energyConstant) * growthRate) * (time : ℝ) ^ (1 - exponent) *
          closedForm domain form nonnegative closable cutoff ≤
        ((2 * normConstant + 4 * energyConstant) * growthRate) * (time : ℝ) ^ (1 - exponent) *
          (cutoffEnergyConstant * decayRate ^ level) := multipliedEnergyBound
      _ = (((2 * normConstant + 4 * energyConstant) * growthRate) * cutoffEnergyConstant) *
          ((time : ℝ) ^ (1 - exponent) * decayRate ^ level) := by ring
      _ ≤ (((2 * normConstant + 4 * energyConstant) * growthRate) * cutoffEnergyConstant) *
          cutoffTime ^ (1 - exponent) := multipliedTimeBound
      _ ≤ (1 / 4 : ℝ) := smallTimeBound
  rw [cutoffValue, sq_abs] at quarterIncrement
  have evaluatedLower : (1 / 2 : ℝ) ≤ evaluation lifted := by nlinarith
  have cauchy := real_inner_mul_inner_self_le row cutoff.val
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    ← rowRepresents lifted liftedAgreement] at cauchy
  have quarterRowBound : (1 / 4 : ℝ) ≤ ‖row‖ ^ 2 * (cutoffNormConstant / growthRate ^ level) := by
    calc
      (1 / 4 : ℝ) ≤ evaluation lifted ^ 2 := by nlinarith
      _ ≤ ‖row‖ ^ 2 * ‖cutoff.val‖ ^ 2 := by nlinarith
      _ ≤ ‖row‖ ^ 2 * (cutoffNormConstant / growthRate ^ level) :=
        mul_le_mul_of_nonneg_left cutoffNormBound (sq_nonneg _)
  have quotientRowBound : (1 / 4 : ℝ) ≤ (‖row‖ ^ 2 * cutoffNormConstant) / growthRate ^ level := by
    simpa only [mul_div_assoc] using quarterRowBound
  have productRowBound := (le_div_iff₀ (pow_pos growthPositive level)).mp quotientRowBound
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) cutoffNormPositive)).mpr
  nlinarith

end
end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.geometric_cutoff_lower_scale_choice
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_rieszRow_norm_sq_lower_at_cutoff_scale
