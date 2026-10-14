import RequestProject.Section31.ExponentialHoldingClockUniform

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem holdingJumpClock_uniform_bound (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (tolerance constant acceleration horizon : ℝ)
    (toleranceNonnegative : 0 ≤ tolerance) (toleranceSmall : tolerance < 1)
    (accelerationPositive : 0 < acceleration)
    (error : ∀ count : ℕ, |cumulativeHoldingTime holdingTimes count - (count : ℝ)| ≤
      tolerance * count + constant) (time : ℝ) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    |(holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration - time| ≤
      (tolerance * horizon + (constant + 1 + tolerance) / acceleration) / (1 - tolerance) := by
  have interval := holdingJumpIndex_interval holdingTimes (fun index => (positive index).le)
    nonexplosion (acceleration * time) (mul_nonneg accelerationPositive.le timeNonnegative)
  have firstError := abs_le.mp (error (holdingJumpIndex holdingTimes (acceleration * time)))
  have nextError := abs_le.mp (error (holdingJumpIndex holdingTimes (acceleration * time) + 1))
  simp only [Nat.cast_add, Nat.cast_one] at nextError
  have lowerRaw :
      (1 - tolerance) * (holdingJumpIndex holdingTimes (acceleration * time) : ℝ) ≤
        acceleration * time + constant := by linarith [interval.1, firstError.1]
  have upperRaw : acceleration * time ≤
      (1 + tolerance) * (holdingJumpIndex holdingTimes (acceleration * time) : ℝ) +
        constant + 1 + tolerance := by linarith [interval.2, nextError.2]
  have lower :
      (1 - tolerance) * ((holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration) ≤
        time + constant / acceleration := by
    have divided := div_le_div_of_nonneg_right lowerRaw accelerationPositive.le
    convert divided using 1 <;> (try rfl) <;> (try field_simp [accelerationPositive.ne']) <;> (try ring)
  have upper : time ≤
      (1 + tolerance) * ((holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration) +
        (constant + 1 + tolerance) / acceleration := by
    have divided := div_le_div_of_nonneg_right upperRaw accelerationPositive.le
    convert divided using 1 <;> (try rfl) <;> (try field_simp [accelerationPositive.ne']) <;> (try ring)
  have remainderBound : constant / acceleration ≤ (constant + 1 + tolerance) / acceleration :=
    div_le_div_of_nonneg_right (by linarith) accelerationPositive.le
  have denominatorPositive : 0 < 1 - tolerance := sub_pos.mpr toleranceSmall
  apply abs_le.mpr
  constructor
  · have lowerDifference : time - (holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration ≤
        (tolerance * horizon + (constant + 1 + tolerance) / acceleration) / (1 - tolerance) := by
      apply (le_div_iff₀ denominatorPositive).mpr
      have firstProduct := mul_le_mul_of_nonneg_left lower toleranceNonnegative
      have nextProduct := mul_le_mul_of_nonneg_left upper denominatorPositive.le
      have remainderProduct := mul_le_mul_of_nonneg_left remainderBound toleranceNonnegative
      have horizonProduct := mul_le_mul_of_nonneg_left timeBound toleranceNonnegative
      nlinarith
    linarith
  · apply (le_div_iff₀ denominatorPositive).mpr
    have horizonProduct := mul_le_mul_of_nonneg_left timeBound toleranceNonnegative
    nlinarith

theorem holdingJumpClock_uniform (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (average : Tendsto (fun count => cumulativeHoldingTime holdingTimes count / (count : ℝ))
      atTop (𝓝 1)) (acceleration : ℕ → ℝ)
    (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (accelerationDiverges : Tendsto acceleration atTop atTop)
    (horizon : ℝ) (horizonNonnegative : 0 ≤ horizon) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ time : ℝ,
      0 ≤ time → time ≤ horizon →
      |(holdingJumpIndex holdingTimes (acceleration depth * time) : ℝ) / acceleration depth - time| < tolerance := by
  intro tolerance tolerancePositive
  have smallPositive : 0 < tolerance / (2 * (horizon + tolerance + 1)) := by positivity
  have smallBound : tolerance / (2 * (horizon + tolerance + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨constant, constantNonnegative, error⟩ := cumulativeHoldingTime_affine_error holdingTimes average
    (tolerance / (2 * (horizon + tolerance + 1))) smallPositive
  have remainder := accelerationDiverges.const_div_atTop
    (constant + 1 + tolerance / (2 * (horizon + tolerance + 1)))
  filter_upwards [remainder.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < tolerance / 2))]
    with depth remainderSmall
  intro time timeNonnegative timeBound
  have bound := holdingJumpClock_uniform_bound holdingTimes positive nonexplosion
    (tolerance / (2 * (horizon + tolerance + 1))) constant (acceleration depth) horizon
    smallPositive.le smallBound (accelerationPositive depth) error time timeNonnegative timeBound
  apply bound.trans_lt
  rw [div_lt_iff₀ (sub_pos.mpr smallBound)]
  have smallTimesHorizon :
      tolerance / (2 * (horizon + tolerance + 1)) * (horizon + tolerance) ≤ tolerance / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem exponentialHoldingTimeLaw_jump_clock_uniform :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      ∀ (acceleration : ℕ → ℝ), (∀ depth, 0 < acceleration depth) →
        Tendsto acceleration atTop atTop → ∀ horizon : ℝ, 0 ≤ horizon →
          ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ time : ℝ,
            0 ≤ time → time ≤ horizon →
            |(holdingJumpIndex holdingTimes (acceleration depth * time) : ℝ) /
              acceleration depth - time| < tolerance := by
  filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion,
    exponentialHoldingTimeLaw_clock_average] with holdingTimes positive nonexplosion average
  exact holdingJumpClock_uniform holdingTimes positive nonexplosion average

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingJumpClock_uniform
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingTimeLaw_jump_clock_uniform

