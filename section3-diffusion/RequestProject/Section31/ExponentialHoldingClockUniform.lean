import RequestProject.Section31.ExponentialInverseClockAsymptotics
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem cumulativeHoldingTime_affine_error (holdingTimes : ℕ → ℝ)
    (average : Tendsto (fun count => cumulativeHoldingTime holdingTimes count / (count : ℝ))
      atTop (𝓝 1)) (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ count : ℕ,
      |cumulativeHoldingTime holdingTimes count - (count : ℝ)| ≤ tolerance * count + constant := by
  obtain ⟨threshold, error⟩ := Metric.tendsto_atTop.mp average tolerance tolerancePositive
  refine ⟨∑ count ∈ Finset.range (max threshold 1),
    |cumulativeHoldingTime holdingTimes count - (count : ℝ)|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), fun count => ?_⟩
  by_cases small : count < max threshold 1
  · exact (Finset.single_le_sum (f := fun index =>
      |cumulativeHoldingTime holdingTimes index - (index : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr small)).trans
      (le_add_of_nonneg_left (mul_nonneg tolerancePositive.le (Nat.cast_nonneg count)))
  · have countPositive : 0 < (count : ℝ) := by exact_mod_cast (by omega : 0 < count)
    have approximation := error count (by omega)
    rw [Real.dist_eq] at approximation
    have identity : (cumulativeHoldingTime holdingTimes count / (count : ℝ) - 1) * (count : ℝ) =
        cumulativeHoldingTime holdingTimes count - (count : ℝ) := by field_simp
    rw [← identity, abs_mul, abs_of_pos countPositive]
    exact (mul_le_mul_of_nonneg_right approximation.le countPositive.le).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))

/-- A deterministic uniform estimate for the discrete-to-exponential time change. -/
theorem holdingClock_floor_uniform_bound (holdingTimes : ℕ → ℝ)
    (tolerance constant acceleration horizon : ℝ)
    (toleranceNonnegative : 0 ≤ tolerance) (accelerationPositive : 0 < acceleration)
    (error : ∀ count : ℕ, |cumulativeHoldingTime holdingTimes count - (count : ℝ)| ≤
      tolerance * count + constant) (time : ℝ) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    |cumulativeHoldingTime holdingTimes ⌊acceleration * time⌋₊ / acceleration - time| ≤
      tolerance * horizon + (constant + 1) / acceleration := by
  have floorBound := Nat.floor_le (mul_nonneg accelerationPositive.le timeNonnegative)
  have floorError := Nat.abs_sub_floor_le (mul_nonneg accelerationPositive.le timeNonnegative)
  have approximation := error ⌊acceleration * time⌋₊
  calc
    _ ≤ |(cumulativeHoldingTime holdingTimes ⌊acceleration * time⌋₊ -
        (⌊acceleration * time⌋₊ : ℝ)) / acceleration| +
        |(⌊acceleration * time⌋₊ : ℝ) / acceleration - time| := by
      convert abs_add_le ((cumulativeHoldingTime holdingTimes ⌊acceleration * time⌋₊ -
        (⌊acceleration * time⌋₊ : ℝ)) / acceleration)
        ((⌊acceleration * time⌋₊ : ℝ) / acceleration - time) using 1 <;> congr 1 <;> ring
    _ ≤ (tolerance * (⌊acceleration * time⌋₊ : ℝ) + constant) / acceleration + 1 / acceleration := by
      apply add_le_add
      · rw [abs_div, abs_of_pos accelerationPositive]
        exact div_le_div_of_nonneg_right approximation accelerationPositive.le
      · have identity : (⌊acceleration * time⌋₊ : ℝ) / acceleration - time =
            ((⌊acceleration * time⌋₊ : ℝ) - acceleration * time) / acceleration := by
          field_simp
        rw [identity, abs_div, abs_of_pos accelerationPositive, abs_sub_comm]
        exact div_le_div_of_nonneg_right floorError accelerationPositive.le
    _ ≤ tolerance * horizon + (constant + 1) / acceleration := by
      rw [← add_div, div_le_iff₀ accelerationPositive]
      have scaledBound := mul_le_mul_of_nonneg_left (floorBound.trans
        (mul_le_mul_of_nonneg_left timeBound accelerationPositive.le)) toleranceNonnegative
      field_simp
      nlinarith

/-- The exponential reparametrisation clock tends uniformly to the identity on
every bounded nonnegative time interval, for every diverging positive acceleration. -/
theorem holdingClock_floor_uniform (holdingTimes : ℕ → ℝ)
    (average : Tendsto (fun count => cumulativeHoldingTime holdingTimes count / (count : ℝ))
      atTop (𝓝 1)) (acceleration : ℕ → ℝ)
    (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (accelerationDiverges : Tendsto acceleration atTop atTop)
    (horizon : ℝ) (horizonNonnegative : 0 ≤ horizon) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ time : ℝ,
      0 ≤ time → time ≤ horizon →
      |cumulativeHoldingTime holdingTimes ⌊acceleration depth * time⌋₊ / acceleration depth - time| < tolerance := by
  intro tolerance tolerancePositive
  have smallPositive : 0 < tolerance / (2 * (horizon + 1)) := by positivity
  obtain ⟨constant, constantNonnegative, error⟩ := cumulativeHoldingTime_affine_error
    holdingTimes average (tolerance / (2 * (horizon + 1))) smallPositive
  have remainder := (tendsto_const_nhds (x := constant + 1)).div_atTop accelerationDiverges
  filter_upwards [remainder.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < tolerance / 2))]
    with depth remainderSmall
  intro time timeNonnegative timeBound
  have bound := holdingClock_floor_uniform_bound holdingTimes
    (tolerance / (2 * (horizon + 1))) constant (acceleration depth) horizon
    smallPositive.le (accelerationPositive depth) error time timeNonnegative timeBound
  have toleranceBound : tolerance / (2 * (horizon + 1)) * horizon ≤ tolerance / 2 := by
    have denominatorPositive : 0 < 2 * (horizon + 1) := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ denominatorPositive]
    nlinarith
  exact bound.trans_lt (by linarith)

theorem exponentialHoldingTimeLaw_floor_clock_uniform :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      ∀ (acceleration : ℕ → ℝ), (∀ depth, 0 < acceleration depth) →
        Tendsto acceleration atTop atTop → ∀ horizon : ℝ, 0 ≤ horizon →
          ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ time : ℝ,
            0 ≤ time → time ≤ horizon →
            |cumulativeHoldingTime holdingTimes ⌊acceleration depth * time⌋₊ /
              acceleration depth - time| < tolerance := by
  filter_upwards [exponentialHoldingTimeLaw_clock_average] with holdingTimes average
  exact holdingClock_floor_uniform holdingTimes average

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingClock_floor_uniform
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingTimeLaw_floor_clock_uniform

