import RequestProject.Section31.ExponentialClockStrongLaw
import RequestProject.Section31.ExponentialHoldingJumpIndexOrder
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem holdingJumpIndex_tendsto_atTop (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop) :
    Tendsto (holdingJumpIndex holdingTimes) atTop atTop := by
  apply tendsto_atTop.mpr
  intro count
  filter_upwards [eventually_ge_atTop (max 0 (cumulativeHoldingTime holdingTimes count))]
    with time lower
  exact (holdingJumpIndex_ge_iff holdingTimes positive nonexplosion time
    (le_max_left _ _ |>.trans lower) count).mpr (le_max_right _ _ |>.trans lower)

/-- Deterministic inversion of a mean-one nonexplosive waiting-time clock. -/
theorem holdingJumpIndex_clock_ratio (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (average : Tendsto (fun count => cumulativeHoldingTime holdingTimes count / (count : ℝ))
      atTop (𝓝 1)) :
    Tendsto (fun time : ℝ => (holdingJumpIndex holdingTimes time : ℝ) / time) atTop (𝓝 1) := by
  have indexDiverges := holdingJumpIndex_tendsto_atTop holdingTimes positive nonexplosion
  have ratio : Tendsto (fun time : ℝ =>
      ((holdingJumpIndex holdingTimes time + 1 : ℕ) : ℝ) /
        (holdingJumpIndex holdingTimes time : ℝ)) atTop (𝓝 1) := by
    have reciprocal := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp indexDiverges
    have convergence := (tendsto_const_nhds (x := (1 : ℝ))).add reciprocal
    apply (show Tendsto (fun time : ℝ => 1 + 1 / (holdingJumpIndex holdingTimes time : ℝ))
      atTop (𝓝 1) by simpa using convergence).congr'
    filter_upwards [indexDiverges.eventually (eventually_ge_atTop 1)] with time indexPositive
    have nonzero : (holdingJumpIndex holdingTimes time : ℝ) ≠ 0 := by exact_mod_cast (by omega : holdingJumpIndex holdingTimes time ≠ 0)
    push_cast
    field_simp
  have successorDiverges : Tendsto (fun time : ℝ => holdingJumpIndex holdingTimes time + 1)
      atTop atTop := tendsto_atTop_mono (fun _ => Nat.le_succ _) indexDiverges
  have upperConverges := (average.comp successorDiverges).mul ratio
  have timeRatio : Tendsto (fun time : ℝ => time / (holdingJumpIndex holdingTimes time : ℝ))
      atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (average.comp indexDiverges)
      (by simpa using upperConverges)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with time timeNonnegative
      exact div_le_div_of_nonneg_right
        (holdingJumpIndex_interval holdingTimes (fun index => (positive index).le)
          nonexplosion time timeNonnegative).1 (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop (0 : ℝ),
        indexDiverges.eventually (eventually_ge_atTop 1)] with time timeNonnegative indexPositive
      have nonzero : ((holdingJumpIndex holdingTimes time + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      calc
        _ ≤ cumulativeHoldingTime holdingTimes (holdingJumpIndex holdingTimes time + 1) /
            (holdingJumpIndex holdingTimes time : ℝ) :=
          div_le_div_of_nonneg_right
            (holdingJumpIndex_interval holdingTimes (fun index => (positive index).le)
              nonexplosion time timeNonnegative).2.le (Nat.cast_nonneg _)
        _ = _ := by field_simp
  have inverted := timeRatio.inv₀ (by norm_num)
  simpa only [inv_div, inv_one] using inverted

/-- Almost-sure real-time jump-clock law for the actual exponential construction. -/
theorem exponentialHoldingTimeLaw_jump_clock_ratio :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      Tendsto (fun time : ℝ => (holdingJumpIndex holdingTimes time : ℝ) / time) atTop (𝓝 1) := by
  filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion,
    exponentialHoldingTimeLaw_clock_average] with holdingTimes positive nonexplosion average
  exact holdingJumpIndex_clock_ratio holdingTimes positive nonexplosion average

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingJumpIndex_clock_ratio
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingTimeLaw_jump_clock_ratio

