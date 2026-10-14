import RequestProject.Section31.ExponentialInverseClockUniform
import RequestProject.Section31.ExponentialHoldingJumpIndexOrder

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem holdingJumpIndex_monotone (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (first last : ℝ) (firstNonnegative : 0 ≤ first) (ordered : first ≤ last) :
    holdingJumpIndex holdingTimes first ≤ holdingJumpIndex holdingTimes last := by
  apply (holdingJumpIndex_ge_iff holdingTimes positive nonexplosion last
    (firstNonnegative.trans ordered) _).mpr
  exact (holdingJumpIndex_interval holdingTimes (fun index => (positive index).le)
    nonexplosion first firstNonnegative).1.trans ordered

theorem scaled_jump_window_count_le (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (acceleration first last error : ℝ) (accelerationPositive : 0 < acceleration)
    (firstNonnegative : 0 ≤ first) (ordered : first ≤ last)
    (firstError : |(holdingJumpIndex holdingTimes (acceleration * first) : ℝ) / acceleration - first| ≤ error)
    (lastError : |(holdingJumpIndex holdingTimes (acceleration * last) : ℝ) / acceleration - last| ≤ error) :
    ((holdingJumpIndex holdingTimes (acceleration * last) -
      holdingJumpIndex holdingTimes (acceleration * first) : ℕ) : ℝ) ≤
        acceleration * (last - first + 2 * error) := by
  have indicesOrdered := holdingJumpIndex_monotone holdingTimes positive nonexplosion
    (acceleration * first) (acceleration * last) (mul_nonneg accelerationPositive.le firstNonnegative)
    (mul_le_mul_of_nonneg_left ordered accelerationPositive.le)
  rw [Nat.cast_sub indicesOrdered]
  have lower := (abs_le.mp firstError).1
  have upper := (abs_le.mp lastError).2
  have divided : (holdingJumpIndex holdingTimes (acceleration * last) : ℝ) / acceleration -
      (holdingJumpIndex holdingTimes (acceleration * first) : ℝ) / acceleration ≤ last - first + 2 * error := by
    linarith
  rw [← sub_div] at divided
  simpa only [mul_comm] using (div_le_iff₀ accelerationPositive).mp divided

theorem holdingTimePath_escape_in_jump_window
    {Space : Type*} [PseudoMetricSpace Space] (trajectory : ℕ → Space) (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (acceleration first last radius : ℝ) (accelerationPositive : 0 < acceleration)
    (firstNonnegative : 0 ≤ first) (ordered : first ≤ last) (window : ℕ)
    (countBound : holdingJumpIndex holdingTimes (acceleration * last) -
      holdingJumpIndex holdingTimes (acceleration * first) ≤ window)
    (escape : ∃ time, first ≤ time ∧ time ≤ last ∧
      radius < dist (holdingTimePath trajectory holdingTimes (acceleration * time))
        (holdingTimePath trajectory holdingTimes (acceleration * first))) :
    ∃ offset ≤ window, radius < dist
      (trajectory (holdingJumpIndex holdingTimes (acceleration * first) + offset))
      (trajectory (holdingJumpIndex holdingTimes (acceleration * first))) := by
  obtain ⟨time, after, before, escaped⟩ := escape
  have firstIndex := holdingJumpIndex_monotone holdingTimes positive nonexplosion
    (acceleration * first) (acceleration * time) (mul_nonneg accelerationPositive.le firstNonnegative)
    (mul_le_mul_of_nonneg_left after accelerationPositive.le)
  have lastIndex := holdingJumpIndex_monotone holdingTimes positive nonexplosion
    (acceleration * time) (acceleration * last) (mul_nonneg accelerationPositive.le (firstNonnegative.trans after))
    (mul_le_mul_of_nonneg_left before accelerationPositive.le)
  refine ⟨holdingJumpIndex holdingTimes (acceleration * time) -
    holdingJumpIndex holdingTimes (acceleration * first), (Nat.sub_le_sub_right lastIndex _).trans countBound, ?_⟩
  simpa only [Nat.add_sub_cancel' firstIndex, holdingTimePath] using escaped

theorem holdingTimePath_modulus_transfer
    {Space : Type*} [PseudoMetricSpace Space] (trajectory : ℕ → Space) (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (acceleration horizon duration error tolerance : ℝ) (accelerationPositive : 0 < acceleration)
    (clockError : ∀ time, 0 ≤ time → time ≤ horizon →
      |(holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration - time| ≤ error)
    (discreteModulus : ∀ first last : ℕ, first ≤ last →
      last ≤ holdingJumpIndex holdingTimes (acceleration * horizon) →
      ((last - first : ℕ) : ℝ) ≤ acceleration * (duration + 2 * error) →
      dist (trajectory last) (trajectory first) ≤ tolerance)
    (first last : ℝ) (firstNonnegative : 0 ≤ first) (ordered : first ≤ last)
    (lastBound : last ≤ horizon) (durationBound : last - first ≤ duration) :
    dist (holdingTimePath trajectory holdingTimes (acceleration * last))
      (holdingTimePath trajectory holdingTimes (acceleration * first)) ≤ tolerance := by
  apply discreteModulus
  · exact holdingJumpIndex_monotone holdingTimes positive nonexplosion _ _
      (mul_nonneg accelerationPositive.le firstNonnegative) (mul_le_mul_of_nonneg_left ordered accelerationPositive.le)
  · exact holdingJumpIndex_monotone holdingTimes positive nonexplosion _ _
      (mul_nonneg accelerationPositive.le (firstNonnegative.trans ordered))
      (mul_le_mul_of_nonneg_left lastBound accelerationPositive.le)
  · exact (scaled_jump_window_count_le holdingTimes positive nonexplosion acceleration first last error
      accelerationPositive firstNonnegative ordered (clockError first firstNonnegative (ordered.trans lastBound))
      (clockError last (firstNonnegative.trans ordered) lastBound)).trans
      (mul_le_mul_of_nonneg_left (by linarith) accelerationPositive.le)

theorem exponential_clock_ae_window_count_bounds :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      ∀ acceleration : ℕ → ℝ, (∀ depth, 0 < acceleration depth) →
        Tendsto acceleration atTop atTop → ∀ horizon error : ℝ, 0 ≤ horizon → 0 < error →
          ∀ᶠ depth in atTop, ∀ first last : ℝ, 0 ≤ first → first ≤ last → last ≤ horizon →
            ((holdingJumpIndex holdingTimes (acceleration depth * last) -
              holdingJumpIndex holdingTimes (acceleration depth * first) : ℕ) : ℝ) ≤
                acceleration depth * (last - first + 2 * error) := by
  filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion,
    exponentialHoldingTimeLaw_jump_clock_uniform] with holdingTimes positive nonexplosion uniform
  intro acceleration accelerationPositive diverge horizon error horizonNonnegative errorPositive
  filter_upwards [uniform acceleration accelerationPositive diverge horizon horizonNonnegative error errorPositive]
    with depth bounds
  intro first last firstNonnegative ordered lastBound
  exact scaled_jump_window_count_le holdingTimes positive nonexplosion
    (acceleration depth) first last error (accelerationPositive depth) firstNonnegative ordered
    (bounds first firstNonnegative (ordered.trans lastBound)).le
    (bounds last (firstNonnegative.trans ordered) lastBound).le

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingJumpIndex_monotone
#print axioms IGS.Sec31.PoissonClock.scaled_jump_window_count_le
#print axioms IGS.Sec31.PoissonClock.holdingTimePath_modulus_transfer
#print axioms IGS.Sec31.PoissonClock.exponential_clock_ae_window_count_bounds

