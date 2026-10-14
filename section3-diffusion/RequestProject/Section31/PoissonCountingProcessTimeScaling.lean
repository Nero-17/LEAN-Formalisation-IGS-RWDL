import RequestProject.Section31.ExponentialPoissonProcessCertificate

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Filter
open IGS.Sec31.DiscreteMarkov
open scoped NNReal
noncomputable section
set_option maxHeartbeats 1800000

theorem PoissonCountingProcessLaws.timeScale
    {Sample : Type*} [MeasurableSpace Sample] {law : Measure Sample}
    {process : ℝ≥0 → Sample → ℕ} {rate : ℝ≥0}
    (processLaws : PoissonCountingProcessLaws law process rate)
    (speed : ℝ≥0) (speedPositive : 0 < speed) :
    PoissonCountingProcessLaws law (fun time sample => process (speed * time) sample)
      (rate * speed) := by
  constructor
  · intro time
    exact processLaws.measurable (speed * time)
  · simpa only [mul_zero] using processLaws.initial
  · filter_upwards [processLaws.regular] with sample regular
    constructor
    · intro first last ordered
      exact regular.1 (mul_le_mul_of_nonneg_left ordered (zero_le speed))
    · exact regular.2.comp_continuous_strictMono (fun time : ℝ≥0 => speed * time)
        (continuous_const.mul continuous_id)
        (fun _ _ ordered => mul_lt_mul_of_pos_left ordered speedPositive)
  · intro first last ordered
    have increment := processLaws.increments (speed * first) (speed * last)
      (mul_le_mul_of_nonneg_left ordered (zero_le speed))
    simpa only [← mul_tsub, mul_assoc] using increment
  · intro times ordered
    exact processLaws.independent (fun index => speed * times index)
      (fun _ _ before => mul_le_mul_of_nonneg_left (ordered before) (zero_le speed))

theorem exponentialHoldingJumpIndex_scaled_poisson_process
    (speed : ℝ≥0) (speedPositive : 0 < speed) :
    PoissonCountingProcessLaws exponentialHoldingTimeLaw
      (fun time holdingTimes => holdingJumpIndex holdingTimes ((speed * time : ℝ≥0) : ℝ)) speed := by
  simpa only [one_mul] using
    exponentialHoldingJumpIndex_poisson_process.timeScale speed speedPositive

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.PoissonCountingProcessLaws.timeScale
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJumpIndex_scaled_poisson_process
