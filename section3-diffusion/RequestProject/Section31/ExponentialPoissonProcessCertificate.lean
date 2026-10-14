import RequestProject.Section31.ExponentialPoissonJointIncrements
import RequestProject.Section31.FiniteGraphExponentialHoldingProcess
import RequestProject.Section31.ExponentialClockWindowBounds

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Filter
open IGS.Sec31.DiscreteMarkov
open scoped NNReal
noncomputable section
set_option maxHeartbeats 2500000

/-- Full counting-process laws, including joint independence of every ordered
increment family. These fields are proved for the actual renewal construction
below; they are not assumptions on that construction. -/
structure PoissonCountingProcessLaws {Sample : Type*} [MeasurableSpace Sample]
    (law : Measure Sample) (process : ℝ≥0 → Sample → ℕ) (rate : ℝ≥0) : Prop where
  measurable : ∀ time, Measurable (process time)
  initial : ∀ᵐ sample ∂law, process 0 sample = 0
  regular : ∀ᵐ sample ∂law, Monotone (fun time => process time sample) ∧
    IsCadlagPath (fun time => process time sample)
  increments : ∀ first last, first ≤ last →
    HasLaw (fun sample => process last sample - process first sample)
      (poissonMeasure (rate * (last - first))) law
  independent : ∀ times : ℕ → ℝ≥0, Monotone times →
    iIndepFun (fun index sample => process (times (index + 1)) sample -
      process (times index) sample) law

theorem exponentialHoldingJumpIndex_initial :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw, holdingJumpIndex holdingTimes 0 = 0 := by
  filter_upwards [exponentialHoldingTimeLaw_positive] with holdingTimes positive
  exact holdingTimePath_initial (fun index : ℕ => index) holdingTimes positive

theorem exponentialHoldingJumpIndex_regular :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      Monotone (fun time : ℝ≥0 => holdingJumpIndex holdingTimes (time : ℝ)) ∧
      IsCadlagPath (fun time : ℝ≥0 => holdingJumpIndex holdingTimes (time : ℝ)) := by
  filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
    with holdingTimes positive nonexplosion
  constructor
  · intro first last ordered
    exact holdingJumpIndex_monotone holdingTimes positive nonexplosion first last
      first.coe_nonneg (by exact_mod_cast ordered)
  · exact holdingTimePathNNReal_isCadlag (fun index : ℕ => index) holdingTimes positive nonexplosion

theorem exponentialHoldingJumpIndex_poisson_process :
    PoissonCountingProcessLaws exponentialHoldingTimeLaw
      (fun time holdingTimes => holdingJumpIndex holdingTimes (time : ℝ)) 1 := by
  refine ⟨fun time => holdingJumpIndex_measurable (time : ℝ),
    exponentialHoldingJumpIndex_initial, exponentialHoldingJumpIndex_regular, ?_, ?_⟩
  · intro first last ordered
    have endpoint : first + (last - first) = last := add_tsub_cancel_of_le ordered
    simpa only [endpoint, one_mul] using exponential_poisson_increment_hasLaw first (last - first)
  · intro times ordered
    exact exponential_poisson_increments_iIndepFun times ordered

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJumpIndex_initial
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJumpIndex_regular
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJumpIndex_poisson_process
