import RequestProject.Section31.ExponentialPoissonFutureIncrements
import RequestProject.Section31.CountableFirstIndependence

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
noncomputable section
set_option maxHeartbeats 3500000

theorem exponential_finite_past_residual_independent
    {observations : ℕ} (time : ℝ≥0) (pastTimes : Fin observations → ℝ≥0)
    (pastBefore : ∀ index, pastTimes index ≤ time) :
    IndepFun (fun holdingTimes : ℕ → ℝ =>
        fun index => holdingJumpIndex holdingTimes (pastTimes index : ℝ))
      (fun holdingTimes => residualHoldingTimes holdingTimes (time : ℝ)) exponentialHoldingTimeLaw := by
  have pastMeasurable : Measurable (fun holdingTimes : ℕ → ℝ =>
      fun index => holdingJumpIndex holdingTimes (pastTimes index : ℝ)) := by
    apply measurable_pi_lambda
    intro index
    exact holdingJumpIndex_measurable (pastTimes index : ℝ)
  apply indepFun_of_countable_first_singleton_factorization exponentialHoldingTimeLaw
    exponentialHoldingTimeLaw _ _ pastMeasurable (residualHoldingTimes_measurable (time : ℝ))
    (residualHoldingTimes_hasLaw time)
  intro pastCounts future futureMeasurable
  simpa only [funext_iff] using exponential_finite_past_regeneration time pastTimes pastCounts
    pastBefore future futureMeasurable

theorem exponential_poisson_future_increment_independent
    {observations : ℕ} (time futureTime : ℝ≥0) (pastTimes : Fin observations → ℝ≥0)
    (pastBefore : ∀ index, pastTimes index ≤ time) :
    IndepFun (fun holdingTimes : ℕ → ℝ =>
        fun index => holdingJumpIndex holdingTimes (pastTimes index : ℝ))
      (fun holdingTimes => holdingJumpIndex holdingTimes ((time + futureTime : ℝ≥0) : ℝ) -
        holdingJumpIndex holdingTimes (time : ℝ)) exponentialHoldingTimeLaw := by
  have independent := (exponential_finite_past_residual_independent time pastTimes pastBefore).comp
    measurable_id (holdingJumpIndex_measurable (futureTime : ℝ))
  apply independent.congr (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
    with holdingTimes positive nonexplosion
  change holdingJumpIndex (residualHoldingTimes holdingTimes (time : ℝ)) (futureTime : ℝ) =
    holdingJumpIndex holdingTimes ((time : ℝ) + (futureTime : ℝ)) -
      holdingJumpIndex holdingTimes (time : ℝ)
  rw [holdingJumpIndex_residual_add holdingTimes (time : ℝ) (futureTime : ℝ)
    time.coe_nonneg futureTime.coe_nonneg positive nonexplosion, Nat.add_sub_cancel_left]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponential_finite_past_residual_independent
#print axioms IGS.Sec31.PoissonClock.exponential_poisson_future_increment_independent
