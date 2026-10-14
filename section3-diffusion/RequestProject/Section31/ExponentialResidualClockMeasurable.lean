import RequestProject.Section31.ExponentialResidualClockIdentity

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Filter
noncomputable section
set_option maxHeartbeats 2200000

theorem holdingJumpIndex_eq_iff_interval
    (holdingTimes : ℕ → ℝ) (nonnegative : ∀ index, 0 ≤ holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (count : ℕ) :
    holdingJumpIndex holdingTimes time = count ↔
      cumulativeHoldingTime holdingTimes count ≤ time ∧
        time < cumulativeHoldingTime holdingTimes (count + 1) := by
  constructor
  · intro equality
    have interval := holdingJumpIndex_interval holdingTimes nonnegative nonexplosion time timeNonnegative
    rw [equality] at interval
    exact interval
  · intro interval
    exact holdingJumpIndex_eq_of_interval holdingTimes nonnegative time count interval.1 interval.2

theorem residualHoldingTimes_measurable (time : ℝ) :
    Measurable (fun holdingTimes => residualHoldingTimes holdingTimes time) := by
  have cumulativeEvaluation : Measurable
      (fun sample : (ℕ → ℝ) × ℕ => cumulativeHoldingTime sample.1 sample.2) :=
    measurable_from_prod_countable_left fun count => cumulativeHoldingTime_measurable count
  have coordinateEvaluation : Measurable
      (fun sample : (ℕ → ℝ) × ℕ => sample.1 sample.2) :=
    measurable_from_prod_countable_left fun count => measurable_pi_apply count
  have nextIndex : Measurable (fun holdingTimes => holdingJumpIndex holdingTimes time + 1) :=
    (holdingJumpIndex_measurable time).add_const 1
  have firstMeasurable : Measurable (fun holdingTimes =>
      cumulativeHoldingTime holdingTimes (holdingJumpIndex holdingTimes time + 1) - time) :=
    (cumulativeEvaluation.comp (measurable_id.prodMk nextIndex)).sub_const time
  have tailMeasurable : Measurable (fun holdingTimes =>
      shiftedHoldingTimes (holdingJumpIndex holdingTimes time + 1) holdingTimes) := by
    apply measurable_pi_lambda
    intro index
    exact coordinateEvaluation.comp (measurable_id.prodMk (nextIndex.add_const index))
  exact prependHoldingTime_measurable.comp (firstMeasurable.prodMk tailMeasurable)

theorem residualHoldingTimes_on_count
    (holdingTimes : ℕ → ℝ) (time : ℝ) (count : ℕ)
    (countEquality : holdingJumpIndex holdingTimes time = count) :
    residualHoldingTimes holdingTimes time =
      prependHoldingTime (holdingTimes count - (time - cumulativeHoldingTime holdingTimes count))
        (shiftedHoldingTimes (count + 1) holdingTimes) := by
  unfold residualHoldingTimes
  rw [countEquality]
  congr 1
  simp only [cumulativeHoldingTime, Finset.sum_range_succ]
  ring

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingJumpIndex_eq_iff_interval
#print axioms IGS.Sec31.PoissonClock.residualHoldingTimes_measurable
#print axioms IGS.Sec31.PoissonClock.residualHoldingTimes_on_count
