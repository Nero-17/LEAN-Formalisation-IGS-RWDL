import RequestProject.Section31.ExponentialHoldingSumGammaLaw
import RequestProject.Section31.GammaExponentialIntervalEvent

/-! Actual holding-jump count marginals: the original infinite iid
exponential sample has the Poisson law at every nonnegative time. -/

namespace IGS.Sec31.PoissonClock
open ProbabilityTheory MeasureTheory Real Set Filter
open scoped ENNReal NNReal Classical MeasureTheory
noncomputable section

 theorem exponentialHoldingJumpIndex_poisson_probability (time : ℝ≥0) (count : ℕ) :
    exponentialHoldingTimeLaw {holdingTimes | holdingJumpIndex holdingTimes (time : ℝ) = count} =
      ENNReal.ofReal (poissonPMFReal time count) := by
  cases count with
  | zero =>
      simpa only [poissonPMFReal, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one] using
        exponentialHoldingJumpIndex_zero_probability (time : ℝ) time.coe_nonneg
  | succ previous =>
      have eventEquality :
          exponentialHoldingTimeLaw {holdingTimes | holdingJumpIndex holdingTimes (time : ℝ) = previous + 1} =
          exponentialHoldingTimeLaw {holdingTimes : ℕ → ℝ |
            cumulativeHoldingTime holdingTimes (previous + 1) ≤ (time : ℝ) ∧
              (time : ℝ) < cumulativeHoldingTime holdingTimes (previous + 1) + holdingTimes (previous + 1)} := by
        apply measure_congr
        filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
          with holdingTimes positive nonexplosion
        apply propext
        constructor
        · intro countEquality
          have interval := holdingJumpIndex_interval holdingTimes (fun index => (positive index).le)
            nonexplosion (time : ℝ) time.coe_nonneg
          simpa only [countEquality, cumulativeHoldingTime, Finset.sum_range_succ] using interval
        · intro interval
          apply holdingJumpIndex_eq_of_interval holdingTimes (fun index => (positive index).le)
            (time : ℝ) (previous + 1) interval.1
          simpa only [cumulativeHoldingTime, Finset.sum_range_succ] using interval.2
      have jointLaw := (indepFun_iff_map_prod_eq_prod_map_map
        (cumulativeHoldingTime_measurable (previous + 1)).aemeasurable
        (measurable_pi_apply (previous + 1)).aemeasurable).mp
          (cumulativeHoldingTime_independent_next (previous + 1))
      rw [(cumulativeHoldingTime_gamma_hasLaw previous).map_eq,
        (exponentialHoldingTime_eval_hasLaw (previous + 1)).map_eq] at jointLaw
      have regionMeasurable : MeasurableSet
          {pair : ℝ × ℝ | pair.1 ≤ (time : ℝ) ∧ (time : ℝ) < pair.1 + pair.2} :=
        (measurableSet_le measurable_fst measurable_const).inter
          (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
      rw [show Nat.succ previous = previous + 1 from rfl, eventEquality]
      have mappedEvent :
          exponentialHoldingTimeLaw {holdingTimes : ℕ → ℝ |
            cumulativeHoldingTime holdingTimes (previous + 1) ≤ (time : ℝ) ∧
              (time : ℝ) < cumulativeHoldingTime holdingTimes (previous + 1) + holdingTimes (previous + 1)} =
          (exponentialHoldingTimeLaw.map (fun holdingTimes : ℕ → ℝ =>
            (cumulativeHoldingTime holdingTimes (previous + 1), holdingTimes (previous + 1))))
              {pair : ℝ × ℝ | pair.1 ≤ (time : ℝ) ∧ (time : ℝ) < pair.1 + pair.2} := by
        rw [Measure.map_apply ((cumulativeHoldingTime_measurable (previous + 1)).prodMk
          (measurable_pi_apply (previous + 1))) regionMeasurable]
        rfl
      rw [mappedEvent, jointLaw, IGS.Sec31.gamma_exponential_interval_event_probability,
        IGS.Sec31.gammaPDF_natural_succ_unit_rate, if_pos time.coe_nonneg]
      congr 1
      simp only [poissonPMFReal, mul_comm]

 theorem exponentialHoldingJumpIndex_poisson_hasLaw (time : ℝ≥0) :
    HasLaw (fun holdingTimes => holdingJumpIndex holdingTimes (time : ℝ))
      (poissonMeasure time) exponentialHoldingTimeLaw := by
  refine ⟨(holdingJumpIndex_measurable (time : ℝ)).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro count
  rw [Measure.map_apply (holdingJumpIndex_measurable (time : ℝ)) (measurableSet_singleton count)]
  change exponentialHoldingTimeLaw {holdingTimes | holdingJumpIndex holdingTimes (time : ℝ) = count} = _
  rw [exponentialHoldingJumpIndex_poisson_probability]
  simp only [poissonMeasure, PMF.toMeasure_apply_singleton, poissonPMF]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJumpIndex_poisson_probability
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJumpIndex_poisson_hasLaw
