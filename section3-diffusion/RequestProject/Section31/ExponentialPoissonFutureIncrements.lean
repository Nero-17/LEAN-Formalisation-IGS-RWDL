import RequestProject.Section31.ExponentialFinitePastRegeneration

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3500000

theorem residualHoldingTimes_hasLaw (time : ℝ≥0) :
    HasLaw (fun holdingTimes => residualHoldingTimes holdingTimes (time : ℝ))
      exponentialHoldingTimeLaw exponentialHoldingTimeLaw := by
  refine ⟨(residualHoldingTimes_measurable (time : ℝ)).aemeasurable, ?_⟩
  apply Measure.ext
  intro future futureMeasurable
  rw [Measure.map_apply (residualHoldingTimes_measurable (time : ℝ)) futureMeasurable]
  have factorization := exponential_finite_past_regeneration (observations := 0) time
    Fin.elim0 Fin.elim0 (fun index => Fin.elim0 index) future futureMeasurable
  simpa using factorization

theorem exponential_poisson_increment_hasLaw (time futureTime : ℝ≥0) :
    HasLaw (fun holdingTimes => holdingJumpIndex holdingTimes ((time + futureTime : ℝ≥0) : ℝ) -
      holdingJumpIndex holdingTimes (time : ℝ)) (poissonMeasure futureTime) exponentialHoldingTimeLaw := by
  have futureLaw := (exponentialHoldingJumpIndex_poisson_hasLaw futureTime).fun_comp
    (residualHoldingTimes_hasLaw time)
  apply futureLaw.congr
  filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
    with holdingTimes positive nonexplosion
  change holdingJumpIndex holdingTimes ((time : ℝ) + (futureTime : ℝ)) -
    holdingJumpIndex holdingTimes (time : ℝ) =
      holdingJumpIndex (residualHoldingTimes holdingTimes (time : ℝ)) (futureTime : ℝ)
  rw [holdingJumpIndex_residual_add holdingTimes (time : ℝ) (futureTime : ℝ)
    time.coe_nonneg futureTime.coe_nonneg positive nonexplosion, Nat.add_sub_cancel_left]

theorem exponential_poisson_increment_finite_past_factorization
    {observations : ℕ} (time futureTime : ℝ≥0) (count : ℕ)
    (pastTimes : Fin observations → ℝ≥0) (pastCounts : Fin observations → ℕ)
    (pastBefore : ∀ index, pastTimes index ≤ time) :
    exponentialHoldingTimeLaw {holdingTimes |
        (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
        holdingJumpIndex holdingTimes ((time + futureTime : ℝ≥0) : ℝ) -
          holdingJumpIndex holdingTimes (time : ℝ) = count} =
      exponentialHoldingTimeLaw {holdingTimes |
        ∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index} *
          ENNReal.ofReal (poissonPMFReal futureTime count) := by
  have futureMeasurable : MeasurableSet
      {tail : ℕ → ℝ | holdingJumpIndex tail (futureTime : ℝ) = count} :=
    (measurableSet_singleton count).preimage (holdingJumpIndex_measurable (futureTime : ℝ))
  have factorization := exponential_finite_past_regeneration time pastTimes pastCounts pastBefore
    {tail : ℕ → ℝ | holdingJumpIndex tail (futureTime : ℝ) = count} futureMeasurable
  have eventEquality :
      exponentialHoldingTimeLaw {holdingTimes |
        (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
        holdingJumpIndex holdingTimes ((time + futureTime : ℝ≥0) : ℝ) -
          holdingJumpIndex holdingTimes (time : ℝ) = count} =
      exponentialHoldingTimeLaw {holdingTimes |
        (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
        residualHoldingTimes holdingTimes (time : ℝ) ∈
          {tail : ℕ → ℝ | holdingJumpIndex tail (futureTime : ℝ) = count}} := by
    apply measure_congr
    filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
      with holdingTimes positive nonexplosion
    apply propext
    change ((∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
      holdingJumpIndex holdingTimes ((time : ℝ) + (futureTime : ℝ)) -
        holdingJumpIndex holdingTimes (time : ℝ) = count) ↔
      ((∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
        holdingJumpIndex (residualHoldingTimes holdingTimes (time : ℝ)) (futureTime : ℝ) = count)
    rw [holdingJumpIndex_residual_add holdingTimes (time : ℝ) (futureTime : ℝ)
      time.coe_nonneg futureTime.coe_nonneg positive nonexplosion, Nat.add_sub_cancel_left]
  rw [← eventEquality, exponentialHoldingJumpIndex_poisson_probability] at factorization
  exact factorization

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.residualHoldingTimes_hasLaw
#print axioms IGS.Sec31.PoissonClock.exponential_poisson_increment_hasLaw
#print axioms IGS.Sec31.PoissonClock.exponential_poisson_increment_finite_past_factorization
