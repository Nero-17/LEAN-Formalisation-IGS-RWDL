import RequestProject.Section31.ExponentialActualCountRegeneration
import RequestProject.Section31.ExponentialHoldingFiniteHistory

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
noncomputable section
set_option maxHeartbeats 3500000

def holdingPrefixCountHistory {count observations : ℕ}
    (pastTimes : Fin observations → ℝ≥0) (pastCounts : Fin observations → ℕ) :
    Set (Fin count → ℝ) :=
  {historyPoint | ∀ index,
    pastCounts index ≤ count ∧
      cumulativeHoldingTime (holdingPrefixExtension historyPoint) (pastCounts index) ≤ (pastTimes index : ℝ) ∧
        (pastCounts index = count ∨ (pastTimes index : ℝ) <
          cumulativeHoldingTime (holdingPrefixExtension historyPoint) (pastCounts index + 1))}

theorem holdingPrefixCountHistory_measurable {count observations : ℕ}
    (pastTimes : Fin observations → ℝ≥0) (pastCounts : Fin observations → ℕ) :
    MeasurableSet (holdingPrefixCountHistory (count := count) pastTimes pastCounts) := by
  have individual (index : Fin observations) : MeasurableSet
      {historyPoint : Fin count → ℝ | pastCounts index ≤ count ∧
        cumulativeHoldingTime (holdingPrefixExtension historyPoint) (pastCounts index) ≤ (pastTimes index : ℝ) ∧
          (pastCounts index = count ∨ (pastTimes index : ℝ) <
            cumulativeHoldingTime (holdingPrefixExtension historyPoint) (pastCounts index + 1))} := by
    by_cases bounded : pastCounts index ≤ count
    · by_cases last : pastCounts index = count
      · simp only [last, le_refl, true_and, true_or, eq_self, and_true]
        exact measurableSet_le
          ((cumulativeHoldingTime_measurable count).comp (holdingPrefixExtension_measurable count))
          measurable_const
      · simp only [bounded, true_and, last, false_or]
        exact (measurableSet_le
          ((cumulativeHoldingTime_measurable (pastCounts index)).comp
            (holdingPrefixExtension_measurable count)) measurable_const).inter
          (measurableSet_lt measurable_const
            ((cumulativeHoldingTime_measurable (pastCounts index + 1)).comp
              (holdingPrefixExtension_measurable count)))
    · simp only [bounded, false_and]
      exact MeasurableSet.empty
  convert MeasurableSet.iInter individual using 1
  ext historyPoint
  simp only [holdingPrefixCountHistory, mem_setOf_eq, mem_iInter]

theorem exponential_finite_history_count_regeneration
    {observations : ℕ} (time : ℝ≥0) (count : ℕ)
    (pastTimes : Fin observations → ℝ≥0) (pastCounts : Fin observations → ℕ)
    (pastBefore : ∀ index, pastTimes index ≤ time)
    (future : Set (ℕ → ℝ)) (futureMeasurable : MeasurableSet future) :
    exponentialHoldingTimeLaw {holdingTimes |
        (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
          holdingJumpIndex holdingTimes (time : ℝ) = count ∧
            residualHoldingTimes holdingTimes (time : ℝ) ∈ future} =
      exponentialHoldingTimeLaw {holdingTimes |
          (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
            holdingJumpIndex holdingTimes (time : ℝ) = count} * exponentialHoldingTimeLaw future := by
  have factorization := exponential_actual_count_regeneration time count
    (holdingPrefixCountHistory pastTimes pastCounts)
    (holdingPrefixCountHistory_measurable pastTimes pastCounts) future futureMeasurable
  have historyEquivalence (holdingTimes : ℕ → ℝ)
      (positive : ∀ index, 0 < holdingTimes index)
      (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
      (countEquality : holdingJumpIndex holdingTimes (time : ℝ) = count) :
      (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ↔
        holdingPrefix count holdingTimes ∈ holdingPrefixCountHistory pastTimes pastCounts := by
    change (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ↔
      ∀ index, pastCounts index ≤ count ∧
        cumulativeHoldingTime (holdingPrefixExtension (holdingPrefix count holdingTimes))
          (pastCounts index) ≤ (pastTimes index : ℝ) ∧
        (pastCounts index = count ∨ (pastTimes index : ℝ) <
          cumulativeHoldingTime (holdingPrefixExtension (holdingPrefix count holdingTimes)) (pastCounts index + 1))
    exact forall_congr' fun index => holdingJumpIndex_past_prefix_on_count holdingTimes
      (fun index => (positive index).le) nonexplosion (time : ℝ) (pastTimes index : ℝ)
      time.coe_nonneg (pastTimes index).coe_nonneg (pastBefore index) count (pastCounts index) countEquality
  have baseEquality :
      exponentialHoldingTimeLaw {holdingTimes |
          (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
            holdingJumpIndex holdingTimes (time : ℝ) = count} =
        exponentialHoldingTimeLaw {holdingTimes |
          holdingJumpIndex holdingTimes (time : ℝ) = count ∧
            holdingPrefix count holdingTimes ∈ holdingPrefixCountHistory pastTimes pastCounts} := by
    apply measure_congr
    filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
      with holdingTimes positive nonexplosion
    apply propext
    constructor
    · rintro ⟨past, countEquality⟩
      exact ⟨countEquality, (historyEquivalence holdingTimes positive nonexplosion countEquality).mp past⟩
    · rintro ⟨countEquality, past⟩
      exact ⟨(historyEquivalence holdingTimes positive nonexplosion countEquality).mpr past, countEquality⟩
  have fullEquality :
      exponentialHoldingTimeLaw {holdingTimes |
          (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
            holdingJumpIndex holdingTimes (time : ℝ) = count ∧ residualHoldingTimes holdingTimes (time : ℝ) ∈ future} =
        exponentialHoldingTimeLaw {holdingTimes |
          holdingJumpIndex holdingTimes (time : ℝ) = count ∧
            holdingPrefix count holdingTimes ∈ holdingPrefixCountHistory pastTimes pastCounts ∧
              residualHoldingTimes holdingTimes (time : ℝ) ∈ future} := by
    apply measure_congr
    filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
      with holdingTimes positive nonexplosion
    apply propext
    constructor
    · rintro ⟨past, countEquality, futureMembership⟩
      exact ⟨countEquality, (historyEquivalence holdingTimes positive nonexplosion countEquality).mp past,
        futureMembership⟩
    · rintro ⟨countEquality, past, futureMembership⟩
      exact ⟨(historyEquivalence holdingTimes positive nonexplosion countEquality).mpr past,
        countEquality, futureMembership⟩
  rw [fullEquality, baseEquality]
  exact factorization

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingPrefixCountHistory_measurable
#print axioms IGS.Sec31.PoissonClock.exponential_finite_history_count_regeneration
