import RequestProject.Section31.ExponentialSurvivalRegenerationFactorization
import RequestProject.Section31.ExponentialHoldingPrefixArrival
import RequestProject.Section31.ExponentialResidualClockMeasurable

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
noncomputable section
set_option maxHeartbeats 3500000

/-- On each actual count fibre, the regenerated infinite future factors
from every event in the entire finite holding-time history. -/
theorem exponential_actual_count_regeneration
    (time : ℝ≥0) (count : ℕ)
    (history : Set (Fin count → ℝ)) (historyMeasurable : MeasurableSet history)
    (future : Set (ℕ → ℝ)) (futureMeasurable : MeasurableSet future) :
    exponentialHoldingTimeLaw
        {holdingTimes | holdingJumpIndex holdingTimes (time : ℝ) = count ∧
          holdingPrefix count holdingTimes ∈ history ∧
          residualHoldingTimes holdingTimes (time : ℝ) ∈ future} =
      exponentialHoldingTimeLaw
          {holdingTimes | holdingJumpIndex holdingTimes (time : ℝ) = count ∧
            holdingPrefix count holdingTimes ∈ history} * exponentialHoldingTimeLaw future := by
  letI : IsProbabilityMeasure (exponentialHoldingTimeLaw.map (holdingPrefix count)) :=
    Measure.isProbabilityMeasure_map (holdingPrefix_measurable count).aemeasurable
  let baseEvent : Set ((Fin count → ℝ) × (ℝ × (ℕ → ℝ))) :=
    {sample | holdingPrefixArrival sample.1 ≤ (time : ℝ) ∧ sample.1 ∈ history ∧
      (time : ℝ) - holdingPrefixArrival sample.1 < sample.2.1}
  let fullEvent : Set ((Fin count → ℝ) × (ℝ × (ℕ → ℝ))) :=
    {sample | holdingPrefixArrival sample.1 ≤ (time : ℝ) ∧ sample.1 ∈ history ∧
      (time : ℝ) - holdingPrefixArrival sample.1 < sample.2.1 ∧
      prependHoldingTime (sample.2.1 - ((time : ℝ) - holdingPrefixArrival sample.1)) sample.2.2 ∈ future}
  have sampleMeasurable : Measurable (fun holdingTimes : ℕ → ℝ =>
      (holdingPrefix count holdingTimes,
        (holdingTimes count, shiftedHoldingTimes (count + 1) holdingTimes))) :=
    (holdingPrefix_measurable count).prodMk
      ((measurable_pi_apply count).prodMk (shiftedHoldingTimes_measurable (count + 1)))
  have baseMeasurable : MeasurableSet baseEvent :=
    (measurableSet_le ((holdingPrefixArrival_measurable count).comp measurable_fst)
      measurable_const).inter ((historyMeasurable.preimage measurable_fst).inter
        (measurableSet_lt (measurable_const.sub
          ((holdingPrefixArrival_measurable count).comp measurable_fst))
            (measurable_fst.comp measurable_snd)))
  have residualMeasurable : Measurable
      (fun sample : (Fin count → ℝ) × (ℝ × (ℕ → ℝ)) => prependHoldingTime
        (sample.2.1 - ((time : ℝ) - holdingPrefixArrival sample.1)) sample.2.2) :=
    prependHoldingTime_measurable.comp
      (((measurable_fst.comp measurable_snd).sub (measurable_const.sub
        ((holdingPrefixArrival_measurable count).comp measurable_fst))).prodMk
          (measurable_snd.comp measurable_snd))
  have fullMeasurable : MeasurableSet fullEvent := by
    convert baseMeasurable.inter (futureMeasurable.preimage residualMeasurable) using 1
    ext sample
    simp only [baseEvent, fullEvent, mem_setOf_eq, mem_inter_iff, mem_preimage, and_assoc]
  have factorization := exponential_survival_regeneration_factorization
    (exponentialHoldingTimeLaw.map (holdingPrefix count)) holdingPrefixArrival
    (holdingPrefixArrival_measurable count) (time : ℝ) history historyMeasurable future futureMeasurable
  change ((exponentialHoldingTimeLaw.map (holdingPrefix count)).prod
      ((expMeasure 1).prod exponentialHoldingTimeLaw)) fullEvent =
    ((exponentialHoldingTimeLaw.map (holdingPrefix count)).prod
      ((expMeasure 1).prod exponentialHoldingTimeLaw)) baseEvent *
        exponentialHoldingTimeLaw future at factorization
  rw [← exponential_holding_prefix_next_tail_map count,
    Measure.map_apply sampleMeasurable fullMeasurable,
    Measure.map_apply sampleMeasurable baseMeasurable] at factorization
  have baseEquivalence (holdingTimes : ℕ → ℝ)
      (positive : ∀ index, 0 < holdingTimes index)
      (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop) :
      (holdingJumpIndex holdingTimes (time : ℝ) = count ∧ holdingPrefix count holdingTimes ∈ history) ↔
        (holdingPrefix count holdingTimes,
          (holdingTimes count, shiftedHoldingTimes (count + 1) holdingTimes)) ∈ baseEvent := by
    have intervalIff := holdingJumpIndex_eq_iff_interval holdingTimes
      (fun index => (positive index).le) nonexplosion (time : ℝ) time.coe_nonneg count
    have cumulativeNext : cumulativeHoldingTime holdingTimes (count + 1) =
        cumulativeHoldingTime holdingTimes count + holdingTimes count := by
      simp only [cumulativeHoldingTime, Finset.sum_range_succ]
    rw [cumulativeNext] at intervalIff
    change (holdingJumpIndex holdingTimes (time : ℝ) = count ∧
      holdingPrefix count holdingTimes ∈ history) ↔
      (holdingPrefixArrival (holdingPrefix count holdingTimes) ≤ (time : ℝ) ∧
        holdingPrefix count holdingTimes ∈ history ∧
        (time : ℝ) - holdingPrefixArrival (holdingPrefix count holdingTimes) < holdingTimes count)
    rw [holdingPrefixArrival_actual]
    constructor
    · rintro ⟨countEquality, historyMembership⟩
      obtain ⟨lower, upper⟩ := intervalIff.mp countEquality
      exact ⟨lower, historyMembership, by linarith only [upper]⟩
    · rintro ⟨lower, historyMembership, upper⟩
      exact ⟨intervalIff.mpr ⟨lower, by linarith only [upper]⟩, historyMembership⟩
  have baseProbability :
      exponentialHoldingTimeLaw {holdingTimes | holdingJumpIndex holdingTimes (time : ℝ) = count ∧
        holdingPrefix count holdingTimes ∈ history} =
      exponentialHoldingTimeLaw ((fun holdingTimes : ℕ → ℝ =>
        (holdingPrefix count holdingTimes,
          (holdingTimes count, shiftedHoldingTimes (count + 1) holdingTimes))) ⁻¹' baseEvent) := by
    apply measure_congr
    filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
      with holdingTimes positive nonexplosion
    apply propext
    exact baseEquivalence holdingTimes positive nonexplosion
  have fullProbability :
      exponentialHoldingTimeLaw {holdingTimes | holdingJumpIndex holdingTimes (time : ℝ) = count ∧
        holdingPrefix count holdingTimes ∈ history ∧ residualHoldingTimes holdingTimes (time : ℝ) ∈ future} =
      exponentialHoldingTimeLaw ((fun holdingTimes : ℕ → ℝ =>
        (holdingPrefix count holdingTimes,
          (holdingTimes count, shiftedHoldingTimes (count + 1) holdingTimes))) ⁻¹' fullEvent) := by
    apply measure_congr
    filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
      with holdingTimes positive nonexplosion
    apply propext
    change (holdingJumpIndex holdingTimes (time : ℝ) = count ∧
      holdingPrefix count holdingTimes ∈ history ∧ residualHoldingTimes holdingTimes (time : ℝ) ∈ future) ↔
      (holdingPrefixArrival (holdingPrefix count holdingTimes) ≤ (time : ℝ) ∧
        holdingPrefix count holdingTimes ∈ history ∧
        (time : ℝ) - holdingPrefixArrival (holdingPrefix count holdingTimes) < holdingTimes count ∧
        prependHoldingTime (holdingTimes count - ((time : ℝ) -
          holdingPrefixArrival (holdingPrefix count holdingTimes)))
            (shiftedHoldingTimes (count + 1) holdingTimes) ∈ future)
    rw [holdingPrefixArrival_actual]
    constructor
    · rintro ⟨countEquality, historyMembership, futureMembership⟩
      have admitted := (baseEquivalence holdingTimes positive nonexplosion).mp
        ⟨countEquality, historyMembership⟩
      change holdingPrefixArrival (holdingPrefix count holdingTimes) ≤ (time : ℝ) ∧
        holdingPrefix count holdingTimes ∈ history ∧
        (time : ℝ) - holdingPrefixArrival (holdingPrefix count holdingTimes) < holdingTimes count at admitted
      rw [holdingPrefixArrival_actual] at admitted
      refine ⟨admitted.1, admitted.2.1, admitted.2.2, ?_⟩
      rw [← residualHoldingTimes_on_count holdingTimes (time : ℝ) count countEquality]
      exact futureMembership
    · rintro ⟨lower, historyMembership, upper, futureMembership⟩
      have admitted :
          (holdingPrefix count holdingTimes,
            (holdingTimes count, shiftedHoldingTimes (count + 1) holdingTimes)) ∈ baseEvent := by
        change holdingPrefixArrival (holdingPrefix count holdingTimes) ≤ (time : ℝ) ∧
          holdingPrefix count holdingTimes ∈ history ∧
          (time : ℝ) - holdingPrefixArrival (holdingPrefix count holdingTimes) < holdingTimes count
        rw [holdingPrefixArrival_actual]
        exact ⟨lower, historyMembership, upper⟩
      have countEquality := ((baseEquivalence holdingTimes positive nonexplosion).mpr admitted).1
      refine ⟨countEquality, historyMembership, ?_⟩
      rw [residualHoldingTimes_on_count holdingTimes (time : ℝ) count countEquality]
      exact futureMembership
  rw [← fullProbability, ← baseProbability] at factorization
  exact factorization

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponential_actual_count_regeneration
