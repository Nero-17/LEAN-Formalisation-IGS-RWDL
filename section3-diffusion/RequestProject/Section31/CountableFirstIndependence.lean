import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Set
noncomputable section
set_option maxHeartbeats 2200000

theorem measure_countable_fibre_partition
    {Sample Value : Type*} [MeasurableSpace Sample] [MeasurableSpace Value]
    [Countable Value] [MeasurableSingletonClass Value]
    (law : Measure Sample) (value : Sample → Value) (valueMeasurable : Measurable value)
    (event : Set Sample) (eventMeasurable : MeasurableSet event) :
    law event = ∑' point : Value, law {sample | sample ∈ event ∧ value sample = point} := by
  have unionEquality : event = ⋃ point : Value, {sample | sample ∈ event ∧ value sample = point} := by
    ext sample
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · intro membership
      exact ⟨value sample, membership, rfl⟩
    · rintro ⟨_, membership, _⟩
      exact membership
  have disjoint : Pairwise (fun first second : Value =>
      Disjoint {sample | sample ∈ event ∧ value sample = first}
        {sample | sample ∈ event ∧ value sample = second}) := by
    intro first second distinct
    apply Set.disjoint_left.mpr
    intro sample firstMembership secondMembership
    exact distinct (firstMembership.2.symm.trans secondMembership.2)
  have measurable (point : Value) : MeasurableSet {sample | sample ∈ event ∧ value sample = point} :=
    eventMeasurable.inter ((measurableSet_singleton point).preimage valueMeasurable)
  calc
    law event = law (⋃ point : Value, {sample | sample ∈ event ∧ value sample = point}) :=
      congrArg law unionEquality
    _ = _ := measure_iUnion disjoint measurable

theorem indepFun_of_countable_first_singleton_factorization
    {Sample First Future : Type*}
    [MeasurableSpace Sample] [MeasurableSpace First] [MeasurableSpace Future]
    [Countable First] [MeasurableSingletonClass First]
    (law : Measure Sample) (futureLaw : Measure Future)
    (first : Sample → First) (future : Sample → Future)
    (firstMeasurable : Measurable first) (futureMeasurable : Measurable future)
    (futureHasLaw : HasLaw future futureLaw law)
    (factorization : ∀ point : First, ∀ event : Set Future, MeasurableSet event →
      law {sample | first sample = point ∧ future sample ∈ event} =
        law {sample | first sample = point} * futureLaw event) :
    IndepFun first future law := by
  classical
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro firstEvent futureEvent firstEventMeasurable futureEventMeasurable
  have futureProbability : law (future ⁻¹' futureEvent) = futureLaw futureEvent := by
    rw [← Measure.map_apply futureMeasurable futureEventMeasurable, futureHasLaw.map_eq]
  have termFactorization (point : First) :
      law {sample | sample ∈ first ⁻¹' firstEvent ∩ future ⁻¹' futureEvent ∧ first sample = point} =
        law {sample | sample ∈ first ⁻¹' firstEvent ∧ first sample = point} * futureLaw futureEvent := by
    have firstEquality :
        {sample : Sample | sample ∈ first ⁻¹' firstEvent ∧ first sample = point} =
          if point ∈ firstEvent then {sample | first sample = point} else ∅ := by
      by_cases membership : point ∈ firstEvent <;> ext sample <;>
        by_cases equality : first sample = point <;> simp [membership, equality]
    have fullEquality :
        {sample : Sample | sample ∈ first ⁻¹' firstEvent ∩ future ⁻¹' futureEvent ∧ first sample = point} =
          if point ∈ firstEvent then {sample | first sample = point ∧ future sample ∈ futureEvent} else ∅ := by
      by_cases membership : point ∈ firstEvent <;> ext sample <;>
        by_cases equality : first sample = point <;> simp [membership, equality]
    rw [firstEquality, fullEquality]
    by_cases membership : point ∈ firstEvent
    · simp only [if_pos membership]
      exact factorization point futureEvent futureEventMeasurable
    · simp only [if_neg membership, measure_empty, zero_mul]
  calc
    law (first ⁻¹' firstEvent ∩ future ⁻¹' futureEvent) =
        ∑' point : First, law {sample |
          sample ∈ first ⁻¹' firstEvent ∩ future ⁻¹' futureEvent ∧ first sample = point} :=
      measure_countable_fibre_partition law first firstMeasurable _
        ((firstEventMeasurable.preimage firstMeasurable).inter
          (futureEventMeasurable.preimage futureMeasurable))
    _ = ∑' point : First,
        law {sample | sample ∈ first ⁻¹' firstEvent ∧ first sample = point} * futureLaw futureEvent :=
      tsum_congr termFactorization
    _ = (∑' point : First,
        law {sample | sample ∈ first ⁻¹' firstEvent ∧ first sample = point}) * futureLaw futureEvent := by
      rw [ENNReal.tsum_mul_right]
    _ = law (first ⁻¹' firstEvent) * law (future ⁻¹' futureEvent) := by
      rw [← measure_countable_fibre_partition law first firstMeasurable _
        (firstEventMeasurable.preimage firstMeasurable), futureProbability]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.measure_countable_fibre_partition
#print axioms IGS.Sec31.PoissonClock.indepFun_of_countable_first_singleton_factorization
