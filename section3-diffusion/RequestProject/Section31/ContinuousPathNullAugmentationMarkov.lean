import RequestProject.Section31.UsualFiltrationAugmentation
import RequestProject.Section31.ContinuousPathMarkovPastEvents

/-! Transfer Borel set integrals to the completed measure and derive the
deterministic-time continuous-test Markov identity after adjoining every
global null event to the natural filtration. The identity is obtained from
an almost-everywhere equal natural-past representative of each event. -/

namespace IGS.Sec31.UsualAugmentation

open MeasureTheory Set Filter
noncomputable section

variable {Sample : Type*} [ambient : MeasurableSpace Sample]

theorem completion_trim_eq (measure : Measure Sample) :
    measure.completion.trim (le_eventuallyMeasurableSpace (m := ambient) (l := ae measure)) = measure := by
  ext event eventMeasurable
  rw [Measure.trim_measurableSet_eq _ eventMeasurable]
  rfl

theorem setIntegral_completion_eq (measure : Measure Sample) (function : Sample → ℝ)
    (functionMeasurable : StronglyMeasurable function) (event : Set Sample)
    (eventMeasurable : MeasurableSet event) :
    (∫ sample : NullMeasurableSpace Sample measure in event, function sample ∂measure.completion) =
      ∫ sample in event, function sample ∂measure := by
  have trimming := setIntegral_trim (m := ambient)
    (m0 := eventuallyMeasurableSpace ambient (ae measure)) (μ := measure.completion)
    (le_eventuallyMeasurableSpace (m := ambient) (l := ae measure)) functionMeasurable eventMeasurable
  simpa only [completion_trim_eq] using trimming

end
end IGS.Sec31.UsualAugmentation

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open IGS.Sec31.UsualAugmentation
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 6000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance continuousNullAugmentationMarkovMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance continuousNullAugmentationMarkovBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem continuousPath_nullAugmentation_setIntegral_markov
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[
      nullAugmentation (law : Measure C(ℝ≥0, State)) canonicalContinuousPathFiltration time] event) :
    (∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
      terminal (path (time + delay)) ∂(law : Measure C(ℝ≥0, State)).completion) =
      ∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
        semigroup delay terminal (path time) ∂(law : Measure C(ℝ≥0, State)).completion := by
  obtain ⟨representative, representativeMeasurable, sameEvent⟩ := eventMeasurable
  have representativeGlobalMeasurable : MeasurableSet representative :=
    (canonicalContinuousPathFiltration (State := State)).le time representative representativeMeasurable
  calc
    _ = ∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in representative,
        terminal (path (time + delay)) ∂(law : Measure C(ℝ≥0, State)).completion :=
      setIntegral_congr_set sameEvent
    _ = ∫ path in representative, terminal (path (time + delay)) ∂(law : Measure C(ℝ≥0, State)) :=
      setIntegral_completion_eq (law : Measure C(ℝ≥0, State)) _
        (terminal.continuous.comp (continuous_eval_const (time + delay))).stronglyMeasurable
        representative representativeGlobalMeasurable
    _ = ∫ path in representative, semigroup delay terminal (path time) ∂(law : Measure C(ℝ≥0, State)) :=
      continuousPath_natural_setIntegral_markov law semigroup start positive observations
        time delay terminal representative representativeMeasurable
    _ = ∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in representative,
        semigroup delay terminal (path time) ∂(law : Measure C(ℝ≥0, State)).completion :=
      (setIntegral_completion_eq (law : Measure C(ℝ≥0, State)) _
        ((semigroup delay terminal).continuous.comp (continuous_eval_const time)).stronglyMeasurable
        representative representativeGlobalMeasurable).symm
    _ = _ := setIntegral_congr_set sameEvent.symm

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.UsualAugmentation.completion_trim_eq
#print axioms IGS.Sec31.UsualAugmentation.setIntegral_completion_eq
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_nullAugmentation_setIntegral_markov
