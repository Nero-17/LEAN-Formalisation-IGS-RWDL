import RequestProject.Section31.ContinuousPathFiniteStoppingTimeMarkov
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! Conditional expectation is identified by the already derived event
integrals and the measurable stopped canonical state. The result concerns
everywhere finite stopping times in the natural filtration and continuous
single-time terminal tests. No conditional-expectation identity is an input. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 6000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance continuousStoppingConditionalExpectationMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance continuousStoppingConditionalExpectationBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem continuousPath_finite_stoppingTime_condExp_markov
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime canonicalContinuousPathFiltration
      (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (delay : ℝ≥0) (terminal : C(State, ℝ)) :
    MeasureTheory.condExp stopping.measurableSpace (law : Measure C(ℝ≥0, State))
        (fun path => terminal (path (stoppingTime path + delay))) =ᵐ[(law : Measure C(ℝ≥0, State))]
      (fun path => semigroup delay terminal (path (stoppingTime path))) := by
  have futureIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      terminal (path (stoppingTime path + delay))) (law : Measure C(ℝ≥0, State)) := by
    simpa using canonical_stopping_future_continuousTest_integrable law
      (fun path => (stoppingTime path : WithTop ℝ≥0)) stopping delay terminal
  have currentIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      semigroup delay terminal (path (stoppingTime path))) (law : Measure C(ℝ≥0, State)) := by
    simpa using canonical_stopping_future_continuousTest_integrable law
      (fun path => (stoppingTime path : WithTop ℝ≥0)) stopping 0 (semigroup delay terminal)
  have currentMeasurable : Measurable[stopping.measurableSpace] (fun path : C(ℝ≥0, State) =>
      semigroup delay terminal (path (stoppingTime path))) := by
    have stoppedMeasurable := canonicalContinuousPathProcess_stoppedValue_measurable
      (fun path => (stoppingTime path : WithTop ℝ≥0)) stopping
    simpa [stoppedValue, canonicalContinuousPathProcess] using
      (semigroup delay terminal).continuous.measurable.comp stoppedMeasurable
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq stopping.measurableSpace_le futureIntegrable
    (fun _ _ _ => currentIntegrable.integrableOn) ?_ currentMeasurable.aestronglyMeasurable
  intro event eventMeasurable eventFinite
  exact (continuousPath_finite_stoppingTime_setIntegral_markov law semigroup start positive observations
    stoppingTime stopping delay terminal event eventMeasurable).symm

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_stoppingTime_condExp_markov
