import RequestProject.Section31.ContinuousPathMarkovPastEvents

/-! The natural-filtration Markov integral identity at finite-valued stopping
times follows by partitioning into the events where the stopping time equals
each of its finitely many real values. No right-continuity of the filtration
and no stopping-time Markov identity are hypotheses. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 6000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance continuousFiniteStoppingMarkovMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance continuousFiniteStoppingMarkovBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem canonical_finite_stopping_future_continuousTest_integrable
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime canonicalContinuousPathFiltration stoppingTime)
    (finiteTimes : Finset ℝ≥0)
    (finiteValues : ∀ path, stoppingTime path ∈ WithTop.some '' (finiteTimes : Set ℝ≥0))
    (delay : ℝ≥0) (terminal : C(State, ℝ)) :
    Integrable (fun path : C(ℝ≥0, State) => terminal (path ((stoppingTime path).untopA + delay)))
      (law : Measure C(ℝ≥0, State)) := by
  exact integrable_stoppedValue_of_mem_finset stopping
    (fun time => canonical_eval_continuousTest_integrable law (time + delay) terminal) finiteValues

theorem continuousPath_finite_stopping_setIntegral_markov
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime canonicalContinuousPathFiltration stoppingTime)
    (finiteTimes : Finset ℝ≥0)
    (finiteValues : ∀ path, stoppingTime path ∈ WithTop.some '' (finiteTimes : Set ℝ≥0))
    (delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    (∫ path in event, terminal (path ((stoppingTime path).untopA + delay))
      ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path in event, semigroup delay terminal (path ((stoppingTime path).untopA))
        ∂(law : Measure C(ℝ≥0, State)) := by
  have levelGlobalMeasurable (time : ℝ≥0) : MeasurableSet {path | stoppingTime path = time} :=
    stopping.measurableSpace_le _ (stopping.measurableSet_eq' time)
  change (∫ path in event,
    stoppedValue (fun time (path : C(ℝ≥0, State)) => terminal (path (time + delay))) stoppingTime path
      ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path in event,
        stoppedValue (fun time (path : C(ℝ≥0, State)) => semigroup delay terminal (path time)) stoppingTime path
          ∂(law : Measure C(ℝ≥0, State))
  rw [stoppedValue_eq_of_mem_finset finiteValues, stoppedValue_eq_of_mem_finset finiteValues]
  simp only [Finset.sum_apply]
  rw [integral_finset_sum finiteTimes
      (fun time _ => ((canonical_eval_continuousTest_integrable law (time + delay) terminal).indicator
        (levelGlobalMeasurable time)).integrableOn),
    integral_finset_sum finiteTimes
      (fun time _ => ((canonical_eval_continuousTest_integrable law time (semigroup delay terminal)).indicator
        (levelGlobalMeasurable time)).integrableOn)]
  apply Finset.sum_congr rfl
  intro time timeMembership
  rw [setIntegral_indicator (levelGlobalMeasurable time), setIntegral_indicator (levelGlobalMeasurable time)]
  exact continuousPath_natural_setIntegral_markov law semigroup start positive observations time delay terminal
    (event ∩ {path | stoppingTime path = time})
    ((stopping.measurableSet_inter_eq_iff event time).mp
      (eventMeasurable.inter (stopping.measurableSet_eq' time)))

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.canonical_finite_stopping_future_continuousTest_integrable
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_stopping_setIntegral_markov
