import RequestProject.Section31.ContinuousPathCountableStoppingMarkov
import RequestProject.Section31.DyadicUpwardStoppingApproximation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The continuous-test Markov event-integral identity at every everywhere
finite real stopping time follows from countable dyadic upper approximations
and dominated convergence along the canonical continuous trajectories.
This establishes the identity for the natural filtration and continuous
single-time terminal tests; usual augmentation, Borel terminal tests, and
path-future tests require further arguments. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open IGS.Sec31.StoppingApproximation
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 7000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance continuousFiniteStoppingTimeMarkovMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance continuousFiniteStoppingTimeMarkovBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem continuousPath_finite_stoppingTime_setIntegral_markov
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime canonicalContinuousPathFiltration
      (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    (∫ path in event, terminal (path (stoppingTime path + delay))
      ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path in event, semigroup delay terminal (path (stoppingTime path))
        ∂(law : Measure C(ℝ≥0, State)) := by
  have approximationStopping (level : ℕ) :
      IsStoppingTime canonicalContinuousPathFiltration
        (fun path => (dyadicUpwardTime level (stoppingTime path) : WithTop ℝ≥0)) :=
    isStoppingTime_dyadicUpwardTime canonicalContinuousPathFiltration stoppingTime stopping level
  have approximationEventMeasurable (level : ℕ) :
      MeasurableSet[(approximationStopping level).measurableSpace] event := by
    apply (stopping.measurableSpace_mono (approximationStopping level) ?_) _ eventMeasurable
    intro path
    dsimp only
    exact_mod_cast time_le_dyadicUpwardTime level (stoppingTime path)
  have approximationIdentity (level : ℕ) :
      (∫ path in event, terminal (path (dyadicUpwardTime level (stoppingTime path) + delay))
        ∂(law : Measure C(ℝ≥0, State))) =
        ∫ path in event, semigroup delay terminal (path (dyadicUpwardTime level (stoppingTime path)))
          ∂(law : Measure C(ℝ≥0, State)) := by
    simpa using continuousPath_countable_stopping_setIntegral_markov law semigroup start positive observations
      (fun path => (dyadicUpwardTime level (stoppingTime path) : WithTop ℝ≥0)) (approximationStopping level)
      (Set.range (dyadicUpwardTime level)) (dyadicUpwardTime_range_countable level)
      (fun path => ⟨dyadicUpwardTime level (stoppingTime path), ⟨stoppingTime path, rfl⟩, rfl⟩)
      delay terminal event (approximationEventMeasurable level)
  have futureMeasurable (level : ℕ) :
      AEStronglyMeasurable (fun path : C(ℝ≥0, State) =>
        terminal (path (dyadicUpwardTime level (stoppingTime path) + delay)))
        ((law : Measure C(ℝ≥0, State)).restrict event) := by
    have integrability := canonical_stopping_future_continuousTest_integrable law
      (fun path => (dyadicUpwardTime level (stoppingTime path) : WithTop ℝ≥0))
      (approximationStopping level) delay terminal
    simpa using integrability.integrableOn.1
  have currentMeasurable (level : ℕ) :
      AEStronglyMeasurable (fun path : C(ℝ≥0, State) =>
        semigroup delay terminal (path (dyadicUpwardTime level (stoppingTime path))))
        ((law : Measure C(ℝ≥0, State)).restrict event) := by
    have integrability := canonical_stopping_future_continuousTest_integrable law
      (fun path => (dyadicUpwardTime level (stoppingTime path) : WithTop ℝ≥0))
      (approximationStopping level) 0 (semigroup delay terminal)
    simpa using integrability.integrableOn.1
  have futureLimit :
      Tendsto (fun level => ∫ path in event,
        terminal (path (dyadicUpwardTime level (stoppingTime path) + delay))
          ∂(law : Measure C(ℝ≥0, State))) atTop
        (𝓝 (∫ path in event, terminal (path (stoppingTime path + delay))
          ∂(law : Measure C(ℝ≥0, State)))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖terminal‖) futureMeasurable (integrable_const _)
    · intro level
      exact Eventually.of_forall fun path => terminal.norm_coe_le_norm _
    · exact Eventually.of_forall fun path =>
        (terminal.continuous.comp path.continuous).continuousAt.tendsto.comp
          ((dyadicUpwardTime_tendsto (stoppingTime path)).add_const delay)
  have currentLimit :
      Tendsto (fun level => ∫ path in event,
        semigroup delay terminal (path (dyadicUpwardTime level (stoppingTime path)))
          ∂(law : Measure C(ℝ≥0, State))) atTop
        (𝓝 (∫ path in event, semigroup delay terminal (path (stoppingTime path))
          ∂(law : Measure C(ℝ≥0, State)))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖semigroup delay terminal‖)
      currentMeasurable (integrable_const _)
    · intro level
      exact Eventually.of_forall fun path => (semigroup delay terminal).norm_coe_le_norm _
    · exact Eventually.of_forall fun path =>
        ((semigroup delay terminal).continuous.comp path.continuous).continuousAt.tendsto.comp
          (dyadicUpwardTime_tendsto (stoppingTime path))
  exact tendsto_nhds_unique futureLimit (currentLimit.congr fun level => (approximationIdentity level).symm)

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_stoppingTime_setIntegral_markov
