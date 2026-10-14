import RequestProject.Section31.ContinuousPathFiltrationCountableStoppingMarkov
import RequestProject.Section31.DyadicUpwardStoppingApproximation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! For a general filtration and completed ambient sigma algebra, continuous
single-time stopping identities follow from deterministic event identities
by countable dyadic approximations and dominated convergence. Conditional
expectation additionally uses adaptation of the canonical process. No target
stopping identity is a hypothesis. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open IGS.Sec31.StoppingApproximation
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 7000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

variable [ambient : MeasurableSpace C(ℝ≥0, State)] [OpensMeasurableSpace C(ℝ≥0, State)]

theorem continuousPath_filtration_finite_stoppingTime_setIntegral_markov
    (measure : Measure C(ℝ≥0, State)) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 ambient)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (deterministicMarkov : ∀ (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State)),
      MeasurableSet[filtration time] event →
      (∫ path in event, terminal (path (time + delay)) ∂measure) =
        ∫ path in event, semigroup delay terminal (path time) ∂measure)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime filtration
      (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    (∫ path in event, terminal (path (stoppingTime path + delay))
      ∂measure) =
      ∫ path in event, semigroup delay terminal (path (stoppingTime path))
        ∂measure := by
  have approximationStopping (level : ℕ) :
      IsStoppingTime filtration
        (fun path => (dyadicUpwardTime level (stoppingTime path) : WithTop ℝ≥0)) :=
    isStoppingTime_dyadicUpwardTime filtration stoppingTime stopping level
  have approximationEventMeasurable (level : ℕ) :
      MeasurableSet[(approximationStopping level).measurableSpace] event := by
    apply (stopping.measurableSpace_mono (approximationStopping level) ?_) _ eventMeasurable
    intro path
    dsimp only
    exact_mod_cast time_le_dyadicUpwardTime level (stoppingTime path)
  have approximationIdentity (level : ℕ) :
      (∫ path in event, terminal (path (dyadicUpwardTime level (stoppingTime path) + delay))
        ∂measure) =
        ∫ path in event, semigroup delay terminal (path (dyadicUpwardTime level (stoppingTime path)))
          ∂measure := by
    simpa using continuousPath_filtration_countable_stopping_setIntegral_markov measure filtration semigroup deterministicMarkov
      (fun path => (dyadicUpwardTime level (stoppingTime path) : WithTop ℝ≥0)) (approximationStopping level)
      (Set.range (dyadicUpwardTime level)) (dyadicUpwardTime_range_countable level)
      (fun path => ⟨dyadicUpwardTime level (stoppingTime path), ⟨stoppingTime path, rfl⟩, rfl⟩)
      delay terminal event (approximationEventMeasurable level)
  have futureMeasurable (level : ℕ) :
      AEStronglyMeasurable (fun path : C(ℝ≥0, State) =>
        terminal (path (dyadicUpwardTime level (stoppingTime path) + delay)))
        (measure.restrict event) := by
    have integrability := canonical_filtration_stopping_future_continuousTest_integrable measure filtration
      (fun path => (dyadicUpwardTime level (stoppingTime path) : WithTop ℝ≥0))
      (approximationStopping level) delay terminal
    simpa using integrability.integrableOn.1
  have currentMeasurable (level : ℕ) :
      AEStronglyMeasurable (fun path : C(ℝ≥0, State) =>
        semigroup delay terminal (path (dyadicUpwardTime level (stoppingTime path))))
        (measure.restrict event) := by
    have integrability := canonical_filtration_stopping_future_continuousTest_integrable measure filtration
      (fun path => (dyadicUpwardTime level (stoppingTime path) : WithTop ℝ≥0))
      (approximationStopping level) 0 (semigroup delay terminal)
    simpa using integrability.integrableOn.1
  have futureLimit :
      Tendsto (fun level => ∫ path in event,
        terminal (path (dyadicUpwardTime level (stoppingTime path) + delay))
          ∂measure) atTop
        (𝓝 (∫ path in event, terminal (path (stoppingTime path + delay))
          ∂measure)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖terminal‖) futureMeasurable (integrable_const _)
    · intro level
      exact Eventually.of_forall fun path => terminal.norm_coe_le_norm _
    · exact Eventually.of_forall fun path =>
        (terminal.continuous.comp path.continuous).continuousAt.tendsto.comp
          ((dyadicUpwardTime_tendsto (stoppingTime path)).add_const delay)
  have currentLimit :
      Tendsto (fun level => ∫ path in event,
        semigroup delay terminal (path (dyadicUpwardTime level (stoppingTime path)))
          ∂measure) atTop
        (𝓝 (∫ path in event, semigroup delay terminal (path (stoppingTime path))
          ∂measure)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖semigroup delay terminal‖)
      currentMeasurable (integrable_const _)
    · intro level
      exact Eventually.of_forall fun path => (semigroup delay terminal).norm_coe_le_norm _
    · exact Eventually.of_forall fun path =>
        ((semigroup delay terminal).continuous.comp path.continuous).continuousAt.tendsto.comp
          (dyadicUpwardTime_tendsto (stoppingTime path))
  exact tendsto_nhds_unique futureLimit (currentLimit.congr fun level => (approximationIdentity level).symm)

theorem continuousPath_filtration_finite_stoppingTime_condExp_markov
    (measure : Measure C(ℝ≥0, State)) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 ambient)
    (naturalBelow : ∀ time, canonicalContinuousPathFiltration (State := State) time ≤ filtration time)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (deterministicMarkov : ∀ (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State)),
      MeasurableSet[filtration time] event →
      (∫ path in event, terminal (path (time + delay)) ∂measure) =
        ∫ path in event, semigroup delay terminal (path time) ∂measure)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime filtration (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (delay : ℝ≥0) (terminal : C(State, ℝ)) :
    MeasureTheory.condExp stopping.measurableSpace measure
        (fun path => terminal (path (stoppingTime path + delay))) =ᵐ[measure]
      (fun path => semigroup delay terminal (path (stoppingTime path))) := by
  have futureIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      terminal (path (stoppingTime path + delay))) measure := by
    simpa using canonical_filtration_stopping_future_continuousTest_integrable measure filtration
      (fun path => (stoppingTime path : WithTop ℝ≥0)) stopping delay terminal
  have currentIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      semigroup delay terminal (path (stoppingTime path))) measure := by
    simpa using canonical_filtration_stopping_future_continuousTest_integrable measure filtration
      (fun path => (stoppingTime path : WithTop ℝ≥0)) stopping 0 (semigroup delay terminal)
  have adapted : StronglyAdapted filtration canonicalContinuousPathProcess :=
    fun time => (canonicalContinuousPathProcess_stronglyAdapted time).mono (naturalBelow time)
  have progressive : ProgMeasurable filtration canonicalContinuousPathProcess :=
    adapted.progMeasurable_of_continuous canonicalContinuousPathProcess_continuous
  have currentMeasurable : Measurable[stopping.measurableSpace] (fun path : C(ℝ≥0, State) =>
      semigroup delay terminal (path (stoppingTime path))) := by
    have stoppedMeasurable := measurable_stoppedValue progressive stopping
    simpa [stoppedValue, canonicalContinuousPathProcess] using
      (semigroup delay terminal).continuous.measurable.comp stoppedMeasurable
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq stopping.measurableSpace_le futureIntegrable
    (fun _ _ _ => currentIntegrable.integrableOn) ?_ currentMeasurable.aestronglyMeasurable
  intro event eventMeasurable eventFinite
  exact (continuousPath_filtration_finite_stoppingTime_setIntegral_markov measure filtration semigroup
    deterministicMarkov stoppingTime stopping delay terminal event eventMeasurable).symm

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_filtration_finite_stoppingTime_setIntegral_markov
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_filtration_finite_stoppingTime_condExp_markov
