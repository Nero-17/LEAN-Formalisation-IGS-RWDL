import RequestProject.Section31.ContinuousPathFiltrationFiniteStoppingTimeMarkov
import RequestProject.Section31.ContinuousMarkovKernel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! Extend finite-stopping continuous single-time test identities to bounded
Borel state tests by equality of finite state measures. The transition kernel
is required only to represent the given semigroup on continuous tests. The
bounded-Borel stopping identity is proved, not assumed. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 7000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable [ambient : MeasurableSpace C(ℝ≥0, State)] [OpensMeasurableSpace C(ℝ≥0, State)]

theorem continuousPath_finite_stoppingTime_boundedBorel_setIntegral_markov
    (measure : Measure C(ℝ≥0, State)) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 ambient)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (deterministicMarkov : ∀ (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State)),
      MeasurableSet[filtration time] event →
      (∫ path in event, terminal (path (time + delay)) ∂measure) =
        ∫ path in event, semigroup delay terminal (path time) ∂measure)
    (kernel : ℝ≥0 → Kernel State State) (kernelMarkov : ∀ delay, IsMarkovKernel (kernel delay))
    (kernelContinuous : ∀ delay point (function : C(State, ℝ)),
      (∫ location, function location ∂kernel delay point) = semigroup delay function point)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime filtration (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (delay : ℝ≥0) (terminal : State → ℝ) (terminalMeasurable : Measurable terminal)
    (bound : ℝ) (terminalBound : ∀ point, ‖terminal point‖ ≤ bound)
    (event : Set C(ℝ≥0, State)) (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    (∫ path in event, terminal (path (stoppingTime path + delay)) ∂measure) =
      ∫ path in event, ∫ location, terminal location ∂kernel delay (path (stoppingTime path)) ∂measure := by
  letI boundedBorelStoppingKernelMarkov : IsMarkovKernel (kernel delay) := kernelMarkov delay
  have stoppingTimeMeasurable : Measurable stoppingTime := by
    simpa using stopping.measurable'.untopA
  have stoppedStateMeasurable : Measurable (fun path : C(ℝ≥0, State) => path (stoppingTime path)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk stoppingTimeMeasurable)
  have futureStateMeasurable : Measurable (fun path : C(ℝ≥0, State) => path (stoppingTime path + delay)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk (stoppingTimeMeasurable.add_const delay))
  let stoppedKernel : Kernel C(ℝ≥0, State) State :=
    (kernel delay).comap (fun path => path (stoppingTime path)) stoppedStateMeasurable
  let eventKernel : Kernel Unit C(ℝ≥0, State) := Kernel.const Unit (measure.restrict event)
  have measureEquality :
      (measure.restrict event).map (fun path => path (stoppingTime path + delay)) =
        (stoppedKernel ∘ₖ eventKernel) () := by
    apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro test
    have compositionIntegral := Kernel.integral_comp (κ := eventKernel) (η := stoppedKernel) (a := ())
      (test.integrable _)
    rw [integral_map futureStateMeasurable.aemeasurable test.continuous.measurable.aestronglyMeasurable]
    calc
      _ = ∫ path in event, semigroup delay test.toContinuousMap (path (stoppingTime path)) ∂measure :=
        continuousPath_filtration_finite_stoppingTime_setIntegral_markov measure filtration semigroup
          deterministicMarkov stoppingTime stopping delay test.toContinuousMap event eventMeasurable
      _ = ∫ path in event, ∫ location, test location ∂kernel delay (path (stoppingTime path)) ∂measure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun path =>
          (kernelContinuous delay (path (stoppingTime path)) test.toContinuousMap).symm
      _ = ∫ location, test location ∂(stoppedKernel ∘ₖ eventKernel) () := by
        simpa only [stoppedKernel, eventKernel, Kernel.const_apply, Kernel.comap_apply] using compositionIntegral.symm
  have terminalIntegrable : Integrable terminal ((stoppedKernel ∘ₖ eventKernel) ()) :=
    Integrable.of_bound terminalMeasurable.aestronglyMeasurable bound (Eventually.of_forall terminalBound)
  have compositionIntegral := Kernel.integral_comp (κ := eventKernel) (η := stoppedKernel) (a := ()) terminalIntegrable
  calc
    _ = ∫ location, terminal location
        ∂(measure.restrict event).map (fun path => path (stoppingTime path + delay)) :=
      (integral_map futureStateMeasurable.aemeasurable terminalMeasurable.aestronglyMeasurable).symm
    _ = ∫ location, terminal location ∂(stoppedKernel ∘ₖ eventKernel) () := by rw [measureEquality]
    _ = _ := by
      simpa only [stoppedKernel, eventKernel, Kernel.const_apply, Kernel.comap_apply] using compositionIntegral

theorem continuousPath_finite_stoppingTime_boundedBorel_condExp_markov
    (measure : Measure C(ℝ≥0, State)) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 ambient)
    (naturalBelow : ∀ time, canonicalContinuousPathFiltration (State := State) time ≤ filtration time)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (deterministicMarkov : ∀ (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State)),
      MeasurableSet[filtration time] event →
      (∫ path in event, terminal (path (time + delay)) ∂measure) =
        ∫ path in event, semigroup delay terminal (path time) ∂measure)
    (kernel : ℝ≥0 → Kernel State State) (kernelMarkov : ∀ delay, IsMarkovKernel (kernel delay))
    (kernelContinuous : ∀ delay point (function : C(State, ℝ)),
      (∫ location, function location ∂kernel delay point) = semigroup delay function point)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime filtration (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (delay : ℝ≥0) (terminal : State → ℝ) (terminalMeasurable : Measurable terminal)
    (bound : ℝ) (terminalBound : ∀ point, ‖terminal point‖ ≤ bound) :
    MeasureTheory.condExp stopping.measurableSpace measure
        (fun path => terminal (path (stoppingTime path + delay))) =ᵐ[measure]
      (fun path => ∫ location, terminal location ∂kernel delay (path (stoppingTime path))) := by
  letI boundedBorelStoppingCondExpKernelMarkov : IsMarkovKernel (kernel delay) := kernelMarkov delay
  have stoppingTimeMeasurable : Measurable stoppingTime := by
    simpa using stopping.measurable'.untopA
  have futureStateMeasurable : Measurable (fun path : C(ℝ≥0, State) => path (stoppingTime path + delay)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk (stoppingTimeMeasurable.add_const delay))
  have futureIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      terminal (path (stoppingTime path + delay))) measure :=
    Integrable.of_bound (terminalMeasurable.comp futureStateMeasurable).aestronglyMeasurable bound
      (Eventually.of_forall fun path => terminalBound _)
  have adapted : StronglyAdapted filtration canonicalContinuousPathProcess :=
    fun time => (canonicalContinuousPathProcess_stronglyAdapted time).mono (naturalBelow time)
  have progressive : ProgMeasurable filtration canonicalContinuousPathProcess :=
    adapted.progMeasurable_of_continuous canonicalContinuousPathProcess_continuous
  have stoppedStateMeasurable : Measurable[stopping.measurableSpace]
      (fun path : C(ℝ≥0, State) => path (stoppingTime path)) := by
    simpa [stoppedValue, canonicalContinuousPathProcess] using measurable_stoppedValue progressive stopping
  have kernelExpectationStronglyMeasurable : StronglyMeasurable
      (fun point : State => ∫ location, terminal location ∂kernel delay point) :=
    terminalMeasurable.stronglyMeasurable.integral_kernel
  have currentMeasurable : Measurable[stopping.measurableSpace] (fun path : C(ℝ≥0, State) =>
      ∫ location, terminal location ∂kernel delay (path (stoppingTime path))) :=
    kernelExpectationStronglyMeasurable.measurable.comp stoppedStateMeasurable
  have expectationBound (point : State) : ‖∫ location, terminal location ∂kernel delay point‖ ≤ bound := by
    simpa using (norm_integral_le_of_norm_le_const (μ := kernel delay point) (Eventually.of_forall terminalBound))
  have currentIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      ∫ location, terminal location ∂kernel delay (path (stoppingTime path))) measure :=
    Integrable.of_bound
      (currentMeasurable.mono stopping.measurableSpace_le le_rfl).aestronglyMeasurable bound
      (Eventually.of_forall fun path => expectationBound _)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq stopping.measurableSpace_le futureIntegrable
    (fun _ _ _ => currentIntegrable.integrableOn) ?_ currentMeasurable.aestronglyMeasurable
  intro event eventMeasurable eventFinite
  exact (continuousPath_finite_stoppingTime_boundedBorel_setIntegral_markov measure filtration semigroup
    deterministicMarkov kernel kernelMarkov kernelContinuous stoppingTime stopping delay terminal
    terminalMeasurable bound terminalBound event eventMeasurable).symm

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_stoppingTime_boundedBorel_setIntegral_markov
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_stoppingTime_boundedBorel_condExp_markov
