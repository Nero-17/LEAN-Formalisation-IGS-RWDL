import RequestProject.Section31.ContinuousPathBoundedBorelStoppingMarkov
import RequestProject.Section31.NNRealStoppingTimeLocalization

/-! Localize extended stopping times to finite deterministic cutoffs and
pass to the increasing union of their finite-value events. Bounded Borel
single-time identities hold on {stoppingTime ≠ infinity}; conditional
expectation is taken under the measure restricted to this event. No process
state at an infinite stopping time is asserted. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open IGS.Sec31.StoppingApproximation
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 8000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable [ambient : MeasurableSpace C(ℝ≥0, State)] [OpensMeasurableSpace C(ℝ≥0, State)]

theorem continuousPath_extended_stoppingTime_boundedBorel_setIntegral_markov
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
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0) (stopping : IsStoppingTime filtration stoppingTime)
    (delay : ℝ≥0) (terminal : State → ℝ) (terminalMeasurable : Measurable terminal)
    (bound : ℝ) (terminalBound : ∀ point, ‖terminal point‖ ≤ bound)
    (event : Set C(ℝ≥0, State)) (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    (∫ path in event ∩ {path | stoppingTime path ≠ ⊤},
      terminal (path ((stoppingTime path).untopA + delay)) ∂measure) =
      ∫ path in event ∩ {path | stoppingTime path ≠ ⊤},
        ∫ location, terminal location ∂kernel delay (path (stoppingTime path).untopA) ∂measure := by
  letI extendedStoppingKernelMarkov : IsMarkovKernel (kernel delay) := kernelMarkov delay
  let localizedEvents (cutoff : ℕ) : Set C(ℝ≥0, State) :=
    event ∩ {path | stoppingTime path ≤ ((cutoff : ℝ≥0) : WithTop ℝ≥0)}
  have eventGlobalMeasurable : MeasurableSet event := stopping.measurableSpace_le _ eventMeasurable
  have localizedMeasurable (cutoff : ℕ) : MeasurableSet (localizedEvents cutoff) :=
    eventGlobalMeasurable.inter (stopping.measurableSpace_le _ (stopping.measurableSet_le' (cutoff : ℝ≥0)))
  have localizedMonotone : Monotone localizedEvents := by
    intro first second ordered path membership
    refine ⟨membership.1, membership.2.trans ?_⟩
    exact_mod_cast ordered
  have unionEquality : (⋃ cutoff : ℕ, localizedEvents cutoff) = event ∩ {path | stoppingTime path ≠ ⊤} := by
    dsimp only [localizedEvents]
    rw [← Set.inter_iUnion, iUnion_stoppingTime_le_nat]
  have futureStateMeasurable : Measurable (fun path : C(ℝ≥0, State) => path ((stoppingTime path).untopA + delay)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk (stopping.measurable'.untopA.add_const delay))
  have stoppedStateMeasurable : Measurable (fun path : C(ℝ≥0, State) => path (stoppingTime path).untopA) :=
    continuous_eval.measurable.comp (measurable_id.prodMk stopping.measurable'.untopA)
  have futureIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      terminal (path ((stoppingTime path).untopA + delay))) measure :=
    Integrable.of_bound (terminalMeasurable.comp futureStateMeasurable).aestronglyMeasurable bound
      (Eventually.of_forall fun path => terminalBound _)
  have kernelExpectationStronglyMeasurable : StronglyMeasurable
      (fun point : State => ∫ location, terminal location ∂kernel delay point) :=
    terminalMeasurable.stronglyMeasurable.integral_kernel
  have expectationBound (point : State) : ‖∫ location, terminal location ∂kernel delay point‖ ≤ bound := by
    simpa using (norm_integral_le_of_norm_le_const (μ := kernel delay point) (Eventually.of_forall terminalBound))
  have currentIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      ∫ location, terminal location ∂kernel delay (path (stoppingTime path).untopA)) measure :=
    Integrable.of_bound
      (kernelExpectationStronglyMeasurable.measurable.comp stoppedStateMeasurable).aestronglyMeasurable bound
      (Eventually.of_forall fun path => expectationBound _)
  have localizedIdentity (cutoff : ℕ) :
      (∫ path in localizedEvents cutoff, terminal (path ((stoppingTime path).untopA + delay)) ∂measure) =
        ∫ path in localizedEvents cutoff, ∫ location, terminal location
          ∂kernel delay (path (stoppingTime path).untopA) ∂measure := by
    have truncatedIdentity := continuousPath_finite_stoppingTime_boundedBorel_setIntegral_markov measure filtration
      semigroup deterministicMarkov kernel kernelMarkov kernelContinuous
      (finiteTruncation stoppingTime (cutoff : ℝ≥0))
      (finiteTruncation_isStoppingTime filtration stoppingTime stopping (cutoff : ℝ≥0)) delay terminal
      terminalMeasurable bound terminalBound (localizedEvents cutoff)
      (finiteTruncation_localized_event_measurable filtration stoppingTime stopping (cutoff : ℝ≥0)
        event eventMeasurable)
    calc
      _ = ∫ path in localizedEvents cutoff,
          terminal (path (finiteTruncation stoppingTime (cutoff : ℝ≥0) path + delay)) ∂measure := by
        apply setIntegral_congr_fun (localizedMeasurable cutoff)
        intro path membership
        have timeBound : stoppingTime path ≤ ((cutoff : ℝ≥0) : WithTop ℝ≥0) := membership.2
        dsimp only
        rw [finiteTruncation_eq_of_le stoppingTime (cutoff : ℝ≥0) path timeBound]
      _ = ∫ path in localizedEvents cutoff, ∫ location, terminal location
          ∂kernel delay (path (finiteTruncation stoppingTime (cutoff : ℝ≥0) path)) ∂measure := truncatedIdentity
      _ = _ := by
        apply setIntegral_congr_fun (localizedMeasurable cutoff)
        intro path membership
        have timeBound : stoppingTime path ≤ ((cutoff : ℝ≥0) : WithTop ℝ≥0) := membership.2
        dsimp only
        rw [finiteTruncation_eq_of_le stoppingTime (cutoff : ℝ≥0) path timeBound]
  have futureLimit := tendsto_setIntegral_of_monotone localizedMeasurable localizedMonotone futureIntegrable.integrableOn
  have currentLimit := tendsto_setIntegral_of_monotone localizedMeasurable localizedMonotone currentIntegrable.integrableOn
  simpa only [unionEquality] using
    tendsto_nhds_unique futureLimit (currentLimit.congr fun cutoff => (localizedIdentity cutoff).symm)

theorem continuousPath_extended_stoppingTime_boundedBorel_condExp_markov
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
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0) (stopping : IsStoppingTime filtration stoppingTime)
    (delay : ℝ≥0) (terminal : State → ℝ) (terminalMeasurable : Measurable terminal)
    (bound : ℝ) (terminalBound : ∀ point, ‖terminal point‖ ≤ bound) :
    MeasureTheory.condExp stopping.measurableSpace (measure.restrict {path | stoppingTime path ≠ ⊤})
        (fun path => terminal (path ((stoppingTime path).untopA + delay))) =ᵐ[
          measure.restrict {path | stoppingTime path ≠ ⊤}]
      (fun path => ∫ location, terminal location ∂kernel delay (path (stoppingTime path).untopA)) := by
  letI extendedStoppingCondExpKernelMarkov : IsMarkovKernel (kernel delay) := kernelMarkov delay
  have futureStateMeasurable : Measurable (fun path : C(ℝ≥0, State) => path ((stoppingTime path).untopA + delay)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk (stopping.measurable'.untopA.add_const delay))
  have futureIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      terminal (path ((stoppingTime path).untopA + delay))) measure :=
    Integrable.of_bound (terminalMeasurable.comp futureStateMeasurable).aestronglyMeasurable bound
      (Eventually.of_forall fun path => terminalBound _)
  have adapted : StronglyAdapted filtration canonicalContinuousPathProcess :=
    fun time => (canonicalContinuousPathProcess_stronglyAdapted time).mono (naturalBelow time)
  have progressive : ProgMeasurable filtration canonicalContinuousPathProcess :=
    adapted.progMeasurable_of_continuous canonicalContinuousPathProcess_continuous
  have stoppedStateMeasurable : Measurable[stopping.measurableSpace]
      (fun path : C(ℝ≥0, State) => path (stoppingTime path).untopA) := by
    simpa [stoppedValue, canonicalContinuousPathProcess] using measurable_stoppedValue progressive stopping
  have kernelExpectationStronglyMeasurable : StronglyMeasurable
      (fun point : State => ∫ location, terminal location ∂kernel delay point) :=
    terminalMeasurable.stronglyMeasurable.integral_kernel
  have currentMeasurable : Measurable[stopping.measurableSpace] (fun path : C(ℝ≥0, State) =>
      ∫ location, terminal location ∂kernel delay (path (stoppingTime path).untopA)) :=
    kernelExpectationStronglyMeasurable.measurable.comp stoppedStateMeasurable
  have expectationBound (point : State) : ‖∫ location, terminal location ∂kernel delay point‖ ≤ bound := by
    simpa using (norm_integral_le_of_norm_le_const (μ := kernel delay point) (Eventually.of_forall terminalBound))
  have currentIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      ∫ location, terminal location ∂kernel delay (path (stoppingTime path).untopA)) measure :=
    Integrable.of_bound
      (currentMeasurable.mono stopping.measurableSpace_le le_rfl).aestronglyMeasurable bound
      (Eventually.of_forall fun path => expectationBound _)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq stopping.measurableSpace_le futureIntegrable.integrableOn
    (fun _ _ _ => currentIntegrable.integrableOn.integrableOn) ?_ currentMeasurable.aestronglyMeasurable
  intro event eventMeasurable eventFinite
  have eventGlobalMeasurable := stopping.measurableSpace_le event eventMeasurable
  change (∫ path, (∫ location, terminal location ∂kernel delay (path (stoppingTime path).untopA))
      ∂(measure.restrict {path | stoppingTime path ≠ ⊤}).restrict event) =
    ∫ path, terminal (path ((stoppingTime path).untopA + delay))
      ∂(measure.restrict {path | stoppingTime path ≠ ⊤}).restrict event
  rw [Measure.restrict_restrict eventGlobalMeasurable]
  exact (continuousPath_extended_stoppingTime_boundedBorel_setIntegral_markov measure filtration semigroup
    deterministicMarkov kernel kernelMarkov kernelContinuous stoppingTime stopping delay terminal
    terminalMeasurable bound terminalBound event eventMeasurable).symm

theorem continuousPath_aeFinite_stoppingTime_boundedBorel_condExp_markov
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
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0) (stopping : IsStoppingTime filtration stoppingTime)
    (aeFinite : ∀ᵐ path ∂measure, stoppingTime path ≠ ⊤)
    (delay : ℝ≥0) (terminal : State → ℝ) (terminalMeasurable : Measurable terminal)
    (bound : ℝ) (terminalBound : ∀ point, ‖terminal point‖ ≤ bound) :
    MeasureTheory.condExp stopping.measurableSpace measure
        (fun path => terminal (path ((stoppingTime path).untopA + delay))) =ᵐ[measure]
      (fun path => ∫ location, terminal location ∂kernel delay (path (stoppingTime path).untopA)) := by
  have restrictionEquality : measure.restrict {path | stoppingTime path ≠ ⊤} = measure :=
    Measure.restrict_eq_self_of_ae_mem aeFinite
  simpa only [restrictionEquality] using
    continuousPath_extended_stoppingTime_boundedBorel_condExp_markov measure filtration naturalBelow semigroup
      deterministicMarkov kernel kernelMarkov kernelContinuous stoppingTime stopping delay terminal
      terminalMeasurable bound terminalBound

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_extended_stoppingTime_boundedBorel_setIntegral_markov
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_extended_stoppingTime_boundedBorel_condExp_markov
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_aeFinite_stoppingTime_boundedBorel_condExp_markov
