import RequestProject.Section31.ContinuousPathExtendedFutureConditionalExpectation
import RequestProject.Section31.ContinuousPathUsualStoppingMarkov

/-! The full future-path property in the usual augmentation, on every
extended stopping time on its finite-value event. The stopped probability kernel is required
pointwise to be the given global family's kernel at the stopped state.
Existential kernel packaging avoids putting a measurability proof in the
statement; it does not permit changing the family or its rows. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators
noncomputable section

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance usualExtendedFuturePathMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance usualExtendedFuturePathBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def ContinuousPathUsualExtendedFutureLawProperties
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State)))) : Prop :=
  ∀ (start : State) (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime (canonicalUsualContinuousPathFiltration (globalLaws start)) stoppingTime),
    ∃ stoppedKernel : @Kernel C(ℝ≥0, State) C(ℝ≥0, State)
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
      (borel C(ℝ≥0, State)),
      (∀ path, stoppedKernel path = continuousPathFamilyKernel globalLaws familyMeasurable
        (ContinuousMap.toFun path (stoppingTime path).untopA)) ∧
      (∀ (event : Set C(ℝ≥0, State)), MeasurableSet[stopping.measurableSpace] event →
        @Measure.map C(ℝ≥0, State) C(ℝ≥0, State)
          (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
          (borel C(ℝ≥0, State)) (continuousPathRandomShift (fun path => (stoppingTime path).untopA))
          ((globalLaws start : Measure C(ℝ≥0, State)).completion.restrict (event ∩ {path | stoppingTime path ≠ ⊤})) =
            (stoppedKernel ∘ₖ Kernel.const Unit ((globalLaws start : Measure C(ℝ≥0, State)).completion.restrict
              (event ∩ {path | stoppingTime path ≠ ⊤}))) ()) ∧
      ∀ (terminal : C(ℝ≥0, State) → ℝ) (terminalMeasurable : Measurable terminal)
        (bound : ℝ) (terminalBound : ∀ future, ‖terminal future‖ ≤ bound),
        condExp stopping.measurableSpace
            ((globalLaws start : Measure C(ℝ≥0, State)).completion.restrict {path | stoppingTime path ≠ ⊤})
            (fun path => terminal (continuousPathRandomShift (fun path => (stoppingTime path).untopA) path)) =ᵐ[
              (globalLaws start : Measure C(ℝ≥0, State)).completion.restrict {path | stoppingTime path ≠ ⊤}]
          (fun path => ∫ future, terminal future ∂(globalLaws (ContinuousMap.toFun path (stoppingTime path).untopA)
            : Measure C(ℝ≥0, State)))

theorem continuousPath_usualExtendedFutureLawProperties_of_ordered_observations
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State))))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (positive : ∀ time (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (orderedObservations : ∀ (start : State) (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)),
        (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
          terminal (path (times count)) ∂(globalLaws start : Measure C(ℝ≥0, State))) =
          ContinuousMarkov.kernelBackwardProduct
            (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
            ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start) :
    ContinuousPathUsualExtendedFutureLawProperties globalLaws familyMeasurable := by
  intro start stoppingTime stopping
  letI usualExtendedFutureCompletionFiniteMeasure : IsFiniteMeasure (globalLaws start : Measure C(ℝ≥0, State)).completion :=
    ⟨measure_lt_top (globalLaws start : Measure C(ℝ≥0, State)) Set.univ⟩
  letI usualExtendedFutureCompletionOpensMeasurableSpace : @OpensMeasurableSpace C(ℝ≥0, State) inferInstance
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State)))) :=
    @OpensMeasurableSpace.mk C(ℝ≥0, State) inferInstance
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
      (le_eventuallyMeasurableSpace (m := borel C(ℝ≥0, State)) (l := ae (globalLaws start : Measure C(ℝ≥0, State))))
  have banachObservations : ContinuousPathOrderedBanachObservations (globalLaws start) semigroup start := by
    intro times timesMonotone startsAtZero tests count terminal
    exact (orderedObservations start times timesMonotone startsAtZero tests count terminal).trans
      (congrFun (ContinuousMarkov.kernelBackwardProduct_eq_semigroupBackwardProduct
        semigroup positive preservesOne _ terminal) start)
  have timeMeasurable : @Measurable C(ℝ≥0, State) ℝ≥0
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
      inferInstance (fun path => (stoppingTime path).untopA) := stopping.measurable'.untopA
  have stateMeasurable : @Measurable C(ℝ≥0, State) State
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
      inferInstance (fun path => ContinuousMap.toFun path (stoppingTime path).untopA) := by
    letI usualExtendedFutureStateSourceMeasurableSpace : MeasurableSpace C(ℝ≥0, State) :=
      eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State)))
    exact continuous_eval.measurable.comp (measurable_id.prodMk timeMeasurable)
  let stoppedKernel : @Kernel C(ℝ≥0, State) C(ℝ≥0, State)
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
      (borel C(ℝ≥0, State)) :=
    (continuousPathFamilyKernel globalLaws familyMeasurable).comap
      (fun path => ContinuousMap.toFun path (stoppingTime path).untopA) stateMeasurable
  refine ⟨stoppedKernel, fun _ => rfl, ?_, ?_⟩
  · intro event eventMeasurable
    exact continuousPath_extended_stoppingTime_futureLaw_markov
      (ambient := eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
      (globalLaws start : Measure C(ℝ≥0, State)).completion
      (canonicalUsualContinuousPathFiltration (globalLaws start))
      (canonicalNatural_le_usualPathFiltration (globalLaws start)) semigroup positive preservesOne
      (continuousPath_usual_setIntegral_markov (globalLaws start) semigroup start positive banachObservations)
      globalLaws familyMeasurable orderedObservations stoppingTime stopping event eventMeasurable
  · intro terminal terminalMeasurable bound terminalBound
    exact continuousPath_extended_stoppingTime_boundedBorel_future_condExp_markov
      (ambient := eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
      (globalLaws start : Measure C(ℝ≥0, State)).completion
      (canonicalUsualContinuousPathFiltration (globalLaws start))
      (canonicalNatural_le_usualPathFiltration (globalLaws start)) semigroup positive preservesOne
      (continuousPath_usual_setIntegral_markov (globalLaws start) semigroup start positive banachObservations)
      globalLaws familyMeasurable orderedObservations stoppingTime stopping terminal terminalMeasurable bound terminalBound

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_usualExtendedFutureLawProperties_of_ordered_observations
