import RequestProject.Section31.ContinuousPathStoppingFutureLaw
import RequestProject.Section31.ContinuousPathUsualStoppingMarkov

/-! The full future-path property in the usual augmentation, on every
everywhere finite stopping time. The stopped probability kernel is required
pointwise to be the given global family's kernel at the stopped state.
Existential kernel packaging avoids putting a measurability proof in the
statement; it does not permit changing the family or its rows. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators
noncomputable section

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance usualFuturePathMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance usualFuturePathBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def ContinuousPathUsualFiniteFutureLawProperties
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State)))) : Prop :=
  ∀ (start : State) (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime (canonicalUsualContinuousPathFiltration (globalLaws start))
      (fun path => (stoppingTime path : WithTop ℝ≥0))),
    ∃ stoppedKernel : @Kernel C(ℝ≥0, State) C(ℝ≥0, State)
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
      (borel C(ℝ≥0, State)),
      (∀ path, stoppedKernel path = continuousPathFamilyKernel globalLaws familyMeasurable
        (ContinuousMap.toFun path (stoppingTime path))) ∧
      ∀ (event : Set C(ℝ≥0, State)), MeasurableSet[stopping.measurableSpace] event →
        @Measure.map C(ℝ≥0, State) C(ℝ≥0, State)
          (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
          (borel C(ℝ≥0, State)) (continuousPathRandomShift stoppingTime)
          ((globalLaws start : Measure C(ℝ≥0, State)).completion.restrict event) =
            (stoppedKernel ∘ₖ Kernel.const Unit ((globalLaws start : Measure C(ℝ≥0, State)).completion.restrict event)) ()

theorem continuousPath_usualFiniteFutureLawProperties_of_ordered_observations
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
    ContinuousPathUsualFiniteFutureLawProperties globalLaws familyMeasurable := by
  intro start stoppingTime stopping
  letI usualFutureCompletionFiniteMeasure : IsFiniteMeasure (globalLaws start : Measure C(ℝ≥0, State)).completion :=
    ⟨measure_lt_top (globalLaws start : Measure C(ℝ≥0, State)) Set.univ⟩
  letI usualFutureCompletionOpensMeasurableSpace : @OpensMeasurableSpace C(ℝ≥0, State) inferInstance
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State)))) :=
    @OpensMeasurableSpace.mk C(ℝ≥0, State) inferInstance
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
      (le_eventuallyMeasurableSpace (m := borel C(ℝ≥0, State)) (l := ae (globalLaws start : Measure C(ℝ≥0, State))))
  have banachObservations : ContinuousPathOrderedBanachObservations (globalLaws start) semigroup start := by
    intro times timesMonotone startsAtZero tests count terminal
    exact (orderedObservations start times timesMonotone startsAtZero tests count terminal).trans
      (congrFun (ContinuousMarkov.kernelBackwardProduct_eq_semigroupBackwardProduct
        semigroup positive preservesOne _ terminal) start)
  let stoppedKernel : @Kernel C(ℝ≥0, State) C(ℝ≥0, State)
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
      (borel C(ℝ≥0, State)) :=
    (continuousPathFamilyKernel globalLaws familyMeasurable).comap
      (fun path => ContinuousMap.toFun path (stoppingTime path))
      ((continuousPath_finite_stoppingTime_state_measurable
        (ambient := eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
        (canonicalUsualContinuousPathFiltration (globalLaws start))
        (canonicalNatural_le_usualPathFiltration (globalLaws start)) stoppingTime stopping).mono
        stopping.measurableSpace_le le_rfl)
  refine ⟨stoppedKernel, fun _ => rfl, ?_⟩
  intro event eventMeasurable
  exact continuousPath_finite_stoppingTime_futureLaw_markov
    (ambient := eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (globalLaws start : Measure C(ℝ≥0, State))))
    (globalLaws start : Measure C(ℝ≥0, State)).completion
    (canonicalUsualContinuousPathFiltration (globalLaws start))
    (canonicalNatural_le_usualPathFiltration (globalLaws start)) semigroup positive preservesOne
    (continuousPath_usual_setIntegral_markov (globalLaws start) semigroup start positive banachObservations)
    globalLaws familyMeasurable orderedObservations stoppingTime stopping event eventMeasurable

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_usualFiniteFutureLawProperties_of_ordered_observations
