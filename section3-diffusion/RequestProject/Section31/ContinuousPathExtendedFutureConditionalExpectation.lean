import RequestProject.Section31.ContinuousPathExtendedFutureLaw
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! Bounded Borel tests of the entire future path at an extended stopping
time. Conditional expectation is taken on its finite-value event, and then
on the original law when the stopping time is almost surely finite. The
full future measure identity is called internally, never assumed. -/

namespace IGS.Sec31.DiscreteMarkov
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 7000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable [ambient : MeasurableSpace C(ℝ≥0, State)] [OpensMeasurableSpace C(ℝ≥0, State)]

theorem continuousPath_extended_stoppingTime_boundedBorel_future_condExp_markov
    (measure : Measure C(ℝ≥0, State)) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 ambient)
    (naturalBelow : ∀ time, canonicalContinuousPathFiltration (State := State) time ≤ filtration time)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (positive : ∀ time (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (deterministicMarkov : ∀ (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State)),
      MeasurableSet[filtration time] event →
      (∫ path in event, terminal (path (time + delay)) ∂measure) =
        ∫ path in event, semigroup delay terminal (path time) ∂measure)
    (globalLaws : State → @ProbabilityMeasure C(ℝ≥0, State) (borel C(ℝ≥0, State)))
    (familyMeasurable : Measurable (fun point =>
      (globalLaws point : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State)))))
    (orderedObservations : ∀ (start : State) (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)),
        (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
          terminal (path (times count))
          ∂(globalLaws start : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State)))) =
          ContinuousMarkov.kernelBackwardProduct
            (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
            ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start)
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime filtration stoppingTime)
    (terminal : C(ℝ≥0, State) → ℝ)
    (terminalMeasurable : @Measurable C(ℝ≥0, State) ℝ (borel C(ℝ≥0, State)) (borel ℝ) terminal)
    (bound : ℝ) (terminalBound : ∀ future, ‖terminal future‖ ≤ bound) :
    condExp stopping.measurableSpace (measure.restrict {path | stoppingTime path ≠ ⊤})
        (fun path => terminal (continuousPathRandomShift (fun path => (stoppingTime path).untopA) path)) =ᵐ[
          measure.restrict {path | stoppingTime path ≠ ⊤}]
      (fun path => ∫ future, terminal future
        ∂(globalLaws (path (stoppingTime path).untopA) : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State)))) := by
  have timeMeasurable : Measurable (fun path => (stoppingTime path).untopA) := stopping.measurable'.untopA
  have shiftMeasurable := continuousPathRandomShift_measurable _ timeMeasurable
  have terminalStronglyMeasurable : StronglyMeasurable[borel C(ℝ≥0, State)] terminal := by
    letI extendedFutureTerminalStronglyMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
    exact terminalMeasurable.stronglyMeasurable
  have futureIntegrable : Integrable (fun path =>
      terminal (continuousPathRandomShift (fun path => (stoppingTime path).untopA) path)) measure :=
    Integrable.of_bound (terminalMeasurable.comp shiftMeasurable).aestronglyMeasurable bound
      (Eventually.of_forall fun path => terminalBound _)
  have adapted : StronglyAdapted filtration canonicalContinuousPathProcess :=
    fun time => (canonicalContinuousPathProcess_stronglyAdapted time).mono (naturalBelow time)
  have progressive : ProgMeasurable filtration canonicalContinuousPathProcess :=
    adapted.progMeasurable_of_continuous canonicalContinuousPathProcess_continuous
  have stoppedStateMeasurable : Measurable[stopping.measurableSpace]
      (fun path : C(ℝ≥0, State) => path (stoppingTime path).untopA) := by
    simpa [stoppedValue, canonicalContinuousPathProcess] using measurable_stoppedValue progressive stopping
  let familyKernel := continuousPathFamilyKernel globalLaws familyMeasurable
  letI extendedFutureCondExpFamilyMarkov : IsMarkovKernel familyKernel := by
    dsimp only [familyKernel]
    infer_instance
  have kernelExpectationStronglyMeasurable : StronglyMeasurable
      (fun point : State => ∫ future, terminal future ∂familyKernel point) :=
    terminalMeasurable.stronglyMeasurable.integral_kernel
  have currentMeasurable : Measurable[stopping.measurableSpace]
      (fun path : C(ℝ≥0, State) => ∫ future, terminal future ∂familyKernel (path (stoppingTime path).untopA)) :=
    kernelExpectationStronglyMeasurable.measurable.comp stoppedStateMeasurable
  have expectationBound (point : State) : ‖∫ future, terminal future ∂familyKernel point‖ ≤ bound := by
    simpa using (norm_integral_le_of_norm_le_const (μ := familyKernel point) (Eventually.of_forall terminalBound))
  have currentIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      ∫ future, terminal future ∂familyKernel (path (stoppingTime path).untopA)) measure :=
    Integrable.of_bound
      (currentMeasurable.mono stopping.measurableSpace_le le_rfl).aestronglyMeasurable bound
      (Eventually.of_forall fun path => expectationBound _)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq stopping.measurableSpace_le futureIntegrable.integrableOn
    (fun _ _ _ => currentIntegrable.integrableOn.integrableOn) ?_ currentMeasurable.aestronglyMeasurable
  intro event eventMeasurable eventFinite
  have eventGlobalMeasurable := stopping.measurableSpace_le event eventMeasurable
  change (∫ path, (∫ future, terminal future ∂familyKernel (path (stoppingTime path).untopA))
      ∂(measure.restrict {path | stoppingTime path ≠ ⊤}).restrict event) =
    ∫ path, terminal (continuousPathRandomShift (fun path => (stoppingTime path).untopA) path)
      ∂(measure.restrict {path | stoppingTime path ≠ ⊤}).restrict event
  rw [Measure.restrict_restrict eventGlobalMeasurable]
  let stoppedKernel : @Kernel C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State)) :=
    familyKernel.comap (fun path => path (stoppingTime path).untopA)
      (stoppedStateMeasurable.mono stopping.measurableSpace_le le_rfl)
  letI extendedFutureCondExpStoppedMarkov : IsMarkovKernel stoppedKernel := by
    dsimp only [stoppedKernel]
    infer_instance
  let eventKernel : Kernel Unit C(ℝ≥0, State) :=
    Kernel.const Unit (measure.restrict (event ∩ {path | stoppingTime path ≠ ⊤}))
  have terminalIntegrable : Integrable terminal ((stoppedKernel ∘ₖ eventKernel) ()) :=
    Integrable.of_bound terminalMeasurable.aestronglyMeasurable bound (Eventually.of_forall terminalBound)
  have compositionIntegral := Kernel.integral_comp (κ := eventKernel) (η := stoppedKernel) (a := ()) terminalIntegrable
  have measureIdentity := continuousPath_extended_stoppingTime_futureLaw_markov
    measure filtration naturalBelow semigroup positive preservesOne deterministicMarkov globalLaws familyMeasurable
    orderedObservations stoppingTime stopping event eventMeasurable
  symm
  calc
    _ = ∫ future, terminal future
        ∂@Measure.map C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State))
          (continuousPathRandomShift (fun path => (stoppingTime path).untopA))
          (measure.restrict (event ∩ {path | stoppingTime path ≠ ⊤})) :=
      (@integral_map_of_stronglyMeasurable C(ℝ≥0, State) ℝ inferInstance inferInstance ambient
        (measure.restrict (event ∩ {path | stoppingTime path ≠ ⊤}))
        C(ℝ≥0, State) (borel C(ℝ≥0, State))
        (continuousPathRandomShift (fun path => (stoppingTime path).untopA))
        shiftMeasurable terminal terminalStronglyMeasurable).symm
    _ = ∫ future, terminal future ∂(stoppedKernel ∘ₖ eventKernel) () := by
      rw [measureIdentity]
    _ = _ := by
      simpa only [stoppedKernel, eventKernel, Kernel.comap_apply, Kernel.const_apply] using compositionIntegral

theorem continuousPath_aeFinite_stoppingTime_boundedBorel_future_condExp_markov
    (measure : Measure C(ℝ≥0, State)) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 ambient)
    (naturalBelow : ∀ time, canonicalContinuousPathFiltration (State := State) time ≤ filtration time)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (positive : ∀ time (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (deterministicMarkov : ∀ (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State)),
      MeasurableSet[filtration time] event →
      (∫ path in event, terminal (path (time + delay)) ∂measure) =
        ∫ path in event, semigroup delay terminal (path time) ∂measure)
    (globalLaws : State → @ProbabilityMeasure C(ℝ≥0, State) (borel C(ℝ≥0, State)))
    (familyMeasurable : Measurable (fun point =>
      (globalLaws point : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State)))))
    (orderedObservations : ∀ (start : State) (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)),
        (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
          terminal (path (times count))
          ∂(globalLaws start : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State)))) =
          ContinuousMarkov.kernelBackwardProduct
            (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
            ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start)
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime filtration stoppingTime)
    (aeFinite : ∀ᵐ path ∂measure, stoppingTime path ≠ ⊤)
    (terminal : C(ℝ≥0, State) → ℝ)
    (terminalMeasurable : @Measurable C(ℝ≥0, State) ℝ (borel C(ℝ≥0, State)) (borel ℝ) terminal)
    (bound : ℝ) (terminalBound : ∀ future, ‖terminal future‖ ≤ bound) :
    condExp stopping.measurableSpace measure
        (fun path => terminal (continuousPathRandomShift (fun path => (stoppingTime path).untopA) path)) =ᵐ[measure]
      (fun path => ∫ future, terminal future
        ∂(globalLaws (path (stoppingTime path).untopA) : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State)))) := by
  have restrictionEquality : measure.restrict {path | stoppingTime path ≠ ⊤} = measure :=
    Measure.restrict_eq_self_of_ae_mem aeFinite
  simpa only [restrictionEquality] using
    continuousPath_extended_stoppingTime_boundedBorel_future_condExp_markov
      measure filtration naturalBelow semigroup positive preservesOne deterministicMarkov globalLaws familyMeasurable
      orderedObservations stoppingTime stopping terminal terminalMeasurable bound terminalBound

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_extended_stoppingTime_boundedBorel_future_condExp_markov
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_aeFinite_stoppingTime_boundedBorel_future_condExp_markov
