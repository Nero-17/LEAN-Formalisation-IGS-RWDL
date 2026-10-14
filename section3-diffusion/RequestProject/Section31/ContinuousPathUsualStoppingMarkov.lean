import RequestProject.Section31.ContinuousPathNullAugmentationMarkov
import RequestProject.Section31.ContinuousPathFiltrationFiniteStoppingTimeMarkov

/-! Derive continuous-test deterministic and everywhere finite stopping-time
Markov identities for the usual augmentation of the canonical natural
filtration under each starting law. The completed measure, global null-set
augmentation, and right-continuation are explicit. Bounded Borel terminal
tests, path-future tests, and a full Hunt assertion remain separate. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open IGS.Sec31.UsualAugmentation
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 7000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance continuousUsualStoppingMarkovMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance continuousUsualStoppingMarkovBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def canonicalUsualContinuousPathFiltration (law : ProbabilityMeasure C(ℝ≥0, State)) :
    Filtration ℝ≥0 (eventuallyMeasurableSpace (borel C(ℝ≥0, State))
      (ae (law : Measure C(ℝ≥0, State)))) :=
  usualAugmentation (law : Measure C(ℝ≥0, State)) canonicalContinuousPathFiltration

theorem canonicalNatural_le_usualPathFiltration
    (law : ProbabilityMeasure C(ℝ≥0, State)) (time : ℝ≥0) :
    canonicalContinuousPathFiltration (State := State) time ≤ canonicalUsualContinuousPathFiltration law time :=
  filtration_le_usualAugmentation (law : Measure C(ℝ≥0, State)) canonicalContinuousPathFiltration time

theorem canonicalUsualPast_measurable_augmented_later
    (law : ProbabilityMeasure C(ℝ≥0, State)) (time later : ℝ≥0) (strictlyLater : time < later)
    (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[canonicalUsualContinuousPathFiltration law time] event) :
    MeasurableSet[nullAugmentation (law : Measure C(ℝ≥0, State)) canonicalContinuousPathFiltration later] event := by
  have filtrationBound : canonicalUsualContinuousPathFiltration law time ≤
      nullAugmentation (law : Measure C(ℝ≥0, State)) canonicalContinuousPathFiltration later := by
    change (nullAugmentation (law : Measure C(ℝ≥0, State)) canonicalContinuousPathFiltration).rightCont time ≤ _
    rw [Filtration.rightCont_eq]
    exact iInf_le_of_le later (iInf_le_of_le strictlyLater le_rfl)
  exact filtrationBound _ eventMeasurable

theorem canonical_completion_eval_continuousTest_integrable
    (law : ProbabilityMeasure C(ℝ≥0, State)) (time : ℝ≥0) (terminal : C(State, ℝ)) :
    Integrable (fun path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) =>
      terminal (ContinuousMap.toFun path time)) (law : Measure C(ℝ≥0, State)).completion := by
  letI usualEvalCompletionFiniteMeasure : IsFiniteMeasure (law : Measure C(ℝ≥0, State)).completion :=
    ⟨measure_lt_top (law : Measure C(ℝ≥0, State)) Set.univ⟩
  have completedMeasurable : @Measurable C(ℝ≥0, State) ℝ
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (law : Measure C(ℝ≥0, State))))
      (borel ℝ) (fun path => terminal (ContinuousMap.toFun path time)) :=
    (terminal.continuous.comp (continuous_eval_const time)).measurable.mono
      (le_eventuallyMeasurableSpace (m := borel C(ℝ≥0, State))
        (l := ae (law : Measure C(ℝ≥0, State)))) le_rfl
  exact Integrable.of_bound completedMeasurable.aestronglyMeasurable
    ‖terminal‖ (Eventually.of_forall fun path => terminal.norm_coe_le_norm (ContinuousMap.toFun path time))

theorem continuousPath_usual_setIntegral_markov
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[canonicalUsualContinuousPathFiltration law time] event) :
    (∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
      terminal (ContinuousMap.toFun path (time + delay)) ∂(law : Measure C(ℝ≥0, State)).completion) =
      ∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
        semigroup delay terminal (ContinuousMap.toFun path time) ∂(law : Measure C(ℝ≥0, State)).completion := by
  letI usualDeterministicCompletionFiniteMeasure : IsFiniteMeasure (law : Measure C(ℝ≥0, State)).completion :=
    ⟨measure_lt_top (law : Measure C(ℝ≥0, State)) Set.univ⟩
  have shiftedTimeTendsto : Tendsto (fun level : ℕ => time + ((2 : ℝ≥0)⁻¹) ^ level) atTop (𝓝 time) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0)⁻¹) (by norm_num))
  have approximationIdentity (level : ℕ) :
      (∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
        terminal (ContinuousMap.toFun path (time + ((2 : ℝ≥0)⁻¹) ^ level + delay)) ∂(law : Measure C(ℝ≥0, State)).completion) =
        ∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
          semigroup delay terminal (ContinuousMap.toFun path (time + ((2 : ℝ≥0)⁻¹) ^ level))
            ∂(law : Measure C(ℝ≥0, State)).completion :=
    continuousPath_nullAugmentation_setIntegral_markov law semigroup start positive observations
      (time + ((2 : ℝ≥0)⁻¹) ^ level) delay terminal event
      (canonicalUsualPast_measurable_augmented_later law time (time + ((2 : ℝ≥0)⁻¹) ^ level)
        (lt_add_of_pos_right time (pow_pos (by norm_num : (0 : ℝ≥0) < (2 : ℝ≥0)⁻¹) level)) event eventMeasurable)
  have futureLimit :
      Tendsto (fun level : ℕ => ∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
        terminal (ContinuousMap.toFun path (time + ((2 : ℝ≥0)⁻¹) ^ level + delay)) ∂(law : Measure C(ℝ≥0, State)).completion) atTop
        (𝓝 (∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
          terminal (ContinuousMap.toFun path (time + delay)) ∂(law : Measure C(ℝ≥0, State)).completion)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖terminal‖)
      (fun level => (canonical_completion_eval_continuousTest_integrable law
        (time + ((2 : ℝ≥0)⁻¹) ^ level + delay) terminal).integrableOn.1) (integrable_const _)
    · intro level
      exact Eventually.of_forall fun path => terminal.norm_coe_le_norm _
    · exact Eventually.of_forall fun path =>
        (terminal.continuous.comp (ContinuousMap.continuous_toFun path)).continuousAt.tendsto.comp (shiftedTimeTendsto.add_const delay)
  have currentLimit :
      Tendsto (fun level : ℕ => ∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
        semigroup delay terminal (ContinuousMap.toFun path (time + ((2 : ℝ≥0)⁻¹) ^ level))
          ∂(law : Measure C(ℝ≥0, State)).completion) atTop
        (𝓝 (∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
          semigroup delay terminal (ContinuousMap.toFun path time) ∂(law : Measure C(ℝ≥0, State)).completion)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖semigroup delay terminal‖)
      (fun level => (canonical_completion_eval_continuousTest_integrable law
        (time + ((2 : ℝ≥0)⁻¹) ^ level) (semigroup delay terminal)).integrableOn.1) (integrable_const _)
    · intro level
      exact Eventually.of_forall fun path => (semigroup delay terminal).norm_coe_le_norm _
    · exact Eventually.of_forall fun path =>
        ((semigroup delay terminal).continuous.comp (ContinuousMap.continuous_toFun path)).continuousAt.tendsto.comp shiftedTimeTendsto
  exact tendsto_nhds_unique futureLimit (currentLimit.congr fun level => (approximationIdentity level).symm)

theorem continuousPath_usual_finite_stoppingTime_setIntegral_markov
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime (canonicalUsualContinuousPathFiltration law)
      (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    (∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
      terminal (ContinuousMap.toFun path (stoppingTime path + delay)) ∂(law : Measure C(ℝ≥0, State)).completion) =
      ∫ path : NullMeasurableSpace C(ℝ≥0, State) (law : Measure C(ℝ≥0, State)) in event,
        semigroup delay terminal (ContinuousMap.toFun path (stoppingTime path)) ∂(law : Measure C(ℝ≥0, State)).completion := by
  letI usualStoppingCompletionFiniteMeasure : IsFiniteMeasure (law : Measure C(ℝ≥0, State)).completion :=
    ⟨measure_lt_top (law : Measure C(ℝ≥0, State)) Set.univ⟩
  letI usualStoppingCompletionOpensMeasurableSpace : @OpensMeasurableSpace C(ℝ≥0, State) inferInstance
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (law : Measure C(ℝ≥0, State)))) :=
    @OpensMeasurableSpace.mk C(ℝ≥0, State) inferInstance
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (law : Measure C(ℝ≥0, State))))
      (le_eventuallyMeasurableSpace (m := borel C(ℝ≥0, State)) (l := ae (law : Measure C(ℝ≥0, State))))
  exact continuousPath_filtration_finite_stoppingTime_setIntegral_markov
    (ambient := eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (law : Measure C(ℝ≥0, State))))
    (law : Measure C(ℝ≥0, State)).completion (canonicalUsualContinuousPathFiltration law) semigroup
    (continuousPath_usual_setIntegral_markov law semigroup start positive observations)
    stoppingTime stopping delay terminal event eventMeasurable

theorem continuousPath_usual_finite_stoppingTime_condExp_markov
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime (canonicalUsualContinuousPathFiltration law)
      (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (delay : ℝ≥0) (terminal : C(State, ℝ)) :
    MeasureTheory.condExp stopping.measurableSpace (law : Measure C(ℝ≥0, State)).completion
        (fun path => terminal (ContinuousMap.toFun path (stoppingTime path + delay))) =ᵐ[(law : Measure C(ℝ≥0, State)).completion]
      (fun path => semigroup delay terminal (ContinuousMap.toFun path (stoppingTime path))) := by
  letI usualCondExpCompletionFiniteMeasure : IsFiniteMeasure (law : Measure C(ℝ≥0, State)).completion :=
    ⟨measure_lt_top (law : Measure C(ℝ≥0, State)) Set.univ⟩
  letI usualCondExpCompletionOpensMeasurableSpace : @OpensMeasurableSpace C(ℝ≥0, State) inferInstance
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (law : Measure C(ℝ≥0, State)))) :=
    @OpensMeasurableSpace.mk C(ℝ≥0, State) inferInstance
      (eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (law : Measure C(ℝ≥0, State))))
      (le_eventuallyMeasurableSpace (m := borel C(ℝ≥0, State)) (l := ae (law : Measure C(ℝ≥0, State))))
  exact continuousPath_filtration_finite_stoppingTime_condExp_markov
    (ambient := eventuallyMeasurableSpace (borel C(ℝ≥0, State)) (ae (law : Measure C(ℝ≥0, State))))
    (law : Measure C(ℝ≥0, State)).completion (canonicalUsualContinuousPathFiltration law)
    (canonicalNatural_le_usualPathFiltration law) semigroup
    (continuousPath_usual_setIntegral_markov law semigroup start positive observations)
    stoppingTime stopping delay terminal

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.canonicalNatural_le_usualPathFiltration
#print axioms IGS.Sec31.DiscreteMarkov.canonicalUsualPast_measurable_augmented_later
#print axioms IGS.Sec31.DiscreteMarkov.canonical_completion_eval_continuousTest_integrable
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_usual_setIntegral_markov
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_usual_finite_stoppingTime_setIntegral_markov
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_usual_finite_stoppingTime_condExp_markov
