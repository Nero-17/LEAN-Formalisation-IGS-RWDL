import RequestProject.Section31.ContinuousPathMarkovPastEvents
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The continuous-test deterministic Markov event identity also holds in
the right-continuation of the canonical natural filtration. This follows
by approaching the deterministic observation time from above and dominated
convergence along continuous paths. No right-continuous Markov identity is
an assumption. Completion and stopping-time conclusions remain separate. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 6000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance continuousRightContinuousMarkovMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance continuousRightContinuousMarkovBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def canonicalRightContinuousPathFiltration : Filtration ℝ≥0 (borel C(ℝ≥0, State)) :=
  (canonicalContinuousPathFiltration (State := State)).rightCont

theorem canonicalRightContinuousPast_measurable_later
    (time later : ℝ≥0) (strictlyLater : time < later) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[canonicalRightContinuousPathFiltration (State := State) time] event) :
    MeasurableSet[canonicalContinuousPathFiltration (State := State) later] event := by
  have filtrationBound : canonicalRightContinuousPathFiltration (State := State) time ≤
      canonicalContinuousPathFiltration (State := State) later := by
    change (canonicalContinuousPathFiltration (State := State)).rightCont time ≤ _
    rw [Filtration.rightCont_eq]
    exact iInf_le_of_le later (iInf_le_of_le strictlyLater le_rfl)
  exact filtrationBound _ eventMeasurable

theorem continuousPath_rightContinuous_setIntegral_markov
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[canonicalRightContinuousPathFiltration (State := State) time] event) :
    (∫ path in event, terminal (path (time + delay)) ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path in event, semigroup delay terminal (path time) ∂(law : Measure C(ℝ≥0, State)) := by
  have shiftedTimeTendsto : Tendsto (fun level : ℕ => time + ((2 : ℝ≥0)⁻¹) ^ level) atTop (𝓝 time) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0)⁻¹) (by norm_num))
  have approximationIdentity (level : ℕ) :
      (∫ path in event, terminal (path (time + ((2 : ℝ≥0)⁻¹) ^ level + delay))
        ∂(law : Measure C(ℝ≥0, State))) =
        ∫ path in event, semigroup delay terminal (path (time + ((2 : ℝ≥0)⁻¹) ^ level))
          ∂(law : Measure C(ℝ≥0, State)) :=
    continuousPath_natural_setIntegral_markov law semigroup start positive observations
      (time + ((2 : ℝ≥0)⁻¹) ^ level) delay terminal event
      (canonicalRightContinuousPast_measurable_later time (time + ((2 : ℝ≥0)⁻¹) ^ level)
        (lt_add_of_pos_right time (pow_pos (by norm_num : (0 : ℝ≥0) < (2 : ℝ≥0)⁻¹) level))
        event eventMeasurable)
  have futureLimit :
      Tendsto (fun level : ℕ => ∫ path in event,
        terminal (path (time + ((2 : ℝ≥0)⁻¹) ^ level + delay))
          ∂(law : Measure C(ℝ≥0, State))) atTop
        (𝓝 (∫ path in event, terminal (path (time + delay)) ∂(law : Measure C(ℝ≥0, State)))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖terminal‖)
      (fun level => (canonical_eval_continuousTest_integrable law
        (time + ((2 : ℝ≥0)⁻¹) ^ level + delay) terminal).integrableOn.1) (integrable_const _)
    · intro level
      exact Eventually.of_forall fun path => terminal.norm_coe_le_norm _
    · exact Eventually.of_forall fun path =>
        (terminal.continuous.comp path.continuous).continuousAt.tendsto.comp
          (shiftedTimeTendsto.add_const delay)
  have currentLimit :
      Tendsto (fun level : ℕ => ∫ path in event,
        semigroup delay terminal (path (time + ((2 : ℝ≥0)⁻¹) ^ level))
          ∂(law : Measure C(ℝ≥0, State))) atTop
        (𝓝 (∫ path in event, semigroup delay terminal (path time) ∂(law : Measure C(ℝ≥0, State)))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖semigroup delay terminal‖)
      (fun level => (canonical_eval_continuousTest_integrable law
        (time + ((2 : ℝ≥0)⁻¹) ^ level) (semigroup delay terminal)).integrableOn.1) (integrable_const _)
    · intro level
      exact Eventually.of_forall fun path => (semigroup delay terminal).norm_coe_le_norm _
    · exact Eventually.of_forall fun path =>
        ((semigroup delay terminal).continuous.comp path.continuous).continuousAt.tendsto.comp shiftedTimeTendsto
  exact tendsto_nhds_unique futureLimit (currentLimit.congr fun level => (approximationIdentity level).symm)

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.canonicalRightContinuousPast_measurable_later
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_rightContinuous_setIntegral_markov
