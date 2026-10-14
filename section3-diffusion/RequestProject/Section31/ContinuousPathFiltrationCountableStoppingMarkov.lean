import RequestProject.Section31.ContinuousPathCountableStoppingMarkov

/-! Countable finite-valued stopping identities for a general filtration
and any finite measure on a sigma algebra containing the compact-open Borel
sets. The deterministic-time event identity is the only Markov input; the
stopping identity is proved by disjoint level events. This version can be
instantiated on a completed ambient measurable space. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators Function
noncomputable section
set_option maxHeartbeats 6000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable [ambient : MeasurableSpace C(ℝ≥0, State)] [OpensMeasurableSpace C(ℝ≥0, State)]

theorem canonical_filtration_stopping_future_continuousTest_integrable
    (measure : Measure C(ℝ≥0, State)) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 ambient)
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime filtration stoppingTime)
    (delay : ℝ≥0) (terminal : C(State, ℝ)) :
    Integrable (fun path : C(ℝ≥0, State) => terminal (path ((stoppingTime path).untopA + delay))) measure := by
  have evaluationMeasurable : Measurable (fun path : C(ℝ≥0, State) =>
      path ((stoppingTime path).untopA + delay)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk (stopping.measurable'.untopA.add_const delay))
  exact Integrable.of_bound (terminal.continuous.measurable.comp evaluationMeasurable).aestronglyMeasurable
    ‖terminal‖ (Eventually.of_forall fun path => terminal.norm_coe_le_norm _)

theorem continuousPath_filtration_countable_stopping_setIntegral_markov
    (measure : Measure C(ℝ≥0, State)) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 ambient)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (deterministicMarkov : ∀ (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State)),
      MeasurableSet[filtration time] event →
      (∫ path in event, terminal (path (time + delay)) ∂measure) =
        ∫ path in event, semigroup delay terminal (path time) ∂measure)
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime filtration stoppingTime)
    (realValues : Set ℝ≥0) (valuesCountable : realValues.Countable)
    (finiteValues : ∀ path, stoppingTime path ∈ WithTop.some '' realValues)
    (delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    (∫ path in event, terminal (path ((stoppingTime path).untopA + delay)) ∂measure) =
      ∫ path in event, semigroup delay terminal (path ((stoppingTime path).untopA)) ∂measure := by
  letI filtrationCountableStoppingValuesCountable : Countable realValues := valuesCountable.to_subtype
  have eventGlobalMeasurable : MeasurableSet event := stopping.measurableSpace_le _ eventMeasurable
  have levelGlobalMeasurable (time : ℝ≥0) : MeasurableSet {path | stoppingTime path = time} :=
    stopping.measurableSpace_le _ (stopping.measurableSet_eq' time)
  have partitionMeasurable (time : realValues) :
      MeasurableSet (event ∩ {path | stoppingTime path = time.val}) :=
    eventGlobalMeasurable.inter (levelGlobalMeasurable time.val)
  have partitionDisjoint : Pairwise (Disjoint on (fun time : realValues =>
      event ∩ {path | stoppingTime path = time.val})) := by
    intro first second different
    apply Set.disjoint_left.mpr
    intro path firstMembership secondMembership
    apply different
    apply Subtype.ext
    exact WithTop.coe_injective (firstMembership.2.symm.trans secondMembership.2)
  have partitionEquality : event = ⋃ time : realValues, event ∩ {path | stoppingTime path = time.val} := by
    ext path
    constructor
    · intro membership
      obtain ⟨time, timeMembership, timeEquality⟩ := finiteValues path
      exact Set.mem_iUnion.mpr ⟨⟨time, timeMembership⟩, membership, timeEquality.symm⟩
    · intro membership
      obtain ⟨time, membership⟩ := Set.mem_iUnion.mp membership
      exact membership.1
  have futureIntegrable := canonical_filtration_stopping_future_continuousTest_integrable
    measure filtration stoppingTime stopping delay terminal
  have currentIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      semigroup delay terminal (path ((stoppingTime path).untopA))) measure := by
    simpa only [add_zero] using canonical_filtration_stopping_future_continuousTest_integrable
      measure filtration stoppingTime stopping 0 (semigroup delay terminal)
  rw [partitionEquality, integral_iUnion partitionMeasurable partitionDisjoint futureIntegrable.integrableOn,
    integral_iUnion partitionMeasurable partitionDisjoint currentIntegrable.integrableOn]
  apply tsum_congr
  intro time
  calc
    _ = ∫ path in event ∩ {path | stoppingTime path = time.val}, terminal (path (time.val + delay)) ∂measure := by
      apply setIntegral_congr_fun (partitionMeasurable time)
      intro path membership
      have timeEquality : stoppingTime path = (time.val : WithTop ℝ≥0) := membership.2
      dsimp only
      rw [timeEquality] <;> rfl
    _ = ∫ path in event ∩ {path | stoppingTime path = time.val}, semigroup delay terminal (path time.val) ∂measure :=
      deterministicMarkov time.val delay terminal (event ∩ {path | stoppingTime path = time.val})
        ((stopping.measurableSet_inter_eq_iff event time.val).mp
          (eventMeasurable.inter (stopping.measurableSet_eq' time.val)))
    _ = _ := by
      apply setIntegral_congr_fun (partitionMeasurable time)
      intro path membership
      have timeEquality : stoppingTime path = (time.val : WithTop ℝ≥0) := membership.2
      dsimp only
      rw [timeEquality] <;> rfl

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.canonical_filtration_stopping_future_continuousTest_integrable
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_filtration_countable_stopping_setIntegral_markov
