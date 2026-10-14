import RequestProject.Section31.ContinuousPathFiniteStoppingMarkov

/-! Countably many finite real stopping-time values suffice for the natural
filtration event-integral Markov identity. Integrability is obtained from
the bounded continuous terminal test, rather than from an assumed stopping
identity. Every stopping time in the identity is explicitly finite-valued
in the sense that it takes values in a countable subset of real times. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators Function
noncomputable section
set_option maxHeartbeats 6000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance continuousCountableStoppingMarkovMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance continuousCountableStoppingMarkovBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem canonical_stopping_future_continuousTest_integrable
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime canonicalContinuousPathFiltration stoppingTime)
    (delay : ℝ≥0) (terminal : C(State, ℝ)) :
    Integrable (fun path : C(ℝ≥0, State) => terminal (path ((stoppingTime path).untopA + delay)))
      (law : Measure C(ℝ≥0, State)) := by
  have evaluationMeasurable : Measurable (fun path : C(ℝ≥0, State) =>
      path ((stoppingTime path).untopA + delay)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk (stopping.measurable'.untopA.add_const delay))
  exact Integrable.of_bound (terminal.continuous.measurable.comp evaluationMeasurable).aestronglyMeasurable
    ‖terminal‖ (Eventually.of_forall fun path => terminal.norm_coe_le_norm _)

theorem continuousPath_countable_stopping_setIntegral_markov
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime canonicalContinuousPathFiltration stoppingTime)
    (realValues : Set ℝ≥0) (valuesCountable : realValues.Countable)
    (finiteValues : ∀ path, stoppingTime path ∈ WithTop.some '' realValues)
    (delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    (∫ path in event, terminal (path ((stoppingTime path).untopA + delay))
      ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path in event, semigroup delay terminal (path ((stoppingTime path).untopA))
        ∂(law : Measure C(ℝ≥0, State)) := by
  letI : Countable realValues := valuesCountable.to_subtype
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
  have futureIntegrable := canonical_stopping_future_continuousTest_integrable law stoppingTime stopping delay terminal
  have currentIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      semigroup delay terminal (path ((stoppingTime path).untopA))) (law : Measure C(ℝ≥0, State)) := by
    simpa only [add_zero] using
      canonical_stopping_future_continuousTest_integrable law stoppingTime stopping 0 (semigroup delay terminal)
  rw [partitionEquality, integral_iUnion partitionMeasurable partitionDisjoint futureIntegrable.integrableOn,
    integral_iUnion partitionMeasurable partitionDisjoint currentIntegrable.integrableOn]
  apply tsum_congr
  intro time
  calc
    _ = ∫ path in event ∩ {path | stoppingTime path = time.val}, terminal (path (time.val + delay))
        ∂(law : Measure C(ℝ≥0, State)) := by
      apply setIntegral_congr_fun (partitionMeasurable time)
      intro path membership
      have timeEquality : stoppingTime path = (time.val : WithTop ℝ≥0) := membership.2
      dsimp only
      rw [timeEquality] <;> rfl
    _ = ∫ path in event ∩ {path | stoppingTime path = time.val}, semigroup delay terminal (path time.val)
        ∂(law : Measure C(ℝ≥0, State)) :=
      continuousPath_natural_setIntegral_markov law semigroup start positive observations time.val delay terminal
        (event ∩ {path | stoppingTime path = time.val})
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

#print axioms IGS.Sec31.DiscreteMarkov.canonical_stopping_future_continuousTest_integrable
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_countable_stopping_setIntegral_markov
