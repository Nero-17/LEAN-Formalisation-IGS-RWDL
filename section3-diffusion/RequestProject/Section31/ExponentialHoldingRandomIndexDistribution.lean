import RequestProject.Section31.ExponentialHoldingPoissonCountLaw
import RequestProject.Section31.FiniteGraphExponentialHoldingProcess

/-! The actual independent exponential clock samples the actual discrete
trajectory with Poisson weights. This proves one-time distributions; it does
not assert independence of clock increments from marginal laws alone. -/

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section

theorem independent_random_index_probability
    {State Clock : Type*} [MeasurableSpace State] [MeasurableSpace Clock]
    (trajectoryLaw : Measure (ℕ → State)) [SFinite trajectoryLaw]
    (clockLaw : Measure Clock) [SFinite clockLaw]
    (index : Clock → ℕ) (indexMeasurable : Measurable index)
    (event : Set State) (eventMeasurable : MeasurableSet event) :
    (trajectoryLaw.prod clockLaw) {sample | sample.1 (index sample.2) ∈ event} =
      ∑' count : ℕ, trajectoryLaw {trajectory | trajectory count ∈ event} *
        clockLaw {clock | index clock = count} := by
  have eventEquality :
      {sample : (ℕ → State) × Clock | sample.1 (index sample.2) ∈ event} =
        ⋃ count : ℕ, {trajectory : ℕ → State | trajectory count ∈ event} ×ˢ
          {clock : Clock | index clock = count} := by
    ext sample
    simp only [mem_setOf_eq, mem_iUnion, mem_prod]
    constructor
    · intro membership
      exact ⟨index sample.2, membership, rfl⟩
    · rintro ⟨count, membership, equality⟩
      simpa only [equality] using membership
  have disjoint : Pairwise (fun first second : ℕ => Disjoint
      ({trajectory : ℕ → State | trajectory first ∈ event} ×ˢ
        {clock : Clock | index clock = first})
      ({trajectory : ℕ → State | trajectory second ∈ event} ×ˢ
        {clock : Clock | index clock = second})) := by
    intro first second distinct
    apply Set.disjoint_left.mpr
    intro sample firstMembership secondMembership
    exact distinct (firstMembership.2.symm.trans secondMembership.2)
  have measurable (count : ℕ) : MeasurableSet
      ({trajectory : ℕ → State | trajectory count ∈ event} ×ˢ
        {clock : Clock | index clock = count}) :=
    (eventMeasurable.preimage (measurable_pi_apply count)).prod
      ((measurableSet_singleton count).preimage indexMeasurable)
  rw [eventEquality, measure_iUnion disjoint measurable]
  simp only [Measure.prod_prod]

theorem exponential_holding_path_poisson_mixture
    {State : Type*} [MeasurableSpace State]
    (trajectoryLaw : Measure (ℕ → State)) [SFinite trajectoryLaw]
    (time : ℝ≥0) (event : Set State) (eventMeasurable : MeasurableSet event) :
    (trajectoryLaw.prod exponentialHoldingTimeLaw)
        {sample | holdingTimePath sample.1 sample.2 (time : ℝ) ∈ event} =
      ∑' count : ℕ, trajectoryLaw {trajectory | trajectory count ∈ event} *
        ENNReal.ofReal (poissonPMFReal time count) := by
  change (trajectoryLaw.prod exponentialHoldingTimeLaw)
      {sample | sample.1 (holdingJumpIndex sample.2 (time : ℝ)) ∈ event} = _
  rw [independent_random_index_probability trajectoryLaw exponentialHoldingTimeLaw
    (fun holdingTimes => holdingJumpIndex holdingTimes (time : ℝ))
    (holdingJumpIndex_measurable (time : ℝ)) event eventMeasurable]
  simp_rw [exponentialHoldingJumpIndex_poisson_probability]

theorem finite_graph_exponential_path_marginal_mixture
    {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex)
    (initial : ProbabilityMeasure Vertex) (rate time : ℝ≥0)
    (event : Set Vertex) (eventMeasurable : MeasurableSet event) :
    finiteGraphExponentialSampleLaw graph degreePositive initial
        {sample | finiteGraphExponentialEmbeddedPath id rate sample time ∈ event} =
      ∑' count : ℕ,
        ((EIGS.finiteGraphTransitionKernel graph degreePositive ^ count) ∘ₘ
          (initial : Measure Vertex)) event *
            ENNReal.ofReal (poissonPMFReal (rate * time) count) := by
  change ((DiscreteMarkov.pathLaw
    (EIGS.finiteGraphTransitionKernel graph degreePositive)
    (initial : Measure Vertex)).prod exponentialHoldingTimeLaw)
      {sample | holdingTimePath sample.1 sample.2 ((rate * time : ℝ≥0) : ℝ) ∈ event} = _
  rw [exponential_holding_path_poisson_mixture _ (rate * time) event eventMeasurable]
  apply tsum_congr
  intro count
  congr 1
  rw [← DiscreteMarkov.pathLaw_coordinate_iterates]
  rw [Measure.map_apply (measurable_pi_apply count) eventMeasurable]
  rfl

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.independent_random_index_probability
#print axioms IGS.Sec31.PoissonClock.exponential_holding_path_poisson_mixture
#print axioms IGS.Sec31.PoissonClock.finite_graph_exponential_path_marginal_mixture
