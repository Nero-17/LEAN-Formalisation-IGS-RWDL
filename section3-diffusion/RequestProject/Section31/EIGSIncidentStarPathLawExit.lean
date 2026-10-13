import RequestProject.Section31.EIGSIncidentStarTrajectoryExit
import RequestProject.Section31.FiniteGraphSurvivalPathLaw

/-! The actual graph Ionescu--Tulcea path law starts at its Dirac point and
uses adjacent steps almost surely. Consequently star first-exit events and
next-distinct-coarse-hit events have the same actual probability. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped Classical ProbabilityTheory
open IGS.Sec31.DiscreteMarkov
noncomputable section

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]

theorem finitePrefixPredicate_measurable (time : ℕ) (predicate : (Finset.Iic time → Vertex) → Prop) :
    MeasurableSet {path : ℕ → Vertex | predicate (frestrictLe time path)} :=
  (Set.to_countable {history | predicate history}).measurableSet.preimage (measurable_frestrictLe time)

theorem finiteGraphTransitionKernel_ae_adjacent (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (degree : ∀ vertex, 0 < graph.degree vertex) (vertex : Vertex) :
    ∀ᵐ other ∂finiteGraphTransitionKernel graph degree vertex, graph.Adj vertex other := by
  rw [ae_iff]
  change (rwStep (degree vertex)).toMeasure {other | ¬ graph.Adj vertex other} = 0
  apply ((rwStep (degree vertex)).toMeasure_apply_eq_zero_iff
    (Set.to_countable _).measurableSet).mpr
  apply Set.disjoint_left.mpr
  intro other supported nonadjacent
  change rwStep (degree vertex) other ≠ 0 at supported
  change ¬ graph.Adj vertex other at nonadjacent
  exact supported (by simp [rwStep_apply, transProb, nonadjacent])

theorem finiteGraphPathLaw_ae_start (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree : ∀ vertex, 0 < graph.degree vertex) (start : Vertex) :
    ∀ᵐ path ∂pathLaw (finiteGraphTransitionKernel graph degree) (Measure.dirac start),
      path 0 = start := by
  have projected : ∀ᵐ vertex ∂(pathLaw (finiteGraphTransitionKernel graph degree)
      (Measure.dirac start)).map (fun path => path 0), vertex = start := by
    rw [pathLaw_coordinate_zero]
    simp
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable projected

theorem finiteGraphPathLaw_ae_adjacent (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree : ∀ vertex, 0 < graph.degree vertex) (start : Vertex) (index : ℕ) :
    ∀ᵐ path ∂pathLaw (finiteGraphTransitionKernel graph degree) (Measure.dirac start),
      graph.Adj (path index) (path (index + 1)) := by
  have joint : ∀ᵐ pair ∂(pathLaw (finiteGraphTransitionKernel graph degree) (Measure.dirac start)).map
      (fun path => (frestrictLe index path, path (index + 1))),
      graph.Adj (pair.1 ⟨index, Finset.mem_Iic.mpr le_rfl⟩) pair.2 := by
    rw [pathLaw_history_endpoint_joint (finiteGraphTransitionKernel graph degree)
      (Measure.dirac start) index 1, pow_one]
    apply Measure.ae_compProd_of_ae_ae (Set.to_countable _).measurableSet
    apply Eventually.of_forall
    intro history
    change ∀ᵐ other ∂finiteGraphTransitionKernel graph degree
      (history ⟨index, Finset.mem_Iic.mpr le_rfl⟩),
      graph.Adj (history ⟨index, Finset.mem_Iic.mpr le_rfl⟩) other
    exact finiteGraphTransitionKernel_ae_adjacent graph degree _
  exact ae_of_ae_map
    ((measurable_frestrictLe index).prodMk (measurable_pi_apply (index + 1))).aemeasurable joint

variable {K : ℕ}

/-- The actual simple graph walk path law, with a Dirac initial state. -/
def xiGraphWalkPathLaw (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ)
    [MeasurableSpace (XiVtx system level)] [MeasurableSingletonClass (XiVtx system level)]
    (start : XiVtx system level) : Measure (ℕ → XiVtx system level) :=
  pathLaw (finiteGraphTransitionKernel (XiSimpleGraph system level)
    (fun vertex => by exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected level vertex))
    (Measure.dirac start)

theorem xiTrajectoryFirstStarExit_measurable (system : EIGSData K) (coarse steps : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (center : XiVtx system coarse) (time : ℕ) :
    MeasurableSet {path | xiTrajectoryFirstStarExit system coarse steps center path time} := by
  have event_eq : {path | xiTrajectoryFirstStarExit system coarse steps center path time} =
      {path : ℕ → XiVtx system (coarse + steps) | (frestrictLe time path) ⟨time, Finset.mem_Iic.mpr le_rfl⟩ ∉
          xiIncidentStarDomain system coarse steps center ∧
        ∀ index : Finset.Iic time, index.val < time →
          (frestrictLe time path) index ∈ xiIncidentStarDomain system coarse steps center} := by
    ext path
    constructor
    · rintro ⟨outside, earlier⟩
      exact ⟨outside, fun index before => earlier index.val before⟩
    · rintro ⟨outside, earlier⟩
      exact ⟨outside, fun index before => earlier ⟨index, Finset.mem_Iic.mpr before.le⟩ before⟩
  rw [event_eq]
  exact finitePrefixPredicate_measurable time (fun history : Finset.Iic time → XiVtx system (coarse + steps) =>
    history ⟨time, Finset.mem_Iic.mpr le_rfl⟩ ∉ xiIncidentStarDomain system coarse steps center ∧
      ∀ index : Finset.Iic time, index.val < time →
        history index ∈ xiIncidentStarDomain system coarse steps center)

theorem xiTrajectoryFirstDistinctCoarseHit_measurable (system : EIGSData K) (coarse steps : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (center : XiVtx system coarse) (time : ℕ) :
    MeasurableSet {path | xiTrajectoryFirstDistinctCoarseHit system coarse steps center path time} := by
  have event_eq : {path | xiTrajectoryFirstDistinctCoarseHit system coarse steps center path time} =
      {path | (∃ other : XiVtx system coarse, other ≠ center ∧
          (frestrictLe time path) ⟨time, Finset.mem_Iic.mpr le_rfl⟩ = xiForward system coarse steps other) ∧
        ∀ index : Finset.Iic time, index.val < time → ∀ other : XiVtx system coarse, other ≠ center →
          (frestrictLe time path) index ≠ xiForward system coarse steps other} := by
    ext path
    constructor
    · rintro ⟨at_hit, earlier⟩
      exact ⟨at_hit, fun index before => earlier index.val before⟩
    · rintro ⟨at_hit, earlier⟩
      exact ⟨at_hit, fun index before => earlier ⟨index, Finset.mem_Iic.mpr before.le⟩ before⟩
  rw [event_eq]
  exact finitePrefixPredicate_measurable time (fun history =>
    (∃ other : XiVtx system coarse, other ≠ center ∧
      history ⟨time, Finset.mem_Iic.mpr le_rfl⟩ = xiForward system coarse steps other) ∧
      ∀ index : Finset.Iic time, index.val < time → ∀ other : XiVtx system coarse, other ≠ center →
        history index ≠ xiForward system coarse steps other)

theorem xiGraphWalkPathLaw_ae_star_exit_iff_distinct_hit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (center : XiVtx system coarse) (time : ℕ) :
    ∀ᵐ path ∂xiGraphWalkPathLaw system rulesConnected (coarse + steps) (xiForward system coarse steps center),
      xiTrajectoryFirstStarExit system coarse steps center path time ↔
        xiTrajectoryFirstDistinctCoarseHit system coarse steps center path time := by
  have starts := finiteGraphPathLaw_ae_start (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex)
    (xiForward system coarse steps center)
  have adjacent := ae_all_iff.mpr (fun index => finiteGraphPathLaw_ae_adjacent
    (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex)
    (xiForward system coarse steps center) index)
  filter_upwards [starts, adjacent] with path start support
  exact xiIncidentStarDomain_first_exit_iff_first_distinct_hit system coarse steps center path time
    start (fun index _ => support index)

/-- The equality concerns the genuine IFT law; the initial state and
adjacency support have been proved internally almost surely. -/
theorem xiGraphWalkPathLaw_star_exit_probability_eq_distinct_hit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (center : XiVtx system coarse) (time : ℕ) :
    xiGraphWalkPathLaw system rulesConnected (coarse + steps) (xiForward system coarse steps center)
        {path | xiTrajectoryFirstStarExit system coarse steps center path time} =
      xiGraphWalkPathLaw system rulesConnected (coarse + steps) (xiForward system coarse steps center)
        {path | xiTrajectoryFirstDistinctCoarseHit system coarse steps center path time} := by
  apply measure_congr
  filter_upwards [xiGraphWalkPathLaw_ae_star_exit_iff_distinct_hit system rulesConnected coarse steps center time]
    with path equivalent
  exact propext equivalent

end
end EIGS

#print axioms EIGS.finiteGraphTransitionKernel_ae_adjacent
#print axioms EIGS.xiTrajectoryFirstStarExit_measurable
#print axioms EIGS.xiTrajectoryFirstDistinctCoarseHit_measurable
#print axioms EIGS.finiteGraphPathLaw_ae_start
#print axioms EIGS.finiteGraphPathLaw_ae_adjacent
#print axioms EIGS.xiGraphWalkPathLaw_ae_star_exit_iff_distinct_hit
#print axioms EIGS.xiGraphWalkPathLaw_star_exit_probability_eq_distinct_hit
