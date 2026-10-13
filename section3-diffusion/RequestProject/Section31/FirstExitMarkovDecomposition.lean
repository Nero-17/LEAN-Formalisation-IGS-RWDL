import RequestProject.Section31.FiniteGraphExitDuration
import RequestProject.Section31.EIGSDiscreteFiniteObservations

/-! Actual first-exit Markov decomposition under the Ionescu--Tulcea law.
The exit event is a finite-history event, so the proved whole-history/future
endpoint joint law applies before summing over the possible exit times.
This does not assume a strong Markov property or path-law tightness. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter Topology
open scoped BigOperators ProbabilityTheory Classical

noncomputable section
set_option maxHeartbeats 4000000

variable {X : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]

def firstExitHistory (domain : Finset X) (time : ℕ) : Set (Finset.Iic time → X) :=
  {history | (∀ index : Fin time,
    history ⟨index.val, Finset.mem_Iic.mpr (Nat.le_of_lt index.isLt)⟩ ∈ domain) ∧
      history ⟨time, Finset.mem_Iic.mpr le_rfl⟩ ∉ domain}

def firstExitAt (domain : Finset X) (time : ℕ) : Set (ℕ → X) :=
  (frestrictLe time) ⁻¹' firstExitHistory domain time

theorem firstExitAt_measurable (domain : Finset X) (time : ℕ) :
    MeasurableSet (firstExitAt domain time) :=
  (Set.to_countable _).measurableSet.preimage (measurable_frestrictLe time)

theorem mem_firstExitAt (domain : Finset X) (time : ℕ) (path : ℕ → X) :
    path ∈ firstExitAt domain time ↔
      (∀ index < time, path index ∈ domain) ∧ path time ∉ domain := by
  constructor
  · rintro ⟨before, outside⟩
    exact ⟨fun index bounded => before ⟨index, bounded⟩, outside⟩
  · rintro ⟨before, outside⟩
    exact ⟨fun index => before index.val index.isLt, outside⟩

theorem firstExitAt_disjoint (domain : Finset X) {first second : ℕ} (different : first ≠ second) :
    Disjoint (firstExitAt domain first) (firstExitAt domain second) := by
  apply Set.disjoint_left.mpr
  intro path firstExit secondExit
  rw [mem_firstExitAt] at firstExit secondExit
  rcases lt_or_gt_of_ne different with ordered | ordered
  · exact firstExit.2 (secondExit.1 first ordered)
  · exact secondExit.2 (firstExit.1 second ordered)

theorem exits_by_iff (domain : Finset X) (horizon : ℕ) (path : ℕ → X) :
    path ∉ EIGS.graphSurvivalEvent domain horizon ↔
      ∃ time ≤ horizon, path ∈ firstExitAt domain time := by
  constructor
  · intro doesNotSurvive
    have exits : ∃ time ≤ horizon, path time ∉ domain := by
      simpa only [EIGS.graphSurvivalEvent, Set.mem_setOf_eq, not_forall, exists_prop] using doesNotSurvive
    obtain ⟨witness, bounded, outside⟩ := exits
    have eventuallyOutside : ∃ time, path time ∉ domain := ⟨witness, outside⟩
    refine ⟨Nat.find eventuallyOutside, (Nat.find_min' eventuallyOutside outside).trans bounded, ?_⟩
    rw [mem_firstExitAt]
    exact ⟨fun index before => by simpa using Nat.find_min eventuallyOutside before,
      Nat.find_spec eventuallyOutside⟩
  · rintro ⟨time, bounded, firstExit⟩ survives
    exact ((mem_firstExitAt domain time path).mp firstExit).2 (survives time bounded)

/-- This is the actual finite-history Markov identity on a first-exit event. -/
theorem firstExitAt_integral_future (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (domain : Finset X) (time offset : ℕ) (function : X → ℝ) :
    (∫ path, (firstExitAt domain time).indicator
      (fun path => function (path (time + offset))) path
      ∂pathLaw kernel (initial : Measure X)) =
    ∫ path, (firstExitAt domain time).indicator
      (fun path => ∫ target, function target ∂(kernel ^ offset) (path time)) path
      ∂pathLaw kernel (initial : Measure X) := by
  let endpoint : Kernel (Finset.Iic time → X) X :=
    (kernel ^ offset).comap (fun history => history ⟨time, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _)
  let jointTest : (Finset.Iic time → X) × X → ℝ :=
    fun pair => (firstExitHistory domain time).indicator (fun _ => function pair.2) pair.1
  have jointMeasurable : Measurable jointTest := measurable_of_countable _
  have jointIntegrable : Integrable jointTest
      ((pathLaw kernel (initial : Measure X)).map (frestrictLe time) ⊗ₘ endpoint) :=
    Integrable.of_finite
  have actualJoint := pathLaw_history_endpoint_joint kernel (initial : Measure X) time offset
  have jointIntegral :
      (∫ path, jointTest (frestrictLe time path, path (time + offset))
        ∂pathLaw kernel (initial : Measure X)) =
      ∫ pair, jointTest pair
        ∂((pathLaw kernel (initial : Measure X)).map (frestrictLe time) ⊗ₘ endpoint) := by
    rw [← actualJoint]
    exact (integral_map ((measurable_frestrictLe time).prodMk (measurable_pi_apply _)).aemeasurable
      jointMeasurable.aestronglyMeasurable).symm
  change (∫ path, jointTest (frestrictLe time path, path (time + offset))
    ∂pathLaw kernel (initial : Measure X)) = _
  rw [jointIntegral, Measure.integral_compProd jointIntegrable,
    integral_map (measurable_frestrictLe time).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro path
  by_cases exits : frestrictLe time path ∈ firstExitHistory domain time
  · simp only [jointTest, Set.indicator_of_mem exits]
    change (∫ target, function target ∂(kernel ^ offset) (path time)) =
      (firstExitAt domain time).indicator
        (fun path => ∫ target, function target ∂(kernel ^ offset) (path time)) path
    rw [Set.indicator_of_mem (show path ∈ firstExitAt domain time from exits)]
  · simp only [jointTest, Set.indicator_of_notMem exits, integral_zero]
    rw [Set.indicator_of_notMem (show path ∉ firstExitAt domain time from exits)]

theorem firstExitAt_integral_final (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (domain : Finset X) (time horizon : ℕ)
    (bounded : time ≤ horizon) (function : X → ℝ) :
    (∫ path, (firstExitAt domain time).indicator (fun path => function (path horizon)) path
      ∂pathLaw kernel (initial : Measure X)) =
    ∫ path, (firstExitAt domain time).indicator
      (fun path => ∫ target, function target ∂(kernel ^ (horizon - time)) (path time)) path
      ∂pathLaw kernel (initial : Measure X) := by
  simpa only [Nat.add_sub_of_le bounded] using
    firstExitAt_integral_future kernel initial domain time (horizon - time) function

theorem firstExit_indicator_sum (domain : Finset X) (horizon : ℕ)
    (function : (ℕ → X) → ℝ) (path : ℕ → X) :
    (∑ time ∈ Finset.range (horizon + 1), (firstExitAt domain time).indicator function path) =
      (EIGS.graphSurvivalEvent domain horizon)ᶜ.indicator function path := by
  by_cases exits : path ∉ EIGS.graphSurvivalEvent domain horizon
  · obtain ⟨time, bounded, firstExit⟩ := (exits_by_iff domain horizon path).mp exits
    rw [Finset.sum_eq_single time]
    · rw [Set.indicator_of_mem firstExit, Set.indicator_of_mem exits]
    · intro other _ different
      apply Set.indicator_of_notMem
      intro otherExit
      exact Set.disjoint_left.mp (firstExitAt_disjoint domain different) otherExit firstExit
    · intro notInRange
      exact False.elim (notInRange (Finset.mem_range.mpr (Nat.lt_succ_of_le bounded)))
  · rw [Set.indicator_of_notMem exits]
    apply Finset.sum_eq_zero
    intro time inRange
    apply Set.indicator_of_notMem
    intro firstExit
    exact exits ((exits_by_iff domain horizon path).mpr
      ⟨time, Nat.le_of_lt_succ (Finset.mem_range.mp inRange), firstExit⟩)

theorem path_coordinate_integrable (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (time : ℕ) (function : X → ℝ) :
    Integrable (fun path : ℕ → X => function (path time)) (pathLaw kernel (initial : Measure X)) := by
  apply Integrable.of_bound
    ((measurable_of_countable function).comp (measurable_pi_apply time)).aestronglyMeasurable
    (∑ vertex : X, ‖function vertex‖)
  apply Eventually.of_forall
  intro path
  exact Finset.single_le_sum (fun vertex _ => norm_nonneg (function vertex)) (Finset.mem_univ (path time))

/-- A genuine bounded first-exit decomposition. The remaining time is
horizon minus the actual exit time, rather than a deterministic substitute. -/
theorem exitBy_integral_final (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (domain : Finset X) (horizon : ℕ) (function : X → ℝ) :
    (∫ path, (EIGS.graphSurvivalEvent domain horizon)ᶜ.indicator
      (fun path => function (path horizon)) path ∂pathLaw kernel (initial : Measure X)) =
      ∑ time ∈ Finset.range (horizon + 1),
        ∫ path, (firstExitAt domain time).indicator
          (fun path => ∫ target, function target ∂(kernel ^ (horizon - time)) (path time)) path
          ∂pathLaw kernel (initial : Measure X) := by
  calc
    _ = ∫ path, ∑ time ∈ Finset.range (horizon + 1),
        (firstExitAt domain time).indicator (fun path => function (path horizon)) path
          ∂pathLaw kernel (initial : Measure X) :=
      integral_congr_ae (Eventually.of_forall (fun path =>
        (firstExit_indicator_sum domain horizon (fun path => function (path horizon)) path).symm))
    _ = ∑ time ∈ Finset.range (horizon + 1),
        ∫ path, (firstExitAt domain time).indicator (fun path => function (path horizon)) path
          ∂pathLaw kernel (initial : Measure X) :=
      integral_finset_sum _ (fun time _ =>
        (path_coordinate_integrable kernel initial horizon function).indicator (firstExitAt_measurable domain time))
    _ = _ := Finset.sum_congr rfl (fun time inRange =>
      firstExitAt_integral_final kernel initial domain time horizon
        (Nat.le_of_lt_succ (Finset.mem_range.mp inRange)) function)

/-- The post-exit persistence condition yields a true maximal exit bound.
Its uniform quantitative verification for native graphs remains a separate
analytic task; it is not replaced by stationary deterministic two-time bounds. -/
theorem exit_probability_le_endpoint_expectation (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (domain : Finset X) (horizon : ℕ)
    (function : X → ℝ) (functionNonnegative : ∀ vertex, 0 ≤ function vertex)
    (persistence : ℝ)
    (persistentAfterExit : ∀ time ≤ horizon, ∀ vertex ∉ domain,
      persistence ≤ ∫ target, function target ∂(kernel ^ (horizon - time)) vertex) :
    persistence * ((pathLaw kernel (initial : Measure X)) (EIGS.graphSurvivalEvent domain horizon)ᶜ).toReal ≤
      ∫ path, function (path horizon) ∂pathLaw kernel (initial : Measure X) := by
  have exitMeasurable := (EIGS.graphSurvivalEvent_measurable domain horizon).compl
  have constantExitIntegral :
      (∫ path, (EIGS.graphSurvivalEvent domain horizon)ᶜ.indicator (fun _ => persistence) path
        ∂pathLaw kernel (initial : Measure X)) =
      persistence * ((pathLaw kernel (initial : Measure X)) (EIGS.graphSurvivalEvent domain horizon)ᶜ).toReal := by
    simpa only [smul_eq_mul, mul_comm, measureReal_def] using
      integral_indicator_const (μ := pathLaw kernel (initial : Measure X)) persistence exitMeasurable
  calc
    _ = ∫ path, (EIGS.graphSurvivalEvent domain horizon)ᶜ.indicator (fun _ => persistence) path
        ∂pathLaw kernel (initial : Measure X) := constantExitIntegral.symm
    _ = ∑ time ∈ Finset.range (horizon + 1),
        ∫ path, (firstExitAt domain time).indicator (fun _ => persistence) path
          ∂pathLaw kernel (initial : Measure X) := by
      rw [← integral_finset_sum _ (fun time _ =>
        (integrable_const persistence).indicator (firstExitAt_measurable domain time))]
      exact integral_congr_ae (Eventually.of_forall (fun path =>
        (firstExit_indicator_sum domain horizon (fun _ => persistence) path).symm))
    _ ≤ ∑ time ∈ Finset.range (horizon + 1),
        ∫ path, (firstExitAt domain time).indicator
          (fun path => ∫ target, function target ∂(kernel ^ (horizon - time)) (path time)) path
          ∂pathLaw kernel (initial : Measure X) := by
      apply Finset.sum_le_sum
      intro time inRange
      apply integral_mono
        ((integrable_const persistence).indicator (firstExitAt_measurable domain time))
        ((path_coordinate_integrable kernel initial time
          (fun vertex => ∫ target, function target ∂(kernel ^ (horizon - time)) vertex)).indicator
            (firstExitAt_measurable domain time))
      intro path
      by_cases exits : path ∈ firstExitAt domain time
      · rw [Set.indicator_of_mem exits, Set.indicator_of_mem exits]
        exact persistentAfterExit time (Nat.le_of_lt_succ (Finset.mem_range.mp inRange))
          (path time) ((mem_firstExitAt domain time path).mp exits).2
      · rw [Set.indicator_of_notMem exits, Set.indicator_of_notMem exits]
    _ = ∫ path, (EIGS.graphSurvivalEvent domain horizon)ᶜ.indicator
        (fun path => function (path horizon)) path ∂pathLaw kernel (initial : Measure X) :=
      (exitBy_integral_final kernel initial domain horizon function).symm
    _ ≤ _ := integral_mono
      ((path_coordinate_integrable kernel initial horizon function).indicator exitMeasurable)
      (path_coordinate_integrable kernel initial horizon function) (fun path => by
        by_cases exits : path ∈ (EIGS.graphSurvivalEvent domain horizon)ᶜ
        · rw [Set.indicator_of_mem exits]
        · rw [Set.indicator_of_notMem exits]
          exact functionNonnegative (path horizon))

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31 Filter Topology
open scoped BigOperators Classical ProbabilityTheory

noncomputable section

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)

/-- The future observation after the actual native first exit is represented
by the actual discrete walk operator, with no Markov-property premise. -/
theorem xiNativeDiscrete_firstExit_integral_future
    (domain : Finset (XiVtx system level)) (time offset : ℕ)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    (∫ path, (DiscreteMarkov.firstExitAt domain time).indicator
      (fun path => values (path (time + offset))) path
      ∂DiscreteMarkov.pathLaw
        (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        (xiVertexSpeedMeasure system mass level)) =
    ∫ path, (DiscreteMarkov.firstExitAt domain time).indicator
      (fun path => (xiNativeRandomWalk system rulesConnected mass level ^ offset) values (path time)) path
      ∂DiscreteMarkov.pathLaw
        (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        (xiVertexSpeedMeasure system mass level) := by
  have decomposition := DiscreteMarkov.firstExitAt_integral_future
    (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
    (xiNativeSpeedProbabilityMeasure system mass level) domain time offset (fun vertex => values vertex)
  simp_rw [xiNativeDiscreteKernel_power_integral system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level offset values] at decomposition
  exact decomposition

/-- A true native path exit bound. The explicitly stated persistence estimate
is the remaining analytic input; this theorem does not claim native tightness. -/
theorem xiNativeDiscrete_exit_probability_le_endpoint_expectation
    (domain : Finset (XiVtx system level)) (horizon : ℕ)
    (function : XiVtx system level → ℝ) (functionNonnegative : ∀ vertex, 0 ≤ function vertex)
    (persistence : ℝ)
    (persistentAfterExit : ∀ time ≤ horizon, ∀ vertex ∉ domain,
      persistence ≤ (xiNativeRandomWalk system rulesConnected mass level ^ (horizon - time))
        (xiFiniteSpeedL2 system mass level function) vertex) :
    persistence * ((DiscreteMarkov.pathLaw
      (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
      (xiVertexSpeedMeasure system mass level)) (graphSurvivalEvent domain horizon)ᶜ).toReal ≤
      ∫ path, function (path horizon) ∂DiscreteMarkov.pathLaw
        (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        (xiVertexSpeedMeasure system mass level) := by
  apply DiscreteMarkov.exit_probability_le_endpoint_expectation
    (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
    (xiNativeSpeedProbabilityMeasure system mass level) domain horizon function functionNonnegative persistence
  intro time bounded vertex outside
  have representation := xiNativeDiscreteKernel_power_integral system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level (horizon - time) (xiFiniteSpeedL2 system mass level function) vertex
  simp_rw [xiFiniteSpeedL2_apply system rulesConnected mass level] at representation
  exact (persistentAfterExit time bounded vertex outside).trans_eq representation.symm

end
end EIGS

#print axioms IGS.Sec31.DiscreteMarkov.mem_firstExitAt
#print axioms IGS.Sec31.DiscreteMarkov.firstExitAt_disjoint
#print axioms IGS.Sec31.DiscreteMarkov.exits_by_iff
#print axioms IGS.Sec31.DiscreteMarkov.firstExitAt_integral_future
#print axioms IGS.Sec31.DiscreteMarkov.firstExitAt_integral_final
#print axioms IGS.Sec31.DiscreteMarkov.exitBy_integral_final
#print axioms IGS.Sec31.DiscreteMarkov.exit_probability_le_endpoint_expectation
#print axioms EIGS.xiNativeDiscrete_firstExit_integral_future
#print axioms EIGS.xiNativeDiscrete_exit_probability_le_endpoint_expectation
