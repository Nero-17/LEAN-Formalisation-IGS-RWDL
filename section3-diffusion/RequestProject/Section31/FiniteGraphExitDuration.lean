import RequestProject.Section31.FiniteGraphSurvivalPathLaw

/-! The actual pathwise exit duration, its first-exit interpretation, and its
expectation under the actual graph Ionescu--Tulcea law. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open IGS.Sec31.DiscreteMarkov

noncomputable section

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]

def graphExitDuration (domain : Finset Vertex) (path : ℕ → Vertex) : ℝ≥0∞ :=
  ∑' time : ℕ, (graphSurvivalEvent domain time).indicator (fun _ => (1 : ℝ≥0∞)) path

theorem graphExitDuration_measurable (domain : Finset Vertex) :
    Measurable (graphExitDuration domain) := by
  exact Measurable.ennreal_tsum (fun time =>
    measurable_const.indicator (graphSurvivalEvent_measurable domain time))

theorem graphExitDuration_eq_of_first_exit (domain : Finset Vertex)
    (path : ℕ → Vertex) (duration : ℕ)
    (before_exit : ∀ time < duration, path time ∈ domain)
    (at_exit : path duration ∉ domain) : graphExitDuration domain path = duration := by
  classical
  have survival_iff (time : ℕ) : path ∈ graphSurvivalEvent domain time ↔ time < duration := by
    constructor
    · intro survives
      by_contra too_late
      exact at_exit (survives duration (Nat.le_of_not_gt too_late))
    · intro before
      exact fun index bounded => before_exit index (lt_of_le_of_lt bounded before)
  unfold graphExitDuration
  rw [tsum_eq_sum (s := Finset.range duration) (fun time outside => by
    apply Set.indicator_of_notMem
    rw [survival_iff]
    simpa only [Finset.mem_range] using outside)]
  have terms : ∀ time ∈ Finset.range duration,
      (graphSurvivalEvent domain time).indicator (fun _ => (1 : ℝ≥0∞)) path = 1 := by
    intro time inside
    exact Set.indicator_of_mem ((survival_iff time).mpr (Finset.mem_range.mp inside)) _
  rw [Finset.sum_congr rfl terms]
  simp

theorem graphExitDuration_eq_top_of_never_exit (domain : Finset Vertex)
    (path : ℕ → Vertex) (always_inside : ∀ time, path time ∈ domain) :
    graphExitDuration domain path = ⊤ := by
  have survives (time : ℕ) : path ∈ graphSurvivalEvent domain time :=
    fun index _ => always_inside index
  simp only [graphExitDuration, Set.indicator_of_mem (survives _)]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

theorem graphSurvivalEvent_measure (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree_positive : ∀ vertex, 0 < graph.degree vertex) (domain : Finset Vertex)
    (time : ℕ) (vertex : Vertex) :
    (pathLaw (finiteGraphTransitionKernel graph degree_positive) (Measure.dirac vertex))
      (graphSurvivalEvent domain time) = ENNReal.ofReal (surv graph domain time vertex) := by
  rw [← graphSurvivalEvent_probability graph degree_positive domain time vertex,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem graphExitDuration_lintegral (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree_positive : ∀ vertex, 0 < graph.degree vertex)
    (connected : graph.Connected) {domain : Finset Vertex} (proper : domainᶜ.Nonempty)
    (vertex : Vertex) :
    (∫⁻ path, graphExitDuration domain path
      ∂pathLaw (finiteGraphTransitionKernel graph degree_positive) (Measure.dirac vertex)) =
      ENNReal.ofReal (expExit graph domain vertex) := by
  unfold graphExitDuration
  rw [lintegral_tsum (fun time =>
    (measurable_const.indicator (graphSurvivalEvent_measurable domain time)).aemeasurable)]
  simp_rw [lintegral_indicator_const (graphSurvivalEvent_measurable domain _) (1 : ℝ≥0∞),
    one_mul,
    graphSurvivalEvent_measure graph degree_positive]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun time => surv_nonneg (G := graph) time vertex)
    (expExit_summable connected proper vertex)).symm

theorem graphExitDuration_ae_finite (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree_positive : ∀ vertex, 0 < graph.degree vertex)
    (connected : graph.Connected) {domain : Finset Vertex} (proper : domainᶜ.Nonempty)
    (vertex : Vertex) :
    ∀ᵐ path ∂pathLaw (finiteGraphTransitionKernel graph degree_positive) (Measure.dirac vertex),
      graphExitDuration domain path < ⊤ := by
  apply ae_lt_top (graphExitDuration_measurable domain)
  rw [graphExitDuration_lintegral graph degree_positive connected proper vertex]
  exact ENNReal.ofReal_ne_top

theorem graphPath_ae_eventually_exits (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree_positive : ∀ vertex, 0 < graph.degree vertex)
    (connected : graph.Connected) {domain : Finset Vertex} (proper : domainᶜ.Nonempty)
    (vertex : Vertex) :
    ∀ᵐ path ∂pathLaw (finiteGraphTransitionKernel graph degree_positive) (Measure.dirac vertex),
      ∃ time : ℕ, path time ∉ domain := by
  filter_upwards [graphExitDuration_ae_finite graph degree_positive connected proper vertex]
    with path finite
  by_contra never_exits
  push_neg at never_exits
  rw [graphExitDuration_eq_top_of_never_exit domain path never_exits] at finite
  exact lt_irrefl _ finite

theorem graphExitDuration_integral (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree_positive : ∀ vertex, 0 < graph.degree vertex)
    (connected : graph.Connected) {domain : Finset Vertex} (proper : domainᶜ.Nonempty)
    (vertex : Vertex) :
    (∫ path, (graphExitDuration domain path).toReal
      ∂pathLaw (finiteGraphTransitionKernel graph degree_positive) (Measure.dirac vertex)) =
      expExit graph domain vertex := by
  rw [integral_toReal (graphExitDuration_measurable domain).aemeasurable
    (graphExitDuration_ae_finite graph degree_positive connected proper vertex),
    graphExitDuration_lintegral graph degree_positive connected proper vertex,
    ENNReal.toReal_ofReal (expExit_nonneg (G := graph) vertex)]

end
end EIGS

#print axioms EIGS.graphExitDuration_eq_of_first_exit
#print axioms EIGS.graphExitDuration_eq_top_of_never_exit
#print axioms EIGS.graphSurvivalEvent_measure
#print axioms EIGS.graphExitDuration_lintegral
#print axioms EIGS.graphExitDuration_ae_finite
#print axioms EIGS.graphPath_ae_eventually_exits
#print axioms EIGS.graphExitDuration_integral
