import RequestProject.Section31.FiniteGraphFloorExitTime
import RequestProject.Section2LocalBall

/-! Exact interpretation of the actual native floor-clock first exit as
an attained finite prefix radius event. This uses actual exit duration,
including infinite duration, rather than a one-time marginal event. -/

namespace EIGS
open MeasureTheory
open IGS.Sec31.DiscreteMarkov
open scoped NNReal ENNReal
noncomputable section
variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]

theorem graphFloorExitTime_le_iff_exists_outside
    (domain : Finset Vertex) (rate : ℝ≥0) (ratePositive : 0 < rate)
    (path : ℕ → Vertex) (time : ℝ≥0) :
    graphFloorExitTime domain rate path ≤ (time : ℝ≥0∞) ↔
      ∃ index : ℕ, index ≤ ⌊(time : ℝ) * (rate : ℝ)⌋₊ ∧ path index ∉ domain := by
  rw [← not_lt, graphFloorExitTime_survival_iff domain rate ratePositive path time]
  simp only [graphSurvivalEvent, Set.mem_setOf_eq, not_forall]
  constructor <;> rintro ⟨index, bounded, outside⟩ <;> exact ⟨index, bounded, outside⟩

theorem graphFloorBallExitTime_le_iff_maximal_graph_distance
    (graph : SimpleGraph Vertex) (center : Vertex) (radius : ℝ)
    (rate : ℝ≥0) (ratePositive : 0 < rate) (path : ℕ → Vertex) (time : ℝ≥0) :
    graphFloorExitTime (finiteGraphBall graph center radius) rate path ≤ (time : ℝ≥0∞) ↔
      ∃ index : ℕ, index ≤ ⌊(time : ℝ) * (rate : ℝ)⌋₊ ∧
        radius ≤ (graph.dist center (path index) : ℝ) := by
  rw [graphFloorExitTime_le_iff_exists_outside (finiteGraphBall graph center radius) rate ratePositive path time]
  simp only [finiteGraphBall, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]

end
end EIGS

#print axioms EIGS.graphFloorExitTime_le_iff_exists_outside
#print axioms EIGS.graphFloorBallExitTime_le_iff_maximal_graph_distance
