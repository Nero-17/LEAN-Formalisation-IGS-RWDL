import RequestProject.Section2LocalBall

/-! The exact radius in the manuscript's recurrence definition is a fixed
fraction of the maximum distance from the chosen vertex. This maximum is
constructed on the actual finite graph, and its proper-ball and diameter
comparisons are proved here. No geometric growth estimate is assumed. -/

namespace EIGS

open scoped Classical
noncomputable section
variable {Vertex : Type*} [Fintype Vertex]

def finiteGraphEccentricity (graph : SimpleGraph Vertex) (center : Vertex) : ℝ :=
  Finset.univ.sup' ⟨center, Finset.mem_univ center⟩ (fun vertex => (graph.dist center vertex : ℝ))

theorem graphDistance_le_finiteGraphEccentricity (graph : SimpleGraph Vertex) (center vertex : Vertex) :
    (graph.dist center vertex : ℝ) ≤ finiteGraphEccentricity graph center :=
  Finset.le_sup' (fun point => (graph.dist center point : ℝ)) (Finset.mem_univ vertex)

theorem finiteGraphEccentricity_nonnegative (graph : SimpleGraph Vertex) (center : Vertex) :
    0 ≤ finiteGraphEccentricity graph center := by
  simpa only [SimpleGraph.dist_self, Nat.cast_zero] using
    graphDistance_le_finiteGraphEccentricity graph center center

theorem finiteGraphEccentricity_positive [Nontrivial Vertex]
    (graph : SimpleGraph Vertex) (connected : graph.Connected) (center : Vertex) :
    0 < finiteGraphEccentricity graph center := by
  obtain ⟨neighbor, adjacency⟩ := connected.preconnected.exists_adj_of_nontrivial center
  have distanceOne := SimpleGraph.dist_eq_one_iff_adj.mpr adjacency
  have bounded := graphDistance_le_finiteGraphEccentricity graph center neighbor
  rw [distanceOne, Nat.cast_one] at bounded
  exact zero_lt_one.trans_le bounded

theorem finiteGraph_fractional_eccentricity_ball_proper [Nontrivial Vertex]
    (graph : SimpleGraph Vertex) (connected : graph.Connected) (center : Vertex)
    (fraction : ℝ) (fractionStrict : fraction < 1) :
    (finiteGraphBall graph center (fraction * finiteGraphEccentricity graph center))ᶜ.Nonempty := by
  by_contra noOutside
  have everyInside : ∀ vertex, vertex ∈ finiteGraphBall graph center
      (fraction * finiteGraphEccentricity graph center) := by
    intro vertex
    by_contra outside
    exact noOutside ⟨vertex, Finset.mem_compl.mpr outside⟩
  have maximumBound : finiteGraphEccentricity graph center ≤
      fraction * finiteGraphEccentricity graph center := by
    apply Finset.sup'_le
    intro vertex _
    exact (Finset.mem_filter.mp (everyInside vertex)).2.le
  nlinarith [finiteGraphEccentricity_positive graph connected center]

theorem graphDistance_le_twice_finiteGraphEccentricity
    (graph : SimpleGraph Vertex) (connected : graph.Connected) (center first last : Vertex) :
    (graph.dist first last : ℝ) ≤ 2 * finiteGraphEccentricity graph center := by
  have triangle : graph.dist first last ≤ graph.dist first center + graph.dist center last :=
    connected.dist_triangle
  have realTriangle : (graph.dist first last : ℝ) ≤
      (graph.dist first center : ℝ) + (graph.dist center last : ℝ) := by exact_mod_cast triangle
  have firstBound := graphDistance_le_finiteGraphEccentricity graph center first
  have lastBound := graphDistance_le_finiteGraphEccentricity graph center last
  rw [SimpleGraph.dist_comm] at firstBound
  linarith

end
end EIGS

#print axioms EIGS.graphDistance_le_finiteGraphEccentricity
#print axioms EIGS.finiteGraphEccentricity_positive
#print axioms EIGS.finiteGraph_fractional_eccentricity_ball_proper
#print axioms EIGS.graphDistance_le_twice_finiteGraphEccentricity
