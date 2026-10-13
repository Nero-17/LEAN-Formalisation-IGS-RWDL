import RequestProject.Section2DegreeGrowth
import RequestProject.Section2ConcreteSimplicity
import RequestProject.Section2SimpleNetwork

/-! Actual graph balls at the first metric scale, and their growth along an
actual vertex lineage from the primitive degree matrix. These are concrete
finite-ball estimates, not the full mesoscopic ball theorem. -/

namespace EIGS

open scoped BigOperators Classical

noncomputable def finiteGraphBall {Vertex : Type*} [Fintype Vertex]
    (graph : SimpleGraph Vertex) (center : Vertex) (radius : ℝ) : Finset Vertex :=
  Finset.univ.filter (fun vertex => (graph.dist center vertex : ℝ) < radius)

theorem finiteGraphBall_eq_insert_neighbors {Vertex : Type*} [Fintype Vertex]
    [DecidableEq Vertex] (graph : SimpleGraph Vertex) (connected : graph.Connected)
    (center : Vertex) {radius : ℝ} (radius_gt_one : 1 < radius) (radius_le_two : radius ≤ 2) :
    finiteGraphBall graph center radius = insert center (graph.neighborFinset center) := by
  ext vertex
  simp only [finiteGraphBall, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, SimpleGraph.mem_neighborFinset]
  constructor
  · intro distance_lt_radius
    have distance_lt_two : (graph.dist center vertex : ℝ) < 2 :=
      distance_lt_radius.trans_le radius_le_two
    have distance_nat_lt_two : graph.dist center vertex < 2 := by exact_mod_cast distance_lt_two
    have distance_le_one : graph.dist center vertex ≤ 1 := by omega
    have alternatives : graph.dist center vertex = 0 ∨ graph.dist center vertex = 1 := by omega
    rcases alternatives with zero_distance | one_distance
    · exact Or.inl ((connected.dist_eq_zero_iff.mp zero_distance).symm)
    · exact Or.inr (SimpleGraph.dist_eq_one_iff_adj.mp one_distance)
  · rintro (rfl | adjacent)
    · simpa only [SimpleGraph.dist_self, Nat.cast_zero] using
        (zero_lt_one.trans radius_gt_one)
    · simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr adjacent, Nat.cast_one]
        using radius_gt_one

theorem finiteGraphBall_card_eq_degree_add_one {Vertex : Type*} [Fintype Vertex]
    [DecidableEq Vertex] (graph : SimpleGraph Vertex) (connected : graph.Connected)
    (center : Vertex) {radius : ℝ} (radius_gt_one : 1 < radius) (radius_le_two : radius ≤ 2) :
    (finiteGraphBall graph center radius).card = graph.degree center + 1 := by
  rw [finiteGraphBall_eq_insert_neighbors graph connected center radius_gt_one radius_le_two,
    Finset.card_insert_of_notMem (graph.notMem_neighborFinset_self center)]
  rfl

variable {K : ℕ}

theorem Network.degree_eq_incident_edge_sum (network : Network K)
    (loopless : network.Loopless) (unique_edges : network.EdgesUnique) (vertex : network.V) :
    (network.toSimpleGraph.degree vertex : ℝ) =
      ∑ edge, ((if network.tail edge = vertex then (1 : ℝ) else 0) +
        (if network.head edge = vertex then (1 : ℝ) else 0)) := by
  have pair_sum := network.sum_adj_eq_sum_edges loopless unique_edges
    (fun source _ => if source = vertex then (1 : ℝ) else 0)
  have left_sum :
      (∑ source, ∑ sink, if network.toSimpleGraph.Adj source sink then
        (if source = vertex then (1 : ℝ) else 0) else 0) =
      ∑ sink, if network.toSimpleGraph.Adj vertex sink then (1 : ℝ) else 0 := by
    calc
      _ = ∑ source, if source = vertex then
          (∑ sink, if network.toSimpleGraph.Adj source sink then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro source _
        by_cases same : source = vertex <;> simp [same]
      _ = _ := by simp
  rw [left_sum] at pair_sum
  have neighbor_sum : (∑ sink, if network.toSimpleGraph.Adj vertex sink then (1 : ℝ) else 0) =
      (network.toSimpleGraph.degree vertex : ℝ) := by
    rw [← Finset.sum_filter]
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  exact neighbor_sum.symm.trans pair_sum

theorem xiSimpleGraph_degree_eq_degree_state_sum (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (level : ℕ) (vertex : XiVtx system level) :
    ((XiSimpleGraph system level).degree vertex : ℝ) =
      ∑ state, degVec system level vertex state := by
  have incident_sum := (XiNetwork system level).degree_eq_incident_edge_sum
    (xiNetwork_loopless system rule_connected rules_loopless level)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent level)
    vertex
  have out_sum : (∑ colour, (outDeg system level vertex colour : ℝ)) =
      ∑ edge, if XiTail system level edge = vertex then (1 : ℝ) else 0 := by
    simp only [outDeg, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases incident : XiTail system level edge = vertex <;> simp [incident]
  have in_sum : (∑ colour, (inDeg system level vertex colour : ℝ)) =
      ∑ edge, if XiHead system level edge = vertex then (1 : ℝ) else 0 := by
    simp only [inDeg, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases incident : XiHead system level edge = vertex <;> simp [incident]
  rw [Fintype.sum_sum_type]
  change ((XiSimpleGraph system level).degree vertex : ℝ) =
    (∑ colour, (outDeg system level vertex colour : ℝ)) +
      ∑ colour, (inDeg system level vertex colour : ℝ)
  rw [out_sum, in_sum, ← Finset.sum_add_distrib]
  exact incident_sum

theorem xiSimpleGraph_small_ball_growth_from_primitive_rules (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (primitive_degree : (degreeMatrix system).IsPrimitive) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ initial_level (vertex : XiVtx system initial_level),
      ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ steps (radius : ℝ),
        1 < radius → radius ≤ 2 →
        lower * rate ^ steps ≤
          ((finiteGraphBall (XiSimpleGraph system (initial_level + steps))
            (xiForward system initial_level steps vertex) radius).card : ℝ) ∧
        ((finiteGraphBall (XiSimpleGraph system (initial_level + steps))
          (xiForward system initial_level steps vertex) radius).card : ℝ) ≤ upper * rate ^ steps := by
  obtain ⟨rate, rate_positive, degree_growth⟩ :=
    degree_growth_from_primitive_rules system rule_connected primitive_degree
  refine ⟨rate, rate_positive, fun initial_level vertex => ?_⟩
  obtain ⟨lower, upper, lower_positive, upper_positive, bounds⟩ := degree_growth initial_level vertex
  refine ⟨lower, 2 * upper, lower_positive, by positivity,
    fun steps radius radius_gt_one radius_le_two => ?_⟩
  let center := xiForward system initial_level steps vertex
  let graph := XiSimpleGraph system (initial_level + steps)
  have connected : graph.Connected := xiSimpleGraph_connected system rule_connected _
  letI : Nontrivial (XiVtx system (initial_level + steps)) :=
    ⟨⟨xiPositiveTerminal system _, xiNegativeTerminal system _, xiTerminals_distinct system _⟩⟩
  obtain ⟨neighbor, adjacent⟩ := connected.preconnected.exists_adj_of_nontrivial center
  have degree_at_least_one : (1 : ℝ) ≤ graph.degree center := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt ((graph.degree_pos_iff_exists_adj center).mpr ⟨neighbor, adjacent⟩)))
  rw [finiteGraphBall_card_eq_degree_add_one graph connected center radius_gt_one radius_le_two,
    Nat.cast_add, Nat.cast_one]
  have degree_bounds := bounds steps
  rw [← xiSimpleGraph_degree_eq_degree_state_sum system rule_connected rules_loopless
    rules_unique planting_nonadjacent] at degree_bounds
  constructor <;> nlinarith [degree_bounds.1, degree_bounds.2]

end EIGS

#print axioms EIGS.xiSimpleGraph_degree_eq_degree_state_sum
#print axioms EIGS.xiSimpleGraph_small_ball_growth_from_primitive_rules
