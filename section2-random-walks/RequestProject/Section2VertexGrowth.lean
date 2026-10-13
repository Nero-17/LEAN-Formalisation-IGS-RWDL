import RequestProject.Section2MassGrowth
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

/-- Forgetting loops and repeated edges can only decrease the edge count. -/
theorem Network.simpleGraph_edge_card_le (network : Network K) :
    network.toSimpleGraph.edgeFinset.card ≤ Fintype.card network.E := by
  have edge_subset : network.toSimpleGraph.edgeFinset ⊆
      Finset.univ.image (fun edge => s(network.tail edge, network.head edge)) := by
    intro pair pair_mem
    induction pair using Sym2.inductionOn with
    | _ source sink =>
      have adjacency : network.toSimpleGraph.Adj source sink :=
        SimpleGraph.mem_edgeFinset.mp pair_mem
      rcases adjacency.2 with ⟨edge, tail_eq, head_eq⟩ | ⟨edge, tail_eq, head_eq⟩
      · exact Finset.mem_image.mpr ⟨edge, Finset.mem_univ _, by simp [tail_eq, head_eq]⟩
      · exact Finset.mem_image.mpr ⟨edge, Finset.mem_univ _,
          by simp [tail_eq, head_eq, Sym2.eq_swap]⟩
  exact (Finset.card_le_card edge_subset).trans (by simpa using Finset.card_image_le)

theorem rule_interior_nonempty (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour)) (colour : Fin K) :
    Nonempty {vertex : (system.rule colour).V //
      vertex ≠ system.plantPlus colour ∧ vertex ≠ system.plantMinus colour} := by
  letI : Nontrivial (system.rule colour).V :=
    ⟨⟨system.plantPlus colour, system.plantMinus colour, system.plant_ne colour⟩⟩
  obtain ⟨neighbor, adjacency⟩ :=
    (rule_connected colour).preconnected.exists_adj_of_nontrivial (system.plantPlus colour)
  refine ⟨neighbor, adjacency.ne.symm, ?_⟩
  intro neighbor_is_sink
  exact planting_nonadjacent colour (neighbor_is_sink ▸ adjacency)

theorem xiNetwork_edges_le_successor_vertices (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour)) (level : ℕ) :
    Fintype.card (XiEdge system.toRuleData level) ≤ Fintype.card (XiVtx system (level + 1)) := by
  have interior_nonempty := rule_interior_nonempty system rule_connected planting_nonadjacent
  let interior_vertex := fun colour => Classical.choice (interior_nonempty colour)
  let edge_to_vertex : XiEdge system.toRuleData level → XiVtx system (level + 1) :=
    fun edge => Sum.inr ⟨edge, interior_vertex (XiCol system.toRuleData level edge)⟩
  apply Fintype.card_le_of_injective edge_to_vertex
  intro first second same_vertex
  exact congrArg Sigma.fst (Sum.inr.inj same_vertex)

/-- The actual vertex count has the same constructed growth rate as edge mass.
Nonadjacent planting vertices provide a new interior vertex in every copy. -/
theorem xiNetwork_vertex_growth_from_rules (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ rate lower upper : ℝ, 0 < rate ∧ 0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * rate ^ level ≤ (Fintype.card (XiVtx system level) : ℝ) ∧
        (Fintype.card (XiVtx system level) : ℝ) ≤ upper * rate ^ level := by
  obtain ⟨rate, mass_lower, mass_upper, rate_positive, mass_lower_positive,
    mass_upper_positive, mass_growth⟩ := eigs_mass_growth_from_rules system rule_connected distance_positive
  refine ⟨rate, min 2 (mass_lower / rate), 2 * mass_upper, rate_positive,
    lt_min (by norm_num) (div_pos mass_lower_positive rate_positive), by positivity, fun level => ?_⟩
  constructor
  · cases level with
    | zero => simpa [XiVtx] using min_le_left (2 : ℝ) (mass_lower / rate)
    | succ level =>
        calc
          min 2 (mass_lower / rate) * rate ^ (level + 1) ≤
              (mass_lower / rate) * rate ^ (level + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_pos rate_positive _).le
          _ = mass_lower * rate ^ level := by rw [pow_succ]; field_simp <;> ring
          _ ≤ (totalEdges system.toRuleData level : ℝ) := (mass_growth level).1
          _ ≤ _ := by exact_mod_cast
            xiNetwork_edges_le_successor_vertices system rule_connected planting_nonadjacent level
  · have vertex_card_bound :=
      (xiSimpleGraph_connected system rule_connected level).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      at vertex_card_bound
    have vertex_card_bound_network := vertex_card_bound.trans
      (Nat.add_le_add_right ((XiNetwork system level).simpleGraph_edge_card_le) 1)
    have mass_positive : 0 < (totalEdges system.toRuleData level : ℝ) :=
      lt_of_lt_of_le (mul_pos mass_lower_positive (pow_pos rate_positive level)) (mass_growth level).1
    have edge_count_one : (1 : ℝ) ≤ totalEdges system.toRuleData level := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp mass_positive.ne'))
    have vertex_card_bound_real : (Fintype.card (XiVtx system level) : ℝ) ≤
        (totalEdges system.toRuleData level : ℝ) + 1 := by exact_mod_cast vertex_card_bound_network
    nlinarith [(mass_growth level).2]

end EIGS
