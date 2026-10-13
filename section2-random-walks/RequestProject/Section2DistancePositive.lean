import RequestProject.Section2PerronConvergence

/-! The path formulation of distance positivity and its electrical cut formulation.
Colour consistency states exactly that the underlying undirected edge has a
well-defined colour. It is automatic for a chosen orientation of a coloured
simple graph, but is not automatic for the legacy multigraph data type.
-/

namespace EIGS.Network

variable {K : ℕ} (network : EIGS.Network K)

def ColourConsistent : Prop := ∀ first second : network.E,
  s(network.tail first, network.head first) =
    s(network.tail second, network.head second) →
      network.color first = network.color second

def UsesColour {source sink : network.V}
    (path : network.toSimpleGraph.Walk source sink) (colour : Fin K) : Prop :=
  ∃ edge : network.E, network.color edge = colour ∧
    s(network.tail edge, network.head edge) ∈ path.edges

theorem withoutColour_le (colour : Fin K) :
    network.withoutColour colour ≤ network.toSimpleGraph := by
  intro source sink adjacent
  refine ⟨adjacent.1, ?_⟩
  rcases adjacent.2 with ⟨edge, _, tail_eq, head_eq⟩ | ⟨edge, _, tail_eq, head_eq⟩
  · exact Or.inl ⟨edge, tail_eq, head_eq⟩
  · exact Or.inr ⟨edge, tail_eq, head_eq⟩

theorem reachable_withoutColour_iff_path_avoids_colour
    (consistent : network.ColourConsistent) (colour : Fin K)
    (source sink : network.V) :
    (network.withoutColour colour).Reachable source sink ↔
      ∃ path : network.toSimpleGraph.Walk source sink,
        path.IsPath ∧ ¬ network.UsesColour path colour := by
  classical
  constructor
  · intro reachable
    obtain ⟨path, simple_path⟩ := reachable.exists_isPath
    refine ⟨path.mapLe (network.withoutColour_le colour),
      simple_path.mapLe _, ?_⟩
    rintro ⟨edge, colour_eq, edge_mem⟩
    rw [path.edges_mapLe_eq_edges] at edge_mem
    have adjacent := path.adj_of_mem_edges edge_mem
    rcases adjacent.2 with
      ⟨retained, colour_ne, tail_eq, head_eq⟩ |
      ⟨retained, colour_ne, tail_eq, head_eq⟩
    · apply colour_ne
      exact (consistent retained edge (by simp [tail_eq, head_eq])).trans colour_eq
    · apply colour_ne
      exact (consistent retained edge (by simp [tail_eq, head_eq, Sym2.eq_swap])).trans colour_eq
  · rintro ⟨path, _, avoids_colour⟩
    have retained_edges : ∀ pair ∈ path.edges,
        pair ∈ (network.withoutColour colour).edgeSet := by
      intro pair pair_mem
      induction pair using Sym2.inductionOn with
      | _ first second =>
        have adjacent := path.adj_of_mem_edges pair_mem
        refine ⟨adjacent.1, ?_⟩
        rcases adjacent.2 with ⟨edge, tail_eq, head_eq⟩ | ⟨edge, tail_eq, head_eq⟩
        · refine Or.inl ⟨edge, ?_, tail_eq, head_eq⟩
          intro colour_eq
          apply avoids_colour
          exact ⟨edge, colour_eq, by simpa [tail_eq, head_eq] using pair_mem⟩
        · refine Or.inr ⟨edge, ?_, tail_eq, head_eq⟩
          intro colour_eq
          apply avoids_colour
          exact ⟨edge, colour_eq, by simpa [tail_eq, head_eq, Sym2.eq_swap] using pair_mem⟩
    exact ⟨path.transfer (network.withoutColour colour) retained_edges⟩

theorem not_reachable_withoutColour_iff_every_path_uses_colour
    (consistent : network.ColourConsistent) (colour : Fin K)
    (source sink : network.V) :
    ¬ (network.withoutColour colour).Reachable source sink ↔
      ∀ path : network.toSimpleGraph.Walk source sink,
        path.IsPath → network.UsesColour path colour := by
  classical
  rw [network.reachable_withoutColour_iff_path_avoids_colour consistent]
  push_neg
  rfl

end EIGS.Network

namespace EIGS.RuleSystem

open scoped BigOperators

variable {K : ℕ}

/-- The path condition supplies the cut hypothesis for electrical resistance
renormalisation. This theorem is not a graph-distance growth assertion. -/
theorem resistance_normalized_iterate_limit_of_path_distance_positive
    (rules : EIGS.RuleSystem K) (colours_positive : 0 < K)
    (consistent : ∀ colour, (rules.R colour).ColourConsistent)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour) :
    ∃ (rate limit : ℝ) (vector : Fin K → ℝ),
      0 < rate ∧ 0 < limit ∧ (∀ colour, 0 < vector colour) ∧
      (∑ colour, vector colour) = 1 ∧
      rules.toRenormMap.apply vector = rate • vector ∧
      Filter.Tendsto (fun level => fun colour =>
        rules.toRenormMap.apply^[level] (fun _ => 1) colour / rate ^ level)
        Filter.atTop (nhds (limit • vector)) := by
  apply rules.distance_positive_normalized_iterate_limit colours_positive
  intro ruleColour edgeColour
  exact ((rules.R ruleColour).not_reachable_withoutColour_iff_every_path_uses_colour
    (consistent ruleColour) edgeColour _ _).mpr (distance_positive ruleColour edgeColour)

@[deprecated resistance_normalized_iterate_limit_of_path_distance_positive (since := "2026-10-13")]
alias path_distance_positive_normalized_iterate_limit :=
  resistance_normalized_iterate_limit_of_path_distance_positive

end EIGS.RuleSystem
