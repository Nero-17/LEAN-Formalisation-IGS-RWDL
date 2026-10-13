import RequestProject.Section2RuleNeighborVoltage

/-! A genuine source-incident rule edge with uniformly positive endpoint
voltages for every actual Psi iterate, using nonadjacent boundary terminals. -/

namespace EIGS

open scoped Classical

variable {K : ℕ}

theorem rule_Psi_positive_incident_edge (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower_voltage : ℝ, 0 < lower_voltage ∧ lower_voltage ≤ 1 ∧
      ∀ colour steps (source sink : (system.ruleNetwork colour).V)
        (potential : (system.ruleNetwork colour).V → ℝ),
        source ≠ sink → ¬ (system.ruleNetwork colour).toSimpleGraph.Adj source sink →
        potential source = 1 → potential sink = 0 →
        (∀ competitor : (system.ruleNetwork colour).V → ℝ,
          competitor source = 1 → competitor sink = 0 →
          ((system.ruleNetwork colour).potentialNetwork
            ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
            (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)).energy potential ≤
          ((system.ruleNetwork colour).potentialNetwork
            ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
            (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)).energy competitor) →
        ∃ edge : (system.ruleNetwork colour).E,
          ((system.ruleNetwork colour).tail edge = source ∨ (system.ruleNetwork colour).head edge = source) ∧
          lower_voltage ≤ potential ((system.ruleNetwork colour).tail edge) ∧
          lower_voltage ≤ potential ((system.ruleNetwork colour).head edge) := by
  obtain ⟨original_lower, original_lower_positive, neighbor_lower⟩ :=
    rule_Psi_source_neighbor_voltage_lower system rule_connected distance_positive
  refine ⟨min original_lower 1, lt_min original_lower_positive zero_lt_one, min_le_right _ _,
    fun colour steps source sink potential source_ne_sink nonadjacent source_value sink_value minimal => ?_⟩
  letI : Nontrivial (system.rule colour).V := ⟨⟨source, sink, source_ne_sink⟩⟩
  obtain ⟨neighbor, adjacency⟩ := (rule_connected colour).preconnected.exists_adj_of_nontrivial source
  have neighbor_ne_source : neighbor ≠ source := adjacency.ne.symm
  have neighbor_ne_sink : neighbor ≠ sink := by
    intro same
    subst neighbor
    exact nonadjacent adjacency
  have edge_exists : ∃ edge : (system.ruleNetwork colour).E,
      (((system.ruleNetwork colour).tail edge = source ∧ (system.ruleNetwork colour).head edge = neighbor) ∨
        ((system.ruleNetwork colour).tail edge = neighbor ∧ (system.ruleNetwork colour).head edge = source)) := by
    change (system.ruleNetwork colour).toSimpleGraph.Adj source neighbor at adjacency
    simp only [Network.toSimpleGraph, SimpleGraph.fromRel_adj] at adjacency
    rcases adjacency.2 with ⟨edge, endpoints⟩ | ⟨edge, endpoints⟩
    · exact ⟨edge, Or.inl endpoints⟩
    · exact ⟨edge, Or.inr endpoints⟩
  obtain ⟨edge, endpoints⟩ := edge_exists
  have neighbor_voltage := neighbor_lower colour steps source sink neighbor potential source_ne_sink
    neighbor_ne_source neighbor_ne_sink source_value sink_value minimal edge endpoints
  have lower_neighbor := (min_le_left original_lower 1).trans neighbor_voltage
  have lower_source : min original_lower 1 ≤ potential source := by rw [source_value]; exact min_le_right _ _
  rcases endpoints with ⟨tail_source, head_neighbor⟩ | ⟨tail_neighbor, head_source⟩
  · refine ⟨edge, Or.inl tail_source, ?_, ?_⟩
    · simpa only [tail_source] using lower_source
    · simpa only [head_neighbor] using lower_neighbor
  · refine ⟨edge, Or.inr head_source, ?_, ?_⟩
    · simpa only [tail_neighbor] using lower_neighbor
    · simpa only [head_source] using lower_source

end EIGS

#print axioms EIGS.rule_Psi_positive_incident_edge
