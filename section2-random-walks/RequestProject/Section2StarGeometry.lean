import RequestProject.Section2DescendantBall
import RequestProject.Section2GroundedResistanceBounds

/-! Every vertex of the actual multistep incident star lies in a uniformly
controlled original-unit metric ball. -/

namespace EIGS

open scoped Classical

variable {K : ℕ}

theorem xiIncidentStar_weightedDistance_bound (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) {rate : ℝ} (rate_ge_two : 2 ≤ rate)
    (eigenpair : (system.ruleFamily rule_connected).metricLengths lengths = rate • lengths)
    (coarse steps : ℕ) (center : XiVtx system coarse) {vertex : XiVtx system (coarse + steps)}
    (vertex_star : xiIncidentStar system coarse center steps vertex) :
    (XiNetwork system (coarse + steps)).weightedDistance lengths
      (xiForward system coarse steps center) vertex ≤ 3 * xiRuleRadius system lengths * rate ^ steps := by
  have rate_nonnegative : 0 ≤ rate := (by norm_num : (0 : ℝ) ≤ 2).trans rate_ge_two
  have radius_nonnegative := xiRuleRadius_nonnegative system nonnegative
  letI : Nontrivial (XiVtx system (coarse + steps)) :=
    ⟨⟨xiPositiveTerminal system _, xiNegativeTerminal system _, xiTerminals_distinct system _⟩⟩
  obtain ⟨neighbor, adjacent⟩ :=
    (xiSimpleGraph_connected system rule_connected _).preconnected.exists_adj_of_nontrivial vertex
  obtain ⟨edge, vertex_endpoint⟩ : ∃ edge : XiEdge system.toRuleData (coarse + steps),
      XiTail system (coarse + steps) edge = vertex ∨ XiHead system (coarse + steps) edge = vertex := by
    rcases adjacent.2 with ⟨edge, tail_vertex, _⟩ | ⟨edge, _, head_vertex⟩
    · exact ⟨edge, Or.inl tail_vertex⟩
    · exact ⟨edge, Or.inr head_vertex⟩
  have incident_star : xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∨
      xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge) := by
    rcases vertex_endpoint with tail_vertex | head_vertex
    · exact Or.inl (tail_vertex.symm ▸ vertex_star)
    · exact Or.inr (head_vertex.symm ▸ vertex_star)
  have ancestor_incident := xiIncidentStar_endpoint_has_incident_ancestor system coarse steps center edge incident_star
  have length_bound : ∀ colour, lengths colour ≤ xiRuleRadius system lengths := by
    intro colour
    have terminal_bound := xiRuleRadius_bound system lengths colour (system.plantMinus colour)
    have coordinate := congrFun eigenpair colour
    change (system.ruleNetwork colour).weightedDistance lengths
      (system.plantPlus colour) (system.plantMinus colour) = rate * lengths colour at coordinate
    rw [coordinate] at terminal_bound
    nlinarith [nonnegative colour]
  have coarse_bound : (XiNetwork system coarse).weightedDistance lengths center
      (XiTail system coarse (xiEdgeAncestor system coarse steps edge)) ≤ xiRuleRadius system lengths := by
    rcases ancestor_incident with tail_center | head_center
    · rw [← tail_center, (XiNetwork system coarse).weightedDistance_self nonnegative]
      exact radius_nonnegative
    · rw [← head_center, (XiNetwork system coarse).weightedDistance_symm
        (xiSimpleGraph_connected system rule_connected coarse) nonnegative]
      exact ((XiNetwork system coarse).weightedDistance_edge nonnegative _).trans (length_bound _)
  have old_trace := xiNetwork_forward_weightedDistance system rule_connected nonnegative coarse steps
    center (XiTail system coarse (xiEdgeAncestor system coarse steps edge))
  rw [system.metricLengths_iterate_eigenpair rule_connected rate_nonnegative eigenpair,
    (XiNetwork system coarse).weightedDistance_smul lengths (pow_nonneg rate_nonnegative _)] at old_trace
  have old_bound := old_trace.le.trans
    (mul_le_mul_of_nonneg_left coarse_bound (pow_nonneg rate_nonnegative steps))
  have endpoint_bounds := xiDescendant_endpoint_distance_bound system rule_connected nonnegative
    rate_ge_two eigenpair coarse steps edge
  have vertex_bound : (XiNetwork system (coarse + steps)).weightedDistance lengths
      (xiForward system coarse steps (XiTail system coarse (xiEdgeAncestor system coarse steps edge))) vertex ≤
        2 * xiRuleRadius system lengths * rate ^ steps - xiRuleRadius system lengths := by
    rcases vertex_endpoint with tail_vertex | head_vertex
    · simpa only [tail_vertex] using endpoint_bounds.1
    · simpa only [head_vertex] using endpoint_bounds.2
  have triangle := (XiNetwork system (coarse + steps)).weightedDistance_triangle
    (xiSimpleGraph_connected system rule_connected _) nonnegative (xiForward system coarse steps center)
    (xiForward system coarse steps (XiTail system coarse (xiEdgeAncestor system coarse steps edge))) vertex
  exact triangle.trans ((add_le_add old_bound vertex_bound).trans (by nlinarith))

theorem xiIncidentStar_subset_large_ball_of_eigenpair (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    {lengths : Fin K → ℝ} (lengths_positive : ∀ colour, 0 < lengths colour)
    {rate : ℝ} (rate_ge_two : 2 ≤ rate)
    (eigenpair : (system.ruleFamily rule_connected).metricLengths lengths = rate • lengths) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ coarse steps (center : XiVtx system coarse) (radius : ℝ),
      coefficient * rate ^ steps ≤ radius →
      ∀ vertex, xiIncidentStar system coarse center steps vertex →
        vertex ∈ finiteGraphBall (XiSimpleGraph system (coarse + steps))
          (xiForward system coarse steps center) radius := by
  classical
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  let lower := Finset.univ.inf' Finset.univ_nonempty lengths
  let upper := Finset.univ.sup' Finset.univ_nonempty lengths
  have lower_positive : 0 < lower := (Finset.lt_inf'_iff _).mpr (fun colour _ => lengths_positive colour)
  have upper_positive : 0 < upper := (lengths_positive system.initCol).trans_le
    (Finset.le_sup' lengths (Finset.mem_univ _))
  have rate_positive : 0 < rate := (by norm_num : (0 : ℝ) < 2).trans_le rate_ge_two
  have radius_positive : 0 < xiRuleRadius system lengths := by
    have coordinate := congrFun eigenpair system.initCol
    change (system.ruleNetwork system.initCol).weightedDistance lengths
      (system.plantPlus system.initCol) (system.plantMinus system.initCol) =
        rate * lengths system.initCol at coordinate
    have bound := xiRuleRadius_bound system lengths system.initCol (system.plantMinus system.initCol)
    rw [coordinate] at bound
    exact (mul_pos rate_positive (lengths_positive _)).trans_le bound
  refine ⟨4 * xiRuleRadius system lengths / lower, div_pos (by positivity) lower_positive,
    fun coarse steps center radius radius_bound vertex vertex_star => ?_⟩
  have metric_bound := xiIncidentStar_weightedDistance_bound system rule_connected
    (fun colour => (lengths_positive colour).le) rate_ge_two eigenpair coarse steps center vertex_star
  have graph_bound := ((XiNetwork system (coarse + steps)).weightedDistance_length_bounds
    (xiSimpleGraph_connected system rule_connected _) (xiNetwork_loopless system rule_connected rules_loopless _)
    lower_positive.le upper_positive.le (fun colour => Finset.inf'_le lengths (Finset.mem_univ colour))
    (fun colour => Finset.le_sup' lengths (Finset.mem_univ colour))
    (xiForward system coarse steps center) vertex).1
  change lower * ((XiSimpleGraph system (coarse + steps)).dist
    (xiForward system coarse steps center) vertex : ℝ) ≤ _ at graph_bound
  have scaled_radius := mul_le_mul_of_nonneg_left radius_bound lower_positive.le
  have cancellation : lower * (4 * xiRuleRadius system lengths / lower * rate ^ steps) =
      4 * xiRuleRadius system lengths * rate ^ steps := by field_simp
  rw [cancellation] at scaled_radius
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_contra not_inside
  have product_nonnegative := mul_nonneg lower_positive.le (sub_nonneg.mpr (le_of_not_gt not_inside))
  nlinarith [mul_pos radius_positive (pow_pos rate_positive steps)]

end EIGS

#print axioms EIGS.xiIncidentStar_weightedDistance_bound
#print axioms EIGS.xiIncidentStar_subset_large_ball_of_eigenpair
