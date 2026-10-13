import RequestProject.Section2WeightedSubstitution

/-! A concrete barrier around the old center in an actual substituted network.
Before reaching a different old vertex, a sufficiently small weighted ball can
only enter private copies attached to an incident coarse edge. -/

namespace EIGS.Network

open scoped BigOperators Classical

variable {K : ℕ} (network : Network K) (rules : RuleFamily K)

def IncidentCopyVertex (center : network.V) : (network.subst rules).V → Prop
  | Sum.inl vertex => vertex = center
  | Sum.inr ⟨edge, _⟩ => network.tail edge = center ∨ network.head edge = center

theorem weightedDistance_subst_ge_radius_outside_incident_copies
    (substituted_connected : (network.subst rules).toSimpleGraph.Connected)
    (rules_connected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    {radius : ℝ} (radius_nonnegative : 0 ≤ radius)
    (rule_distance_bound : ∀ colour, radius ≤ rules.metricLengths lengths colour)
    (center : network.V) (vertex : (network.subst rules).V)
    (outside : ¬ network.IncidentCopyVertex rules center vertex) :
    radius ≤ (network.subst rules).weightedDistance lengths (Sum.inl center) vertex := by
  let potential : network.V → ℝ := fun vertex => if vertex = center then 0 else radius
  have lipschitz : network.EdgeLipschitz (rules.metricLengths lengths) potential := by
    intro edge
    by_cases tail_center : network.tail edge = center <;>
      by_cases head_center : network.head edge = center <;>
      simp only [potential, tail_center, head_center, ↓reduceIte, sub_self, abs_zero,
        zero_sub, abs_neg, sub_zero, abs_of_nonneg radius_nonnegative] <;>
      first | exact rule_distance_bound _ | exact radius_nonnegative.trans (rule_distance_bound _)
  have extended_lipschitz := network.substMetricPotential_lipschitz rules rules_connected
    nonnegative potential lipschitz
  have potential_bound : radius ≤ network.substMetricPotential rules lengths potential vertex := by
    cases vertex with
    | inl old_vertex =>
      have different : old_vertex ≠ center := outside
      simp only [substMetricPotential, potential, different, ↓reduceIte, le_refl]
    | inr private_vertex =>
      obtain ⟨edge, interior⟩ := private_vertex
      have not_incident : network.tail edge ≠ center ∧ network.head edge ≠ center := by
        simpa only [IncidentCopyVertex, not_or] using outside
      simp only [substMetricPotential, potential, not_incident.1, not_incident.2, ↓reduceIte]
      exact le_min (le_add_of_nonneg_right ((rules.R (network.color edge)).weightedDistance_nonnegative
        (rules_connected (network.color edge)) nonnegative (rules.βplus (network.color edge)) interior.val))
        (le_add_of_nonneg_right ((rules.R (network.color edge)).weightedDistance_nonnegative
          (rules_connected (network.color edge)) nonnegative (rules.βminus (network.color edge)) interior.val))
  have distance_bound := (network.subst rules).potential_difference_le_weightedDistance
    substituted_connected extended_lipschitz (Sum.inl center) vertex
  simp only [substMetricPotential, potential, ↓reduceIte, zero_sub, abs_neg] at distance_bound
  exact potential_bound.trans ((le_abs_self _).trans distance_bound)

theorem weighted_ball_subset_incident_copies
    (substituted_connected : (network.subst rules).toSimpleGraph.Connected)
    (rules_connected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    {radius : ℝ} (radius_nonnegative : 0 ≤ radius)
    (rule_distance_bound : ∀ colour, radius ≤ rules.metricLengths lengths colour)
    (center : network.V) (vertex : (network.subst rules).V)
    (in_ball : (network.subst rules).weightedDistance lengths (Sum.inl center) vertex < radius) :
    network.IncidentCopyVertex rules center vertex := by
  by_contra outside
  exact (not_lt_of_ge (network.weightedDistance_subst_ge_radius_outside_incident_copies rules
    substituted_connected rules_connected nonnegative radius_nonnegative rule_distance_bound
    center vertex outside)) in_ball

theorem weighted_ball_card_le_incident_copies
    (substituted_connected : (network.subst rules).toSimpleGraph.Connected)
    (rules_connected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    {radius : ℝ} (radius_nonnegative : 0 ≤ radius)
    (rule_distance_bound : ∀ colour, radius ≤ rules.metricLengths lengths colour)
    (center : network.V) :
    (Finset.univ.filter (fun vertex : (network.subst rules).V =>
      (network.subst rules).weightedDistance lengths (Sum.inl center) vertex < radius)).card ≤
      1 + ∑ edge : network.E, if network.tail edge = center ∨ network.head edge = center
        then Fintype.card (network.SubstInner rules edge) else 0 := by
  have containment :
      Finset.univ.filter (fun vertex : (network.subst rules).V =>
        (network.subst rules).weightedDistance lengths (Sum.inl center) vertex < radius) ⊆
      Finset.univ.filter (network.IncidentCopyVertex rules center) := by
    intro vertex membership
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      network.weighted_ball_subset_incident_copies rules substituted_connected rules_connected
        nonnegative radius_nonnegative rule_distance_bound center vertex
        (Finset.mem_filter.mp membership).2⟩
  apply (Finset.card_le_card containment).trans_eq
  simp only [Finset.card_filter]
  change (∑ vertex : network.V ⊕ (Σ edge : network.E, network.SubstInner rules edge),
    if network.IncidentCopyVertex rules center vertex then (1 : ℕ) else 0) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [IncidentCopyVertex]
  apply congrArg₂ Nat.add
  · rw [Finset.sum_eq_single center]
    · simp
    · intro old_vertex _ different
      simp [different]
    · simp
  · apply Finset.sum_congr rfl
    intro edge _
    by_cases incident : network.tail edge = center ∨ network.head edge = center <;> simp [incident]

end EIGS.Network

#print axioms EIGS.Network.weighted_ball_subset_incident_copies
