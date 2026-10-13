import RequestProject.Section2DescendantBall
import RequestProject.Section2StarSpectralVolume

/-! A finite geometric lower estimate: actual private vertices born in
descendants of coarse incident edges inject into actual sufficiently large balls. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem xiIncidentDescendant_cardinality (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) :
    Fintype.card {edge : XiEdge system.toRuleData (coarse + steps) //
      XiTail system coarse (xiEdgeAncestor system coarse steps edge) = center ∨
        XiHead system coarse (xiEdgeAncestor system coarse steps edge) = center} =
      ∑ ancestor : XiEdge system.toRuleData coarse,
        if XiTail system coarse ancestor = center ∨ XiHead system coarse ancestor = center then
          totalEdges {system.toRuleData with ι := XiCol system.toRuleData coarse ancestor} steps else 0 := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter]
  calc
    _ = ∑ edge : XiEdge system.toRuleData (coarse + steps),
        ∑ ancestor : XiEdge system.toRuleData coarse,
          if xiEdgeAncestor system coarse steps edge = ancestor then
            if XiTail system coarse ancestor = center ∨ XiHead system coarse ancestor = center then (1 : ℕ) else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro edge _
      simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ancestor _
      by_cases incident : XiTail system coarse ancestor = center ∨ XiHead system coarse ancestor = center
      · simp only [incident, ↓reduceIte]
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, totalEdges] using
          xiDescendant_weight_sum system coarse steps ancestor (fun _ => (1 : ℕ))
      · simp only [incident, ↓reduceIte, ite_self, Finset.sum_const_zero]

theorem Network.incident_edge_count_eq_degree (network : Network K)
    (loopless : network.Loopless) (unique_edges : network.EdgesUnique) (center : network.V) :
    (∑ edge : network.E, if network.tail edge = center ∨ network.head edge = center then (1 : ℝ) else 0) =
      (network.toSimpleGraph.degree center : ℝ) := by
  rw [network.degree_eq_incident_edge_sum loopless unique_edges]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases tail_center : network.tail edge = center <;>
    by_cases head_center : network.head edge = center
  · exact False.elim (loopless edge (tail_center.trans head_center.symm))
  all_goals simp [tail_center, head_center]

theorem xiReplanted_edge_card_spectral_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ colour steps,
      lower * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps ≤
        (totalEdges {system.toRuleData with ι := colour} steps : ℝ) := by
  classical
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  have per_colour : ∀ colour : Fin K, ∃ lower : ℝ, 0 < lower ∧ ∀ steps,
      lower * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps ≤
        (totalEdges {system.toRuleData with ι := colour} steps : ℝ) := by
    intro colour
    obtain ⟨_, lower, _, lower_positive, _, mass_bounds⟩ :=
      eigs_mass_spectral_growth {system with initCol := colour} rule_connected distance_positive
    exact ⟨lower, lower_positive, fun steps => (mass_bounds steps).1⟩
  choose colour_lower colour_lower_positive colour_bound using per_colour
  let lower := Finset.univ.inf' Finset.univ_nonempty colour_lower
  have rate_positive := (eigs_mass_spectral_growth system rule_connected distance_positive).1
  refine ⟨lower, (Finset.lt_inf'_iff _).mpr (fun colour _ => colour_lower_positive colour),
    fun colour steps => ?_⟩
  exact (mul_le_mul_of_nonneg_right (Finset.inf'_le colour_lower (Finset.mem_univ colour))
    (pow_nonneg rate_positive.le steps)).trans (colour_bound colour steps)

theorem xiSimpleGraph_large_ball_spectral_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ coefficient lower : ℝ, 0 < coefficient ∧ 0 < lower ∧
      ∀ coarse steps (center : XiVtx system coarse) (radius : ℝ),
        coefficient * (system.distanceSpectralRadius rule_connected) ^ (steps + 1) ≤ radius →
        lower * (XiSimpleGraph system coarse).degree center *
          realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps ≤
          ((finiteGraphBall (XiSimpleGraph system ((coarse + steps) + 1))
            (xiForward system coarse (steps + 1) center) radius).card : ℝ) := by
  classical
  obtain ⟨lengths, lengths_positive, _, _, eigenpair⟩ :=
    system.metricLengths_spectral_eigenpair rule_connected rules_loopless rules_unique distance_positive
  have rate_ge_two := system.two_le_distanceSpectralRadius rule_connected rules_unique
    planting_nonadjacent distance_positive
  obtain ⟨coefficient, coefficient_positive, containment⟩ :=
    xiSimpleGraph_private_descendants_in_ball_of_eigenpair system rule_connected rules_loopless
      lengths_positive rate_ge_two eigenpair
  obtain ⟨lower, lower_positive, mass_bounds⟩ :=
    xiReplanted_edge_card_spectral_lower system rule_connected distance_positive
  let interior_choice := fun colour => Classical.choice
    (rule_interior_nonempty system rule_connected planting_nonadjacent colour)
  refine ⟨coefficient, lower, coefficient_positive, lower_positive,
    fun coarse steps center radius radius_bound => ?_⟩
  let descendants := {edge : XiEdge system.toRuleData (coarse + steps) //
    XiTail system coarse (xiEdgeAncestor system coarse steps edge) = center ∨
      XiHead system coarse (xiEdgeAncestor system coarse steps edge) = center}
  let ball := finiteGraphBall (XiSimpleGraph system ((coarse + steps) + 1))
    (xiForward system coarse (steps + 1) center) radius
  let descendant_vertex : descendants → {vertex // vertex ∈ ball} := fun descendant =>
    ⟨Sum.inr ⟨descendant.val, interior_choice (XiCol system.toRuleData (coarse + steps) descendant.val)⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, containment coarse steps center descendant.val
        descendant.property _ radius radius_bound⟩⟩
  have injection : Function.Injective descendant_vertex := by
    intro first second same_vertex
    apply Subtype.ext
    exact congrArg Sigma.fst (Sum.inr.inj (congrArg Subtype.val same_vertex))
  have count_bound : Fintype.card descendants ≤ ball.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective descendant_vertex injection
  have incident_count := (XiNetwork system coarse).incident_edge_count_eq_degree
    (xiNetwork_loopless system rule_connected rules_loopless coarse)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent coarse) center
  change (∑ edge : XiEdge system.toRuleData coarse,
    if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then (1 : ℝ) else 0) =
      ((XiSimpleGraph system coarse).degree center : ℝ) at incident_count
  have count_lower : lower * ((XiSimpleGraph system coarse).degree center : ℝ) *
      realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps ≤ (Fintype.card descendants : ℝ) := by
    change _ ≤ (Fintype.card {edge : XiEdge system.toRuleData (coarse + steps) //
      XiTail system coarse (xiEdgeAncestor system coarse steps edge) = center ∨
        XiHead system coarse (xiEdgeAncestor system coarse steps edge) = center} : ℝ)
    rw [xiIncidentDescendant_cardinality, Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_zero]
    rw [← incident_count, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ancestor _
    by_cases incident : XiTail system coarse ancestor = center ∨ XiHead system coarse ancestor = center
    · simp only [incident, ↓reduceIte, mul_one]
      exact mass_bounds _ _
    · simp only [incident, ↓reduceIte, mul_zero, zero_mul, le_refl]
  exact count_lower.trans (Nat.cast_le.mpr count_bound)

end EIGS

#print axioms EIGS.xiIncidentDescendant_cardinality
#print axioms EIGS.Network.incident_edge_count_eq_degree
#print axioms EIGS.xiReplanted_edge_card_spectral_lower
#print axioms EIGS.xiSimpleGraph_large_ball_spectral_lower
