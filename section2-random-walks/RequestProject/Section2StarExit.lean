import RequestProject.Section2StarResistance
import RequestProject.Section2ExitComparison

/-! Actual incident-star degree volume and its survival-series exit upper bound.
The mass and resistance growth bounds are constructed from the actual rules. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem Network.volume_eq_endpoint_sum (network : Network K)
    (loopless : network.Loopless) (unique_edges : network.EdgesUnique)
    (domain : Finset network.V) :
    volume network.toSimpleGraph domain =
      ∑ edge : network.E, ((if network.tail edge ∈ domain then (1 : ℝ) else 0) +
        (if network.head edge ∈ domain then (1 : ℝ) else 0)) := by
  classical
  unfold volume
  simp_rw [network.degree_eq_incident_edge_sum loopless unique_edges]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq]

theorem xiReplanted_edge_card_spectral_upper (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ colour steps,
      (totalEdges {system.toRuleData with ι := colour} steps : ℝ) ≤
        upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps := by
  classical
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  have per_colour : ∀ colour : Fin K, ∃ upper : ℝ, 0 < upper ∧ ∀ steps,
      (totalEdges {system.toRuleData with ι := colour} steps : ℝ) ≤
        upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps := by
    intro colour
    obtain ⟨_, _, upper, _, upper_positive, mass_bounds⟩ :=
      eigs_mass_spectral_growth {system with initCol := colour} rule_connected distance_positive
    exact ⟨upper, upper_positive, fun steps => (mass_bounds steps).2⟩
  choose colour_upper colour_upper_positive colour_bound using per_colour
  let upper := Finset.univ.sup' Finset.univ_nonempty colour_upper
  have rate_positive := (eigs_mass_spectral_growth system rule_connected distance_positive).1
  refine ⟨upper, (colour_upper_positive system.initCol).trans_le
    (Finset.le_sup' colour_upper (Finset.mem_univ _)), fun colour steps => ?_⟩
  exact (colour_bound colour steps).trans
    (mul_le_mul_of_nonneg_right (Finset.le_sup' colour_upper (Finset.mem_univ colour))
      (pow_nonneg rate_positive.le steps))

theorem xiIncidentStarDomain_volume_spectral_upper (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps (center : XiVtx system coarse),
      volume (XiSimpleGraph system (coarse + steps))
          (xiIncidentStarDomain system coarse steps center) ≤
        upper * (XiSimpleGraph system coarse).degree center *
          realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps := by
  obtain ⟨mass_upper, mass_upper_positive, mass_bounds⟩ :=
    xiReplanted_edge_card_spectral_upper system rule_connected distance_positive
  refine ⟨2 * mass_upper, by positivity, fun coarse steps center => ?_⟩
  have volume_identity := (XiNetwork system (coarse + steps)).volume_eq_endpoint_sum
    (xiNetwork_loopless system rule_connected rules_loopless _)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent _)
    (xiIncidentStarDomain system coarse steps center)
  change volume (XiSimpleGraph system (coarse + steps)) _ =
    ∑ edge : XiEdge system.toRuleData (coarse + steps),
      ((if XiTail system (coarse + steps) edge ∈ xiIncidentStarDomain system coarse steps center then (1 : ℝ) else 0) +
        (if XiHead system (coarse + steps) edge ∈ xiIncidentStarDomain system coarse steps center then (1 : ℝ) else 0))
    at volume_identity
  rw [volume_identity]
  have endpoint_bound :
      (∑ edge : XiEdge system.toRuleData (coarse + steps),
        ((if XiTail system (coarse + steps) edge ∈ xiIncidentStarDomain system coarse steps center then (1 : ℝ) else 0) +
          (if XiHead system (coarse + steps) edge ∈ xiIncidentStarDomain system coarse steps center then (1 : ℝ) else 0))) ≤
      2 * (Fintype.card {edge : XiEdge system.toRuleData (coarse + steps) //
        XiTail system coarse (xiEdgeAncestor system coarse steps edge) = center ∨
          XiHead system coarse (xiEdgeAncestor system coarse steps edge) = center} : ℝ) := by
    rw [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro edge _
    by_cases tail_inside : XiTail system (coarse + steps) edge ∈ xiIncidentStarDomain system coarse steps center
    · have incident := xiIncidentStar_endpoint_has_incident_ancestor system coarse steps center edge
        (Or.inl (Finset.mem_filter.mp tail_inside).2)
      simp only [tail_inside, incident, ↓reduceIte, mul_one]
      split <;> norm_num
    · by_cases head_inside : XiHead system (coarse + steps) edge ∈ xiIncidentStarDomain system coarse steps center
      · have incident := xiIncidentStar_endpoint_has_incident_ancestor system coarse steps center edge
          (Or.inr (Finset.mem_filter.mp head_inside).2)
        simp only [tail_inside, head_inside, incident, ↓reduceIte, mul_one]
        norm_num
      · simp only [tail_inside, head_inside, ↓reduceIte, zero_add]
        split <;> norm_num
  apply endpoint_bound.trans
  rw [xiIncidentDescendant_cardinality, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_zero]
  have incident_count := (XiNetwork system coarse).incident_edge_count_eq_degree
    (xiNetwork_loopless system rule_connected rules_loopless coarse)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent coarse) center
  change (∑ edge : XiEdge system.toRuleData coarse,
    if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then (1 : ℝ) else 0) =
      ((XiSimpleGraph system coarse).degree center : ℝ) at incident_count
  calc
    _ ≤ 2 * ∑ edge : XiEdge system.toRuleData coarse,
        if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
          mass_upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro edge _
      split
      · exact mass_bounds _ _
      · rfl
    _ = _ := by
      rw [← incident_count]
      simp only [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro edge _
      split <;> simp <;> ring

theorem xiIncidentStarDomain_expExit_spectral_upper (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps (center : XiVtx system coarse),
      expExit (XiSimpleGraph system (coarse + steps))
          (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) ≤
        upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rule_connected distance_positive) ^ steps := by
  obtain ⟨volume_upper, volume_upper_positive, volume_bound⟩ :=
    xiIncidentStarDomain_volume_spectral_upper system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  obtain ⟨_, resistance_upper, _, resistance_upper_positive, resistance_bounds⟩ :=
    xiIncidentStarDomain_resistance_spectral_bounds system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  refine ⟨resistance_upper * volume_upper, by positivity, fun coarse steps center => ?_⟩
  have proper := xiIncidentStarDomain_complement_nonempty system coarse steps center
  have connected := xiSimpleGraph_connected system rule_connected (coarse + steps)
  have exit_bound := exit_le_volume_mul_resistance (XiSimpleGraph system (coarse + steps)) connected proper
    (exitSystem_expExit connected proper) (xiIncidentStarDomain_center_mem system coarse steps center)
  have resistance_positive := effResToBoundary_pos (XiSimpleGraph system (coarse + steps)) connected proper
    (xiIncidentStarDomain_center_mem system coarse steps center)
  have mass_rate_positive := (eigs_mass_spectral_growth system rule_connected distance_positive).1
  apply exit_bound.trans
  apply (mul_le_mul (resistance_bounds coarse steps center).2 (volume_bound coarse steps center)
    (by unfold volume; positivity)
    (resistance_positive.le.trans (resistance_bounds coarse steps center).2)).trans_eq
  rw [mul_pow]
  have degree_positive := xiSimpleGraph_degree_positive system rule_connected coarse center
  field_simp [ne_of_gt degree_positive]
  <;> ring

end EIGS

#print axioms EIGS.Network.volume_eq_endpoint_sum
#print axioms EIGS.xiReplanted_edge_card_spectral_upper
#print axioms EIGS.xiIncidentStarDomain_volume_spectral_upper
#print axioms EIGS.xiIncidentStarDomain_expExit_spectral_upper
