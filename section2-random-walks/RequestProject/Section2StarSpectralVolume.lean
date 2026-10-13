import RequestProject.Section2StarVolume
import RequestProject.Section2MultiStepSpectralBall
import RequestProject.Section2SpectralGrowth

/-! Actual mesoscopic volume upper bounds from original rule data. The
coarse-degree factor and the mass spectral scale are derived, not assumed. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem xiReplanted_vertex_card_spectral_upper (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ colour steps,
      (Fintype.card (XiVtx {system with initCol := colour} steps) : ℝ) ≤
        upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps := by
  classical
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  have per_colour : ∀ colour : Fin K, ∃ upper : ℝ, 0 < upper ∧ ∀ steps,
      (Fintype.card (XiVtx {system with initCol := colour} steps) : ℝ) ≤
        upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps := by
    intro colour
    obtain ⟨rate_positive, lower, upper, lower_positive, upper_positive, mass_bounds⟩ :=
      eigs_mass_spectral_growth {system with initCol := colour} rule_connected distance_positive
    refine ⟨2 * upper, by positivity, fun steps => ?_⟩
    have vertex_bound := (xiSimpleGraph_connected {system with initCol := colour}
      rule_connected steps).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      at vertex_bound
    have labelled_bound := vertex_bound.trans (Nat.add_le_add_right
      ((XiNetwork {system with initCol := colour} steps).simpleGraph_edge_card_le) 1)
    have mass_positive : 0 < (totalEdges {system.toRuleData with ι := colour} steps : ℝ) :=
      lt_of_lt_of_le (mul_pos lower_positive (pow_pos rate_positive steps)) (mass_bounds steps).1
    have mass_at_least_one : (1 : ℝ) ≤ totalEdges {system.toRuleData with ι := colour} steps := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp mass_positive.ne')
    have labelled_bound_real :
        (Fintype.card (XiVtx {system with initCol := colour} steps) : ℝ) ≤
          (totalEdges {system.toRuleData with ι := colour} steps : ℝ) + 1 := by
      exact_mod_cast labelled_bound
    change (Fintype.card (XiVtx {system with initCol := colour} steps) : ℝ) ≤
      2 * upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps
    have mass_upper : (totalEdges {system.toRuleData with ι := colour} steps : ℝ) ≤
        upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps :=
      (mass_bounds steps).2
    nlinarith
  choose colour_upper colour_upper_positive colour_bound using per_colour
  let upper := Finset.univ.sup' Finset.univ_nonempty colour_upper
  have rate_positive := (eigs_mass_spectral_growth system rule_connected distance_positive).1
  refine ⟨upper, (colour_upper_positive system.initCol).trans_le
    (Finset.le_sup' colour_upper (Finset.mem_univ _)), fun colour steps => ?_⟩
  exact (colour_bound colour steps).trans (mul_le_mul_of_nonneg_right
    (Finset.le_sup' colour_upper (Finset.mem_univ colour)) (pow_nonneg rate_positive.le steps))

theorem xiIncidentStar_card_le_degree_mul_mass_spectral_scale (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps (center : XiVtx system coarse),
      ((Finset.univ.filter (xiIncidentStar system coarse center steps)).card : ℝ) ≤
        upper * (XiSimpleGraph system coarse).degree center *
          realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps := by
  obtain ⟨upper, upper_positive, vertex_bounds⟩ :=
    xiReplanted_vertex_card_spectral_upper system rule_connected distance_positive
  refine ⟨2 * upper, by positivity, fun coarse steps center => ?_⟩
  have loopless := xiNetwork_loopless system rule_connected rules_loopless coarse
  have incident_count :
      (∑ edge : XiEdge system.toRuleData coarse,
        if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then (1 : ℝ) else 0) =
      ((XiSimpleGraph system coarse).degree center : ℝ) := by
    have degree_expression := (XiNetwork system coarse).degree_eq_incident_edge_sum loopless
      (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent coarse) center
    change ((XiSimpleGraph system coarse).degree center : ℝ) = _ at degree_expression
    rw [degree_expression]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases tail_center : XiTail system coarse edge = center <;>
      by_cases head_center : XiHead system coarse edge = center
    · exact False.elim (loopless edge (tail_center.trans head_center.symm))
    all_goals simp [XiNetwork, tail_center, head_center]
  have star_bound :
      ((Finset.univ.filter (xiIncidentStar system coarse center steps)).card : ℝ) ≤
        1 + ((XiSimpleGraph system coarse).degree center : ℝ) *
          (upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps) := by
    have finite_bound := xiIncidentStar_card_le_replanted_vertices system coarse steps center
    have cast_bound :
        ((Finset.univ.filter (xiIncidentStar system coarse center steps)).card : ℝ) ≤
        1 + ∑ edge : XiEdge system.toRuleData coarse,
          if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
            (Fintype.card (XiVtx {system with initCol := XiCol system.toRuleData coarse edge} steps) : ℝ)
          else 0 := by exact_mod_cast finite_bound
    apply cast_bound.trans
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ edge : XiEdge system.toRuleData coarse,
          if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
            upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps else 0 := by
        apply Finset.sum_le_sum
        intro edge _
        by_cases incident : XiTail system coarse edge = center ∨ XiHead system coarse edge = center
        · simp only [incident, ↓reduceIte]
          exact vertex_bounds _ _
        · simp only [incident, ↓reduceIte, le_refl]
      _ = _ := by
        rw [← incident_count, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro edge _
        by_cases incident : XiTail system coarse edge = center ∨ XiHead system coarse edge = center
        <;> simp [incident]
  letI : Nontrivial (XiVtx system coarse) :=
    ⟨⟨xiPositiveTerminal system coarse, xiNegativeTerminal system coarse, xiTerminals_distinct system coarse⟩⟩
  obtain ⟨neighbor, adjacency⟩ :=
    (xiSimpleGraph_connected system rule_connected coarse).preconnected.exists_adj_of_nontrivial center
  have degree_at_least_one : (1 : ℝ) ≤ (XiSimpleGraph system coarse).degree center := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt ((XiSimpleGraph system coarse).degree_pos_iff_exists_adj center |>.mpr ⟨neighbor, adjacency⟩))
  have vertex_at_least_two : (2 : ℝ) ≤ Fintype.card (XiVtx system steps) := by
    rw [xiVtx_card_eq_two_add_interior_births, Nat.cast_add, Nat.cast_ofNat]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have scale_at_least_two : 2 ≤ upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps :=
    vertex_at_least_two.trans (vertex_bounds system.initCol steps)
  have product_at_least_one : 1 ≤ ((XiSimpleGraph system coarse).degree center : ℝ) *
      (upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps) := by
    nlinarith
  nlinarith [star_bound]

theorem xiSimpleGraph_mesoscopic_ball_spectral_upper (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ coefficient upper : ℝ, 0 < coefficient ∧ 0 < upper ∧
      ∀ coarse steps (center : XiVtx system coarse) (radius : ℝ),
        0 < radius → radius ≤ coefficient * (system.distanceSpectralRadius rule_connected) ^ steps →
        ((finiteGraphBall (XiSimpleGraph system (coarse + steps))
          (xiForward system coarse steps center) radius).card : ℝ) ≤
          upper * (XiSimpleGraph system coarse).degree center *
            realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ steps := by
  obtain ⟨coefficient, coefficient_positive, containment⟩ :=
    xiSimpleGraph_ball_subset_multistep_star_at_distanceSpectralRadius system rule_connected
      rules_loopless rules_unique distance_positive
  obtain ⟨upper, upper_positive, star_bounds⟩ :=
    xiIncidentStar_card_le_degree_mul_mass_spectral_scale system rule_connected rules_loopless
      rules_unique planting_nonadjacent distance_positive
  refine ⟨coefficient, upper, coefficient_positive, upper_positive,
    fun coarse steps center radius radius_positive radius_bound => ?_⟩
  have finite_containment : finiteGraphBall (XiSimpleGraph system (coarse + steps))
      (xiForward system coarse steps center) radius ⊆
      Finset.univ.filter (xiIncidentStar system coarse center steps) := by
    intro vertex membership
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      containment coarse steps center radius radius_positive radius_bound vertex
        (Finset.mem_filter.mp membership).2⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card finite_containment)).trans (star_bounds coarse steps center)

end EIGS

#print axioms EIGS.xiReplanted_vertex_card_spectral_upper
#print axioms EIGS.xiIncidentStar_card_le_degree_mul_mass_spectral_scale
#print axioms EIGS.xiSimpleGraph_mesoscopic_ball_spectral_upper
