import RequestProject.Section2MesoscopicResistance

/-! Actual fixed-radius resistance, including radii below the mesoscopic
depth-buffer range. The exact zero-depth star supplies the degree lower bound. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem xiSimpleGraph_ball_resistance_degree_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (level : ℕ) (center : XiVtx system level) (radius : ℝ) (radius_positive : 0 < radius)
    (proper : (finiteGraphBall (XiSimpleGraph system level) center radius)ᶜ.Nonempty) :
    1 / ((XiSimpleGraph system level).degree center : ℝ) ≤
      effResToBoundary (XiSimpleGraph system level)
        (finiteGraphBall (XiSimpleGraph system level) center radius) center := by
  have incident_count := (XiNetwork system level).incident_edge_count_eq_degree
    (xiNetwork_loopless system rule_connected rules_loopless level)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent level) center
  change (∑ edge : XiEdge system.toRuleData level,
    if XiTail system level edge = center ∨ XiHead system level edge = center then (1 : ℝ) else 0) =
      ((XiSimpleGraph system level).degree center : ℝ) at incident_count
  have zero_star_resistance :
      effResToBoundary (XiSimpleGraph system level) (xiIncidentStarDomain system level 0 center) center =
        ((XiSimpleGraph system level).degree center : ℝ)⁻¹ := by
    have formula := xiIncidentStarDomain_resistance_eq system rule_connected rules_loopless rules_unique
      planting_nonadjacent level 0 center
    simpa only [Function.iterate_zero_apply, inv_one, incident_count] using formula
  rw [one_div, ← zero_star_resistance]
  apply effResToBoundary_mono_domain (XiSimpleGraph system level)
    (xiSimpleGraph_connected system rule_connected level) _ proper
    (xiIncidentStarDomain_center_mem system level 0 center)
  intro vertex membership
  have same_center : vertex = center := by
    simpa only [xiIncidentStarDomain, Finset.mem_filter, Finset.mem_univ, true_and,
      xiIncidentStar] using membership
  subst vertex
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    by simpa only [SimpleGraph.dist_self, Nat.cast_zero] using radius_positive⟩

theorem xiSimpleGraph_fixed_radius_resistance_spectral_bounds (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitive_degree : (degreeMatrix system).IsPrimitive)
    (radius : ℝ) (radius_gt_one : 1 < radius) :
    ∃ threshold : ℕ, ∀ initial_level (vertex : XiVtx system initial_level),
      ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ age, threshold ≤ age →
        (finiteGraphBall (XiSimpleGraph system (initial_level + age))
          (xiForward system initial_level age vertex) radius)ᶜ.Nonempty ∧
        lower * (finiteRealMatrixSpectralRadius (degreeMatrix system))⁻¹ ^ age ≤
          effResToBoundary (XiSimpleGraph system (initial_level + age))
            (finiteGraphBall (XiSimpleGraph system (initial_level + age))
              (xiForward system initial_level age vertex) radius) (xiForward system initial_level age vertex) ∧
        effResToBoundary (XiSimpleGraph system (initial_level + age))
            (finiteGraphBall (XiSimpleGraph system (initial_level + age))
              (xiForward system initial_level age vertex) radius) (xiForward system initial_level age vertex) ≤
          upper * (finiteRealMatrixSpectralRadius (degreeMatrix system))⁻¹ ^ age := by
  have radius_positive := zero_lt_one.trans radius_gt_one
  have distance_rate_gt_one : 1 < system.distanceSpectralRadius rule_connected := by
    have bound := system.two_le_distanceSpectralRadius rule_connected rules_unique planting_nonadjacent distance_positive
    linarith
  have distance_rate_positive := zero_lt_one.trans distance_rate_gt_one
  have resistance_rate_positive :=
    (system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive).1
  obtain ⟨degree_rate_positive, degree_growth⟩ :=
    degree_spectral_growth_from_primitive_rules system rule_connected primitive_degree
  obtain ⟨upper_coefficient, resistance_upper, upper_coefficient_positive, resistance_upper_positive, upper_bound⟩ :=
    xiSimpleGraph_ball_resistance_spectral_upper system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  obtain ⟨proper_coefficient, proper_coefficient_positive, proper_bound⟩ :=
    xiSimpleGraph_ball_complement_nonempty_at_spectral_scale system rule_connected rules_loopless rules_unique distance_positive
  have coefficient_positive : 0 < min upper_coefficient proper_coefficient :=
    lt_min upper_coefficient_positive proper_coefficient_positive
  obtain ⟨threshold, threshold_bound⟩ :=
    pow_unbounded_of_one_lt (radius / min upper_coefficient proper_coefficient) distance_rate_gt_one
  have radius_bound : radius ≤ min upper_coefficient proper_coefficient *
      (system.distanceSpectralRadius rule_connected) ^ threshold :=
    ((div_lt_iff₀ coefficient_positive).mp threshold_bound).le.trans_eq (mul_comm _ _)
  refine ⟨threshold, fun initial_level vertex => ?_⟩
  obtain ⟨degree_lower, degree_upper, degree_lower_positive, degree_upper_positive, degree_bound⟩ :=
    degree_growth initial_level vertex
  refine ⟨1 / degree_upper,
    resistance_upper * (system.resistanceSpectralRadius rule_connected distance_positive) ^ threshold *
      finiteRealMatrixSpectralRadius (degreeMatrix system) ^ threshold / degree_lower,
    by positivity, by positivity, fun age age_threshold => ?_⟩
  have actual_degree_bound : ∀ steps,
      degree_lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps ≤
          ((XiSimpleGraph system (initial_level + steps)).degree (xiForward system initial_level steps vertex) : ℝ) ∧
      ((XiSimpleGraph system (initial_level + steps)).degree (xiForward system initial_level steps vertex) : ℝ) ≤
        degree_upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps := by
    intro steps
    rw [xiSimpleGraph_degree_eq_degree_state_sum system rule_connected rules_loopless rules_unique planting_nonadjacent]
    exact degree_bound steps
  have proper := proper_bound (initial_level + (age - threshold)) threshold
    (xiForward system initial_level (age - threshold) vertex) radius radius_positive
    (radius_bound.trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (pow_nonneg distance_rate_positive.le threshold)))
  rw [xiForward_ball_complement_trans, Nat.sub_add_cancel age_threshold] at proper
  refine ⟨proper, ?_, ?_⟩
  · have degree_comparison := one_div_le_one_div_of_le
      (xiSimpleGraph_degree_positive system rule_connected _ _) (actual_degree_bound age).2
    apply le_trans _ (degree_comparison.trans
      (xiSimpleGraph_ball_resistance_degree_lower system rule_connected rules_loopless rules_unique
        planting_nonadjacent (initial_level + age) (xiForward system initial_level age vertex)
        radius radius_positive proper))
    apply le_of_eq
    simp only [one_div, inv_pow, mul_inv_rev]
    ring
  · have actual_upper := upper_bound (initial_level + (age - threshold)) threshold
      (xiForward system initial_level (age - threshold) vertex) radius radius_positive
      (radius_bound.trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (pow_nonneg distance_rate_positive.le threshold)))
    rw [xiForward_ball_resistance_trans, Nat.sub_add_cancel age_threshold] at actual_upper
    have quotient_bound := div_le_div_of_nonneg_left
      (mul_nonneg resistance_upper_positive.le (pow_nonneg resistance_rate_positive.le threshold))
      (mul_pos degree_lower_positive (pow_pos degree_rate_positive (age - threshold)))
      (actual_degree_bound (age - threshold)).1
    apply (actual_upper.trans quotient_bound).trans_eq
    have power_decomposition : finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age =
        finiteRealMatrixSpectralRadius (degreeMatrix system) ^ (age - threshold) *
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ threshold := by
      rw [← pow_add, Nat.sub_add_cancel age_threshold]
    rw [inv_pow, power_decomposition]
    field_simp [ne_of_gt degree_lower_positive, ne_of_gt degree_rate_positive]
    <;> ring

end EIGS

#print axioms EIGS.xiSimpleGraph_ball_resistance_degree_lower
#print axioms EIGS.xiSimpleGraph_fixed_radius_resistance_spectral_bounds
