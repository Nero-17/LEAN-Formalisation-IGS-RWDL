import RequestProject.Section2StarResistance
import RequestProject.Section2MesoscopicVolume

/-! The two-sided resistance of actual original-unit balls in the full
birth-dependent mesoscopic range. Properness follows from actual geometry. -/

namespace EIGS

open scoped Classical

variable {K : ℕ}

theorem xiForward_ball_resistance_trans (system : EIGSData K) (initial first second : ℕ)
    (vertex : XiVtx system initial) (radius : ℝ) :
    effResToBoundary (XiSimpleGraph system ((initial + first) + second))
      (finiteGraphBall (XiSimpleGraph system ((initial + first) + second))
        (xiForward system (initial + first) second (xiForward system initial first vertex)) radius)
      (xiForward system (initial + first) second (xiForward system initial first vertex)) =
    effResToBoundary (XiSimpleGraph system (initial + (first + second)))
      (finiteGraphBall (XiSimpleGraph system (initial + (first + second)))
        (xiForward system initial (first + second) vertex) radius)
      (xiForward system initial (first + second) vertex) := by
  exact congrArg (fun point : Σ level, XiVtx system level =>
    effResToBoundary (XiSimpleGraph system point.1)
      (finiteGraphBall (XiSimpleGraph system point.1) point.2 radius) point.2)
    (xiForward_sigma_trans system initial first second vertex)

theorem xiForward_ball_complement_trans (system : EIGSData K) (initial first second : ℕ)
    (vertex : XiVtx system initial) (radius : ℝ) :
    (finiteGraphBall (XiSimpleGraph system ((initial + first) + second))
      (xiForward system (initial + first) second (xiForward system initial first vertex)) radius)ᶜ.Nonempty ↔
    (finiteGraphBall (XiSimpleGraph system (initial + (first + second)))
      (xiForward system initial (first + second) vertex) radius)ᶜ.Nonempty := by
  exact congrArg (fun point : Σ level, XiVtx system level =>
    (finiteGraphBall (XiSimpleGraph system point.1) point.2 radius)ᶜ.Nonempty)
    (xiForward_sigma_trans system initial first second vertex) |>.to_iff

theorem xiSimpleGraph_ball_complement_nonempty_at_spectral_scale (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ coarse steps (center : XiVtx system coarse) (radius : ℝ),
      0 < radius → radius ≤ coefficient * (system.distanceSpectralRadius rule_connected) ^ steps →
      (finiteGraphBall (XiSimpleGraph system (coarse + steps))
        (xiForward system coarse steps center) radius)ᶜ.Nonempty := by
  obtain ⟨coefficient, coefficient_positive, containment⟩ :=
    xiSimpleGraph_ball_subset_multistep_star_at_distanceSpectralRadius system rule_connected rules_loopless
      rules_unique distance_positive
  refine ⟨coefficient, coefficient_positive, fun coarse steps center radius radius_positive radius_bound => ?_⟩
  obtain ⟨vertex, vertex_outside⟩ := xiCoarseGroundedDomain_complement_nonempty system coarse steps center
  refine ⟨vertex, Finset.mem_compl.mpr (fun vertex_inside => ?_)⟩
  exact (Finset.mem_compl.mp vertex_outside)
    (xiIncidentStar_subset_coarseGroundedDomain system coarse steps center
      (containment coarse steps center radius radius_positive radius_bound vertex
        (Finset.mem_filter.mp vertex_inside).2))

theorem xiSimpleGraph_mesoscopic_ball_birth_spectral_resistance (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitive_degree : (degreeMatrix system).IsPrimitive)
    (radius_lower radius_upper : ℝ) (radius_lower_positive : 0 < radius_lower)
    (radius_upper_positive : 0 < radius_upper) :
    ∃ buffer : ℕ, ∀ initial_level (vertex : XiVtx system initial_level),
      ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ age depth (radius : ℝ),
        buffer ≤ age → buffer ≤ depth → 1 < radius →
        radius_lower * (system.distanceSpectralRadius rule_connected) ^ depth ≤ radius →
        radius ≤ radius_upper * (system.distanceSpectralRadius rule_connected) ^ depth →
        (finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
          (xiForward system initial_level (age + depth) vertex) radius)ᶜ.Nonempty ∧
        lower * (system.resistanceSpectralRadius rule_connected distance_positive) ^ depth /
            finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age ≤
          effResToBoundary (XiSimpleGraph system (initial_level + (age + depth)))
            (finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
              (xiForward system initial_level (age + depth) vertex) radius)
            (xiForward system initial_level (age + depth) vertex) ∧
        effResToBoundary (XiSimpleGraph system (initial_level + (age + depth)))
            (finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
              (xiForward system initial_level (age + depth) vertex) radius)
            (xiForward system initial_level (age + depth) vertex) ≤
          upper * (system.resistanceSpectralRadius rule_connected distance_positive) ^ depth /
            finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age := by
  have distance_rate_gt_one : 1 < system.distanceSpectralRadius rule_connected := by
    have bound := system.two_le_distanceSpectralRadius rule_connected rules_unique planting_nonadjacent distance_positive
    linarith
  have distance_rate_positive := zero_lt_one.trans distance_rate_gt_one
  have resistance_rate_positive := (system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive).1
  obtain ⟨degree_rate_positive, degree_growth⟩ :=
    degree_spectral_growth_from_primitive_rules system rule_connected primitive_degree
  obtain ⟨proper_coefficient, proper_coefficient_positive, proper_bound⟩ :=
    xiSimpleGraph_ball_complement_nonempty_at_spectral_scale system rule_connected rules_loopless rules_unique distance_positive
  obtain ⟨upper_coefficient, original_upper, upper_coefficient_positive, original_upper_positive, upper_bound⟩ :=
    xiSimpleGraph_ball_resistance_spectral_upper system rule_connected rules_loopless rules_unique planting_nonadjacent distance_positive
  obtain ⟨lower_coefficient, original_lower, lower_coefficient_positive, original_lower_positive, lower_bound⟩ :=
    xiSimpleGraph_large_ball_resistance_spectral_lower system rule_connected rules_loopless rules_unique planting_nonadjacent distance_positive
  let small_coefficient := min proper_coefficient upper_coefficient
  have small_coefficient_positive : 0 < small_coefficient := lt_min proper_coefficient_positive upper_coefficient_positive
  obtain ⟨upper_shift, upper_shift_bound⟩ :=
    pow_unbounded_of_one_lt (radius_upper / small_coefficient) distance_rate_gt_one
  have upper_coefficient_bound : radius_upper ≤ small_coefficient *
      (system.distanceSpectralRadius rule_connected) ^ upper_shift := by
    exact ((div_lt_iff₀ small_coefficient_positive).mp upper_shift_bound).le.trans_eq (mul_comm _ _)
  obtain ⟨lower_shift, lower_shift_bound⟩ :=
    pow_unbounded_of_one_lt (lower_coefficient / radius_lower) distance_rate_gt_one
  have lower_coefficient_bound : lower_coefficient ≤ radius_lower *
      (system.distanceSpectralRadius rule_connected) ^ lower_shift := by
    exact ((div_lt_iff₀ radius_lower_positive).mp lower_shift_bound).le.trans_eq (mul_comm _ _)
  refine ⟨max upper_shift lower_shift, fun initial_level vertex => ?_⟩
  obtain ⟨degree_lower, degree_upper, degree_lower_positive, degree_upper_positive, degree_bound⟩ :=
    degree_growth initial_level vertex
  let birth_lower := original_lower /
    (degree_upper * (system.resistanceSpectralRadius rule_connected distance_positive) ^ lower_shift *
      finiteRealMatrixSpectralRadius (degreeMatrix system) ^ lower_shift)
  let birth_upper := original_upper *
    (system.resistanceSpectralRadius rule_connected distance_positive) ^ upper_shift *
      finiteRealMatrixSpectralRadius (degreeMatrix system) ^ upper_shift / degree_lower
  refine ⟨birth_lower, birth_upper, by positivity, by positivity,
    fun age depth radius age_buffer depth_buffer radius_gt_one radius_lower_bound radius_upper_bound => ?_⟩
  have age_upper_shift : upper_shift ≤ age := (le_max_left _ _).trans age_buffer
  have depth_lower_shift : lower_shift ≤ depth := (le_max_right _ _).trans depth_buffer
  have actual_degree_bound : ∀ steps,
      degree_lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps ≤
          ((XiSimpleGraph system (initial_level + steps)).degree (xiForward system initial_level steps vertex) : ℝ) ∧
      ((XiSimpleGraph system (initial_level + steps)).degree (xiForward system initial_level steps vertex) : ℝ) ≤
        degree_upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps := by
    intro steps
    rw [xiSimpleGraph_degree_eq_degree_state_sum system rule_connected rules_loopless rules_unique planting_nonadjacent]
    exact degree_bound steps
  have upper_radius_bound : radius ≤ small_coefficient *
      (system.distanceSpectralRadius rule_connected) ^ (upper_shift + depth) := by
    apply radius_upper_bound.trans
    simpa only [mul_assoc, ← pow_add] using mul_le_mul_of_nonneg_right upper_coefficient_bound
      (pow_nonneg distance_rate_positive.le depth)
  have upper_level_identity : (age - upper_shift) + (upper_shift + depth) = age + depth := by omega
  have proper : (finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
      (xiForward system initial_level (age + depth) vertex) radius)ᶜ.Nonempty := by
    have shifted_proper := proper_bound (initial_level + (age - upper_shift)) (upper_shift + depth)
      (xiForward system initial_level (age - upper_shift) vertex) radius (zero_lt_one.trans radius_gt_one)
      (upper_radius_bound.trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (pow_nonneg distance_rate_positive.le _)))
    rw [xiForward_ball_complement_trans, upper_level_identity] at shifted_proper
    exact shifted_proper
  refine ⟨proper, ?_, ?_⟩
  · have lower_radius_bound : lower_coefficient *
        (system.distanceSpectralRadius rule_connected) ^ (depth - lower_shift) ≤ radius := by
      apply le_trans (mul_le_mul_of_nonneg_right lower_coefficient_bound
        (pow_nonneg distance_rate_positive.le _))
      simpa only [mul_assoc, ← pow_add, Nat.add_sub_of_le depth_lower_shift] using radius_lower_bound
    have lower_level_identity : (age + lower_shift) + (depth - lower_shift) = age + depth := by omega
    have shifted_proper : (finiteGraphBall
        (XiSimpleGraph system ((initial_level + (age + lower_shift)) + (depth - lower_shift)))
        (xiForward system (initial_level + (age + lower_shift)) (depth - lower_shift)
          (xiForward system initial_level (age + lower_shift) vertex)) radius)ᶜ.Nonempty := by
      rw [xiForward_ball_complement_trans, lower_level_identity]
      exact proper
    have actual_lower := lower_bound (initial_level + (age + lower_shift)) (depth - lower_shift)
      (xiForward system initial_level (age + lower_shift) vertex) radius lower_radius_bound shifted_proper
    rw [xiForward_ball_resistance_trans, lower_level_identity] at actual_lower
    have quotient_bound := div_le_div_of_nonneg_left
      (mul_nonneg original_lower_positive.le (pow_nonneg resistance_rate_positive.le (depth - lower_shift)))
      (xiSimpleGraph_degree_positive system rule_connected _ _)
      (actual_degree_bound (age + lower_shift)).2
    apply le_trans _ (quotient_bound.trans actual_lower)
    apply le_of_eq
    have resistance_decomposition : (system.resistanceSpectralRadius rule_connected distance_positive) ^ depth =
        (system.resistanceSpectralRadius rule_connected distance_positive) ^ lower_shift *
          (system.resistanceSpectralRadius rule_connected distance_positive) ^ (depth - lower_shift) := by
      rw [← pow_add, Nat.add_sub_of_le depth_lower_shift]
    dsimp [birth_lower]
    rw [resistance_decomposition, pow_add]
    field_simp [ne_of_gt degree_rate_positive, ne_of_gt resistance_rate_positive, ne_of_gt degree_upper_positive]
    <;> ring
  · have actual_upper := upper_bound (initial_level + (age - upper_shift)) (upper_shift + depth)
      (xiForward system initial_level (age - upper_shift) vertex) radius (zero_lt_one.trans radius_gt_one)
      (upper_radius_bound.trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (pow_nonneg distance_rate_positive.le _)))
    rw [xiForward_ball_resistance_trans, upper_level_identity] at actual_upper
    have quotient_bound := div_le_div_of_nonneg_left
      (mul_nonneg original_upper_positive.le (pow_nonneg resistance_rate_positive.le (upper_shift + depth)))
      (mul_pos degree_lower_positive (pow_pos degree_rate_positive (age - upper_shift)))
      (actual_degree_bound (age - upper_shift)).1
    apply (actual_upper.trans quotient_bound).trans_eq
    have degree_decomposition : finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age =
        finiteRealMatrixSpectralRadius (degreeMatrix system) ^ (age - upper_shift) *
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ upper_shift := by
      rw [← pow_add, Nat.sub_add_cancel age_upper_shift]
    dsimp [birth_upper]
    rw [degree_decomposition, pow_add]
    field_simp [ne_of_gt degree_rate_positive, ne_of_gt resistance_rate_positive, ne_of_gt degree_lower_positive]
    <;> ring

end EIGS

#print axioms EIGS.xiForward_ball_resistance_trans
#print axioms EIGS.xiForward_ball_complement_trans
#print axioms EIGS.xiSimpleGraph_ball_complement_nonempty_at_spectral_scale
#print axioms EIGS.xiSimpleGraph_mesoscopic_ball_birth_spectral_resistance
