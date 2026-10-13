import RequestProject.Section2StarExitLower
import RequestProject.Section2BallExitUpper
import RequestProject.Section2MesoscopicResistance

/-! Lower exit bounds for actual comparable-radius balls, using contained
incident stars and monotonicity of the actual survival-series expectation. -/

namespace EIGS

open scoped Classical

variable {K : ℕ}

theorem xiSimpleGraph_large_ball_expExit_spectral_lower (system : EIGSData K)
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
        0 < steps → coefficient * (system.distanceSpectralRadius rule_connected) ^ steps ≤ radius →
        (finiteGraphBall (XiSimpleGraph system (coarse + steps))
          (xiForward system coarse steps center) radius)ᶜ.Nonempty →
        lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rule_connected distance_positive) ^ steps ≤
        expExit (XiSimpleGraph system (coarse + steps))
          (finiteGraphBall (XiSimpleGraph system (coarse + steps))
            (xiForward system coarse steps center) radius) (xiForward system coarse steps center) := by
  obtain ⟨lengths, lengths_positive, _, _, eigenpair⟩ :=
    system.metricLengths_spectral_eigenpair rule_connected rules_loopless rules_unique distance_positive
  obtain ⟨coefficient, coefficient_positive, containment⟩ :=
    xiIncidentStar_subset_large_ball_of_eigenpair system rule_connected rules_loopless lengths_positive
      (system.two_le_distanceSpectralRadius rule_connected rules_unique planting_nonadjacent distance_positive) eigenpair
  obtain ⟨lower, lower_positive, lower_bound⟩ :=
    xiIncidentStarDomain_expExit_successor_spectral_lower system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  refine ⟨coefficient, lower, coefficient_positive, lower_positive,
    fun coarse steps center radius steps_positive radius_bound proper => ?_⟩
  have star_lower := lower_bound coarse (steps - 1) center
  have steps_identity : 1 + (steps - 1) = steps := by omega
  rw [steps_identity] at star_lower
  apply star_lower.trans
  apply expExit_mono_domain (xiSimpleGraph_connected system rule_connected _) _ proper
  intro vertex membership
  exact containment coarse steps center radius radius_bound vertex (Finset.mem_filter.mp membership).2

theorem xiSimpleGraph_mesoscopic_ball_expExit_spectral_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (radius_lower : ℝ) (radius_lower_positive : 0 < radius_lower) :
    ∃ buffer : ℕ, ∃ lower : ℝ, 0 < lower ∧
      ∀ initial_level (vertex : XiVtx system initial_level) age depth (radius : ℝ),
        buffer ≤ depth → radius_lower * (system.distanceSpectralRadius rule_connected) ^ depth ≤ radius →
        (finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
          (xiForward system initial_level (age + depth) vertex) radius)ᶜ.Nonempty →
        lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rule_connected distance_positive) ^ depth ≤
        expExit (XiSimpleGraph system (initial_level + (age + depth)))
          (finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
            (xiForward system initial_level (age + depth) vertex) radius)
          (xiForward system initial_level (age + depth) vertex) := by
  have distance_rate_gt_one : 1 < system.distanceSpectralRadius rule_connected := by
    have bound := system.two_le_distanceSpectralRadius rule_connected rules_unique planting_nonadjacent distance_positive
    linarith
  have distance_rate_positive := zero_lt_one.trans distance_rate_gt_one
  have time_rate_positive : 0 < realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rule_connected distance_positive :=
    mul_pos (eigs_mass_spectral_growth system rule_connected distance_positive).1
      (system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive).1
  obtain ⟨coefficient, original_lower, coefficient_positive, original_lower_positive, large_bound⟩ :=
    xiSimpleGraph_large_ball_expExit_spectral_lower system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  obtain ⟨shift, shift_bound⟩ := pow_unbounded_of_one_lt (coefficient / radius_lower) distance_rate_gt_one
  have coefficient_bound : coefficient ≤ radius_lower * (system.distanceSpectralRadius rule_connected) ^ shift :=
    ((div_lt_iff₀ radius_lower_positive).mp shift_bound).le.trans_eq (mul_comm _ _)
  refine ⟨shift + 1, original_lower / (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
    system.resistanceSpectralRadius rule_connected distance_positive) ^ shift, by positivity,
    fun initial_level vertex age depth radius depth_buffer radius_bound proper => ?_⟩
  have shift_le_depth : shift ≤ depth := by omega
  have shifted_radius : coefficient * (system.distanceSpectralRadius rule_connected) ^ (depth - shift) ≤ radius := by
    apply le_trans (mul_le_mul_of_nonneg_right coefficient_bound (pow_nonneg distance_rate_positive.le _))
    simpa only [mul_assoc, ← pow_add, Nat.add_sub_of_le shift_le_depth] using radius_bound
  have level_identity : (age + shift) + (depth - shift) = age + depth := by omega
  have shifted_proper : (finiteGraphBall
      (XiSimpleGraph system ((initial_level + (age + shift)) + (depth - shift)))
      (xiForward system (initial_level + (age + shift)) (depth - shift)
        (xiForward system initial_level (age + shift) vertex)) radius)ᶜ.Nonempty := by
    rw [xiForward_ball_complement_trans, level_identity]
    exact proper
  have actual_lower := large_bound (initial_level + (age + shift)) (depth - shift)
    (xiForward system initial_level (age + shift) vertex) radius (by omega) shifted_radius shifted_proper
  rw [xiForward_ball_expExit_trans, level_identity] at actual_lower
  apply le_trans _ actual_lower
  apply le_of_eq
  have power_decomposition :
      (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rule_connected distance_positive) ^ depth =
      (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rule_connected distance_positive) ^ shift *
      (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rule_connected distance_positive) ^ (depth - shift) := by
    rw [← pow_add, Nat.add_sub_of_le shift_le_depth]
  rw [power_decomposition]
  field_simp [ne_of_gt (pow_pos time_rate_positive shift)]

theorem xiSimpleGraph_mesoscopic_ball_expExit_spectral_bounds (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (radius_lower radius_upper : ℝ) (radius_lower_positive : 0 < radius_lower) :
    ∃ buffer : ℕ, ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ initial_level (vertex : XiVtx system initial_level) age depth (radius : ℝ),
        buffer ≤ age → buffer ≤ depth →
        radius_lower * (system.distanceSpectralRadius rule_connected) ^ depth ≤ radius →
        radius ≤ radius_upper * (system.distanceSpectralRadius rule_connected) ^ depth →
        (finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
          (xiForward system initial_level (age + depth) vertex) radius)ᶜ.Nonempty ∧
        lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rule_connected distance_positive) ^ depth ≤
          expExit (XiSimpleGraph system (initial_level + (age + depth)))
            (finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
              (xiForward system initial_level (age + depth) vertex) radius)
            (xiForward system initial_level (age + depth) vertex) ∧
        expExit (XiSimpleGraph system (initial_level + (age + depth)))
            (finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
              (xiForward system initial_level (age + depth) vertex) radius)
            (xiForward system initial_level (age + depth) vertex) ≤
          upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rule_connected distance_positive) ^ depth := by
  have distance_rate_gt_one : 1 < system.distanceSpectralRadius rule_connected := by
    have bound := system.two_le_distanceSpectralRadius rule_connected rules_unique planting_nonadjacent distance_positive
    linarith
  have distance_rate_positive := zero_lt_one.trans distance_rate_gt_one
  obtain ⟨upper_buffer, upper, upper_positive, upper_bound⟩ :=
    xiSimpleGraph_mesoscopic_ball_expExit_spectral_upper system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive radius_upper
  obtain ⟨lower_buffer, lower, lower_positive, lower_bound⟩ :=
    xiSimpleGraph_mesoscopic_ball_expExit_spectral_lower system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive radius_lower radius_lower_positive
  obtain ⟨coefficient, coefficient_positive, proper_bound⟩ :=
    xiSimpleGraph_ball_complement_nonempty_at_spectral_scale system rule_connected rules_loopless rules_unique distance_positive
  obtain ⟨proper_buffer, proper_buffer_bound⟩ :=
    pow_unbounded_of_one_lt (radius_upper / coefficient) distance_rate_gt_one
  have coefficient_bound : radius_upper ≤ coefficient *
      (system.distanceSpectralRadius rule_connected) ^ proper_buffer :=
    ((div_lt_iff₀ coefficient_positive).mp proper_buffer_bound).le.trans_eq (mul_comm _ _)
  refine ⟨max proper_buffer (max lower_buffer upper_buffer), lower, upper, lower_positive, upper_positive,
    fun initial_level vertex age depth radius age_buffer depth_buffer radius_lower_bound radius_upper_bound => ?_⟩
  have age_proper : proper_buffer ≤ age := (le_max_left _ _).trans age_buffer
  have age_upper : upper_buffer ≤ age := (le_max_right _ _).trans ((le_max_right _ _).trans age_buffer)
  have depth_lower : lower_buffer ≤ depth := (le_max_left _ _).trans ((le_max_right _ _).trans depth_buffer)
  have radius_positive : 0 < radius :=
    (mul_pos radius_lower_positive (pow_pos distance_rate_positive depth)).trans_le radius_lower_bound
  have shifted_radius : radius ≤ coefficient *
      (system.distanceSpectralRadius rule_connected) ^ (proper_buffer + depth) := by
    apply radius_upper_bound.trans
    simpa only [mul_assoc, ← pow_add] using mul_le_mul_of_nonneg_right coefficient_bound
      (pow_nonneg distance_rate_positive.le depth)
  have proper := proper_bound (initial_level + (age - proper_buffer)) (proper_buffer + depth)
    (xiForward system initial_level (age - proper_buffer) vertex) radius radius_positive shifted_radius
  have level_identity : (age - proper_buffer) + (proper_buffer + depth) = age + depth := by omega
  rw [xiForward_ball_complement_trans, level_identity] at proper
  exact ⟨proper, lower_bound initial_level vertex age depth radius depth_lower radius_lower_bound proper,
    upper_bound initial_level vertex age depth radius age_upper radius_positive radius_upper_bound⟩

end EIGS

#print axioms EIGS.xiSimpleGraph_large_ball_expExit_spectral_lower
#print axioms EIGS.xiSimpleGraph_mesoscopic_ball_expExit_spectral_lower
#print axioms EIGS.xiSimpleGraph_mesoscopic_ball_expExit_spectral_bounds
