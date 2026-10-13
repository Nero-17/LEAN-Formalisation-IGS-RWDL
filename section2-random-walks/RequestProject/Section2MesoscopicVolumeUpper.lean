import RequestProject.Section2StarSpectralVolume

/-! The upper half of the original birth-dependent mesoscopic volume
estimate, with both actual matrix spectral radii and actual graph balls. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem xiSimpleGraph_mesoscopic_ball_birth_spectral_upper (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitive_degree : (degreeMatrix system).IsPrimitive) :
    ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ initial_level (vertex : XiVtx system initial_level),
        ∃ upper : ℝ, 0 < upper ∧ ∀ age depth (radius : ℝ),
          0 < radius → radius ≤ coefficient * (system.distanceSpectralRadius rule_connected) ^ depth →
          ((finiteGraphBall (XiSimpleGraph system ((initial_level + age) + depth))
            (xiForward system (initial_level + age) depth
              (xiForward system initial_level age vertex)) radius).card : ℝ) ≤
            upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
              realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ depth := by
  obtain ⟨coefficient, volume_upper, coefficient_positive, volume_upper_positive, volume_bound⟩ :=
    xiSimpleGraph_mesoscopic_ball_spectral_upper system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  obtain ⟨_, degree_growth⟩ := degree_spectral_growth_from_primitive_rules system rule_connected primitive_degree
  have mass_rate_positive := (eigs_mass_spectral_growth system rule_connected distance_positive).1
  refine ⟨coefficient, coefficient_positive, fun initial_level vertex => ?_⟩
  obtain ⟨_, degree_upper, _, degree_upper_positive, degree_bound⟩ := degree_growth initial_level vertex
  refine ⟨volume_upper * degree_upper, mul_pos volume_upper_positive degree_upper_positive,
    fun age depth radius radius_positive radius_bound => ?_⟩
  have actual_degree_bound := (degree_bound age).2
  rw [← xiSimpleGraph_degree_eq_degree_state_sum system rule_connected rules_loopless rules_unique
    planting_nonadjacent] at actual_degree_bound
  have scaled_degree_bound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left actual_degree_bound volume_upper_positive.le)
    (pow_nonneg mass_rate_positive.le depth)
  apply (volume_bound (initial_level + age) depth (xiForward system initial_level age vertex)
    radius radius_positive radius_bound).trans
  simpa only [mul_assoc] using scaled_degree_bound

end EIGS

#print axioms EIGS.xiSimpleGraph_mesoscopic_ball_birth_spectral_upper
