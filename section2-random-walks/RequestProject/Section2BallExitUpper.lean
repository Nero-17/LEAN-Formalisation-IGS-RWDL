import RequestProject.Section2StarExit
import RequestProject.Section2ForwardComposition

/-! The actual survival-series expected exit upper bound for original-unit
balls at arbitrary prescribed comparable spectral radii. -/

namespace EIGS

open scoped Classical

variable {K : ℕ}

theorem xiForward_ball_expExit_trans (system : EIGSData K) (initial first second : ℕ)
    (vertex : XiVtx system initial) (radius : ℝ) :
    expExit (XiSimpleGraph system ((initial + first) + second))
      (finiteGraphBall (XiSimpleGraph system ((initial + first) + second))
        (xiForward system (initial + first) second (xiForward system initial first vertex)) radius)
      (xiForward system (initial + first) second (xiForward system initial first vertex)) =
    expExit (XiSimpleGraph system (initial + (first + second)))
      (finiteGraphBall (XiSimpleGraph system (initial + (first + second)))
        (xiForward system initial (first + second) vertex) radius)
      (xiForward system initial (first + second) vertex) := by
  exact congrArg (fun point : Σ level, XiVtx system level =>
    expExit (XiSimpleGraph system point.1)
      (finiteGraphBall (XiSimpleGraph system point.1) point.2 radius) point.2)
    (xiForward_sigma_trans system initial first second vertex)

theorem xiSimpleGraph_small_ball_expExit_spectral_upper (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ coefficient upper : ℝ, 0 < coefficient ∧ 0 < upper ∧
      ∀ coarse depth (center : XiVtx system coarse) (radius : ℝ),
        0 < radius → radius ≤ coefficient * (system.distanceSpectralRadius rule_connected) ^ depth →
        expExit (XiSimpleGraph system (coarse + depth))
            (finiteGraphBall (XiSimpleGraph system (coarse + depth))
              (xiForward system coarse depth center) radius) (xiForward system coarse depth center) ≤
          upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rule_connected distance_positive) ^ depth := by
  obtain ⟨coefficient, coefficient_positive, containment⟩ :=
    xiSimpleGraph_ball_subset_multistep_star_at_distanceSpectralRadius system rule_connected
      rules_loopless rules_unique distance_positive
  obtain ⟨upper, upper_positive, star_bound⟩ :=
    xiIncidentStarDomain_expExit_spectral_upper system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  refine ⟨coefficient, upper, coefficient_positive, upper_positive,
    fun coarse depth center radius radius_positive radius_bound => ?_⟩
  apply le_trans _ (star_bound coarse depth center)
  apply expExit_mono_domain (xiSimpleGraph_connected system rule_connected _)
    _ (xiIncidentStarDomain_complement_nonempty system coarse depth center)
  intro vertex membership
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    containment coarse depth center radius radius_positive radius_bound vertex
      (Finset.mem_filter.mp membership).2⟩

theorem xiSimpleGraph_mesoscopic_ball_expExit_spectral_upper (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (radius_upper : ℝ) :
    ∃ buffer : ℕ, ∃ upper : ℝ, 0 < upper ∧
      ∀ initial_level (vertex : XiVtx system initial_level) age depth (radius : ℝ),
        buffer ≤ age → 0 < radius →
        radius ≤ radius_upper * (system.distanceSpectralRadius rule_connected) ^ depth →
        expExit (XiSimpleGraph system (initial_level + (age + depth)))
            (finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
              (xiForward system initial_level (age + depth) vertex) radius)
            (xiForward system initial_level (age + depth) vertex) ≤
          upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rule_connected distance_positive) ^ depth := by
  have distance_rate_gt_one : 1 < system.distanceSpectralRadius rule_connected := by
    have bound := system.two_le_distanceSpectralRadius rule_connected rules_unique
      planting_nonadjacent distance_positive
    linarith
  have distance_rate_positive := zero_lt_one.trans distance_rate_gt_one
  have time_rate_positive : 0 < realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rule_connected distance_positive :=
    mul_pos (eigs_mass_spectral_growth system rule_connected distance_positive).1
      (system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive).1
  obtain ⟨coefficient, original_upper, coefficient_positive, original_upper_positive, small_bound⟩ :=
    xiSimpleGraph_small_ball_expExit_spectral_upper system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  obtain ⟨buffer, buffer_bound⟩ :=
    pow_unbounded_of_one_lt (radius_upper / coefficient) distance_rate_gt_one
  have coefficient_bound : radius_upper ≤ coefficient *
      (system.distanceSpectralRadius rule_connected) ^ buffer :=
    ((div_lt_iff₀ coefficient_positive).mp buffer_bound).le.trans_eq (mul_comm _ _)
  refine ⟨buffer, original_upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
    system.resistanceSpectralRadius rule_connected distance_positive) ^ buffer, by positivity,
    fun initial_level vertex age depth radius age_buffer radius_positive radius_bound => ?_⟩
  have shifted_radius : radius ≤ coefficient *
      (system.distanceSpectralRadius rule_connected) ^ (buffer + depth) := by
    apply radius_bound.trans
    simpa only [mul_assoc, ← pow_add] using mul_le_mul_of_nonneg_right coefficient_bound
      (pow_nonneg distance_rate_positive.le depth)
  have shifted_bound := small_bound (initial_level + (age - buffer)) (buffer + depth)
    (xiForward system initial_level (age - buffer) vertex) radius radius_positive shifted_radius
  have level_identity : (age - buffer) + (buffer + depth) = age + depth := by omega
  rw [xiForward_ball_expExit_trans, level_identity] at shifted_bound
  exact shifted_bound.trans_eq (by rw [pow_add, mul_assoc])

end EIGS

#print axioms EIGS.xiForward_ball_expExit_trans
#print axioms EIGS.xiSimpleGraph_small_ball_expExit_spectral_upper
#print axioms EIGS.xiSimpleGraph_mesoscopic_ball_expExit_spectral_upper
