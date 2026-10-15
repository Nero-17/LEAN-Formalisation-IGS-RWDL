import RequestProject.Section2WalkDimension
import RequestProject.Section2SpectralScaleInequality

/-! The actual finite-graph admissible mean-exit limit has exponent at least
2, from the original rules and the proved mass-resistance-distance inequality.
No exit-time limit, exponent or Einstein comparison is assumed. Candidate. -/

namespace EIGS
open Filter Topology
open scoped Classical
variable {K : ℕ}

theorem xiSimpleGraph_admissible_walk_dimension_limit_ge_two (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (radius_lower radius_upper : ℝ) (radius_lower_positive : 0 < radius_lower)
    (radius_upper_positive : 0 < radius_upper) :
    ∃ buffer : ℕ, 2 ≤ Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rule_connected distance_positive) /
      Real.log (system.distanceSpectralRadius rule_connected) ∧ ∀ initial_level (vertex : XiVtx system initial_level)
      (depth : ℕ → ℕ) (radius : ℕ → ℝ),
      Tendsto radius atTop atTop →
      (∀ᶠ index in atTop, depth index + buffer ≤ index ∧
        radius_lower * (system.distanceSpectralRadius rule_connected) ^ depth index ≤ radius index ∧
        radius index ≤ radius_upper * (system.distanceSpectralRadius rule_connected) ^ depth index) →
      Tendsto (fun index =>
        Real.log (expExit (XiSimpleGraph system (initial_level + index))
          (finiteGraphBall (XiSimpleGraph system (initial_level + index))
            (xiForward system initial_level index vertex) (radius index))
          (xiForward system initial_level index vertex)) / Real.log (radius index)) atTop
        (nhds (Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rule_connected distance_positive) /
          Real.log (system.distanceSpectralRadius rule_connected))) := by
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rule_connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rule_connected rules_unique planting_nonadjacent distance_positive)
  have rateBound := system.distanceSpectralRadius_sq_le_mass_mul_resistance
    rule_connected rules_loopless rules_unique distance_positive
  have logarithmBound := Real.log_le_log
    (sq_pos_of_pos (zero_lt_one.trans distanceGreaterThanOne)) rateBound
  rw [Real.log_pow] at logarithmBound
  have walkLower : 2 ≤ Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rule_connected distance_positive) /
      Real.log (system.distanceSpectralRadius rule_connected) := by
    apply (le_div_iff₀ (Real.log_pos distanceGreaterThanOne)).mpr
    simpa only [Nat.cast_ofNat] using logarithmBound
  obtain ⟨buffer, actualLimit⟩ := xiSimpleGraph_admissible_walk_dimension_limit system rule_connected
    rules_loopless rules_unique planting_nonadjacent distance_positive radius_lower radius_upper
    radius_lower_positive radius_upper_positive
  exact ⟨buffer, walkLower, actualLimit⟩

end EIGS

#print axioms EIGS.xiSimpleGraph_admissible_walk_dimension_limit_ge_two
