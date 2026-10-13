import RequestProject.Section2BallExitLower
import RequestProject.Section2ScaleLimits

/-! The actual walk-dimension limit along every admissible diverging radius
sequence at every vertex born at a finite level. The buffer and all exit-time
comparison constants are constructed from the original rules. -/

namespace EIGS

open Filter Topology
open scoped Classical

variable {K : ℕ}

theorem xiSimpleGraph_admissible_walk_dimension_limit (system : EIGSData K)
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
    ∃ buffer : ℕ, ∀ initial_level (vertex : XiVtx system initial_level)
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
  obtain ⟨buffer, lower, upper, lower_positive, upper_positive, exit_bounds⟩ :=
    xiSimpleGraph_mesoscopic_ball_expExit_spectral_bounds system rule_connected rules_loopless
      rules_unique planting_nonadjacent distance_positive radius_lower radius_upper radius_lower_positive
  refine ⟨buffer, fun initial_level vertex depth radius radius_tendsto admissible => ?_⟩
  have distance_rate_gt_one : 1 < system.distanceSpectralRadius rule_connected := by
    have bound := system.two_le_distanceSpectralRadius rule_connected rules_unique
      planting_nonadjacent distance_positive
    linarith
  have radius_growth : ∀ᶠ index in atTop,
      radius_lower * (system.distanceSpectralRadius rule_connected) ^ depth index ≤ radius index ∧
      radius index ≤ radius_upper * (system.distanceSpectralRadius rule_connected) ^ depth index :=
    admissible.mono (fun _ bounds => bounds.2)
  have depth_tendsto := geometric_depth_tendsto_of_radius_tendsto distance_rate_gt_one.le
    radius_upper_positive radius_tendsto (radius_growth.mono (fun _ bounds => bounds.2))
  apply logarithmic_ratio_limit_of_geometric_scale
    (mul_pos (eigs_mass_spectral_growth system rule_connected distance_positive).1
      (system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive).1)
    distance_rate_gt_one lower_positive upper_positive radius_lower_positive radius_upper_positive
    radius_tendsto _ radius_growth
  filter_upwards [admissible, depth_tendsto.eventually_ge_atTop buffer]
    with index bounds depth_large
  have depth_le : depth index ≤ index := by omega
  have age_large : buffer ≤ index - depth index := by omega
  have actual_bounds := exit_bounds initial_level vertex (index - depth index) (depth index)
    (radius index) age_large depth_large bounds.2.1 bounds.2.2
  rw [Nat.sub_add_cancel depth_le] at actual_bounds
  exact actual_bounds.2

end EIGS

#print axioms EIGS.xiSimpleGraph_admissible_walk_dimension_limit
