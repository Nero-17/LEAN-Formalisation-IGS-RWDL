import RequestProject.Section2WalkDimension
import RequestProject.Section31.EIGSActualTerminalResistanceDimension
import RequestProject.Section31.EIGSCoveringNumberDimensionOfRules
import RequestProject.Section31.EIGSAnalyticTimeScale

/-! The Einstein identity for three actual quantities: the logarithmic
exit-time limit at every finite-born vertex and every admissible scale,
the standard covering-number logarithmic limit of the completion, and
the actual simple-graph terminal resistance dimension. Every scaling
input is supplied by the original rules. -/

namespace EIGS
noncomputable section
open Filter Topology IGS.Sec31
open scoped Classical
set_option maxHeartbeats 4000000
variable {K : ℕ}

theorem xiSimpleGraph_actual_Einstein_relation_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (radiusLower radiusUpper : ℝ) (radiusLowerPositive : 0 < radiusLower)
    (radiusUpperPositive : 0 < radiusUpper) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    ∃ buffer : ℕ, ∀ birth (vertex : XiVtx system birth) (depth : ℕ → ℕ) (radius : ℕ → ℝ),
      Tendsto radius atTop atTop →
      (∀ᶠ index in atTop, depth index + buffer ≤ index ∧
        radiusLower * (system.distanceSpectralRadius connected) ^ depth index ≤ radius index ∧
        radius index ≤ radiusUpper * (system.distanceSpectralRadius connected) ^ depth index) →
      limUnder atTop (fun index =>
        Real.log (expExit (XiSimpleGraph system (birth + index))
          (finiteGraphBall (XiSimpleGraph system (birth + index))
            (xiForward system birth index vertex) (radius index))
          (xiForward system birth index vertex)) / Real.log (radius index)) =
      limUnder (𝓝[>] (0 : ℝ)) (fun coverRadius : ℝ =>
        Real.log (realCoveringNumber parameters.LimitSpace coverRadius) / (-Real.log coverRadius)) +
      resistanceDimension
        (fun level => effResToBoundary (XiSimpleGraph system level)
          (Finset.univ.erase (xiNegativeTerminal system level)) (xiPositiveTerminal system level))
        (fun level => ((XiSimpleGraph system level).dist (xiPositiveTerminal system level)
          (xiNegativeTerminal system level) : ℝ)) := by
  intro parameters
  obtain ⟨buffer, walkLimit⟩ := xiSimpleGraph_admissible_walk_dimension_limit system connected loopless unique
    plantingNonadjacent distancePositive radiusLower radiusUpper radiusLowerPositive radiusUpperPositive
  refine ⟨buffer, ?_⟩
  intro birth vertex depth radius radiusDiverges admissible
  rw [(walkLimit birth vertex depth radius radiusDiverges admissible).limUnder_eq,
    (xiCompletion_coveringNumber_dimension_of_rules system connected loopless unique plantingNonadjacent
      distancePositive primitiveDegree).limUnder_eq,
    xiSimpleGraph_terminal_resistanceDimension_eq system connected loopless unique plantingNonadjacent distancePositive,
    XiMassParameters.rate_eq_spectralRadius system (xiMassParametersOfRules system connected distancePositive)]
  rw [Real.log_mul
    (eigs_mass_spectral_growth system connected distancePositive).1.ne'
    (system.resistanceSpectralRadius_positive_eigenpair connected distancePositive).1.ne', add_div]

end
end EIGS

#print axioms EIGS.xiSimpleGraph_actual_Einstein_relation_of_rules

