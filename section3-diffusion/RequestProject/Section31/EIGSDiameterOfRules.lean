import RequestProject.Section31.EIGSDiameterOriginal
import RequestProject.Section31.EIGSMetricOfRules

/-! Original-rule entry point for the actual diameter-normalized graphs. -/

namespace EIGS

open Filter Topology

variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

theorem xiCanonicalMetric_original_diameter_gromovHausdorff_limit_of_rules :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    Tendsto (xiOriginalDiameterGHPoint system connected) atTop
      (nhds (xiDiameterLimitGHPoint system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair)) := by
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  exact xiSimpleGraph_original_diameter_gromovHausdorff_limit system connected loopless unique plantingNonadjacent
    distancePositive parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    rateGreaterThanOne parameters.normalized parameters.eigenpair

end EIGS

#print axioms EIGS.xiCanonicalMetric_original_diameter_gromovHausdorff_limit_of_rules
