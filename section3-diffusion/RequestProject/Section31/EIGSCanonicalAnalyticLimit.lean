import RequestProject.Section31.EIGSActualL2Core
import RequestProject.Section31.EIGSUnitGromovHausdorff
import RequestProject.Section31.EIGSLimitCompact

/-! Rule-only entry points for the canonical metric limit and its native
varying L2 core. Every Perron vector, mass law and weak-limit input is derived
inside the construction from the explicit original graph assumptions. -/

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

theorem xiCanonicalMetric_gromovHausdorff_limit_of_rules :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    ∃ scale : ℝ, ∃ scalePositive : 0 < scale,
      Tendsto (xiUnitGHPoint system connected (system.distanceSpectralRadius connected)
        parameters.ratePositive scale scalePositive) atTop
        (nhds (xiWeightedLimitGHPoint system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair)) := by
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  exact xiSimpleGraph_gromovHausdorff_limit system connected loopless unique plantingNonadjacent
    distancePositive parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    rateGreaterThanOne parameters.normalized parameters.eigenpair

noncomputable def xiCanonicalLimitProbabilityMeasureOfRules :=
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let mass := xiMassParametersOfRules system connected distancePositive
  let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  xiLimitProbabilityMeasure system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass

noncomputable def xiCanonicalL2CoreOfRules :=
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let mass := xiMassParametersOfRules system connected distancePositive
  let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  xiSpeedL2Core system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass

end EIGS

#print axioms EIGS.xiCanonicalMetric_gromovHausdorff_limit_of_rules
#print axioms EIGS.xiCanonicalLimitProbabilityMeasureOfRules
#print axioms EIGS.xiCanonicalL2CoreOfRules
