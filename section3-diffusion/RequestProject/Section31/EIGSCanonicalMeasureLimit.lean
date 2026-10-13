import RequestProject.Section31.EIGSCanonicalAnalyticLimit
import RequestProject.Section31.EIGSVertexWeakLimit
import RequestProject.Section31.EIGSSpeedDegree
import RequestProject.Section31.EIGSAddressSupport

/-! Rule-only measure limits. The metric Perron data and the actual compatible
edge-address mass parameters are chosen internally from the original rules.
Both empirical laws retain every original discretization index. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped ENNReal Classical

variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

noncomputable def xiCanonicalVertexProbabilityMeasureOfRules (level : ℕ) :=
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  xiVertexProbabilityMeasure system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair level

noncomputable def xiCanonicalSpeedProbabilityMeasureOfRules (level : ℕ) :=
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let mass := xiMassParametersOfRules system connected distancePositive
  let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  xiSpeedProbabilityMeasure system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass level

theorem xiCanonicalVertexProbabilityMeasure_tendsto_of_rules :
    Tendsto (xiCanonicalVertexProbabilityMeasureOfRules system connected loopless unique
      plantingNonadjacent distancePositive) atTop
      (nhds (xiCanonicalLimitProbabilityMeasureOfRules system connected loopless unique
        plantingNonadjacent distancePositive)) := by
  dsimp [xiCanonicalVertexProbabilityMeasureOfRules, xiCanonicalLimitProbabilityMeasureOfRules]
  exact xiVertexProbabilityMeasure_tendsto system connected plantingNonadjacent distancePositive
    _ _ _ _ _ (xiMassParametersOfRules system connected distancePositive)

theorem xiCanonicalSpeedProbabilityMeasure_tendsto_of_rules :
    Tendsto (xiCanonicalSpeedProbabilityMeasureOfRules system connected loopless unique
      plantingNonadjacent distancePositive) atTop
      (nhds (xiCanonicalLimitProbabilityMeasureOfRules system connected loopless unique
        plantingNonadjacent distancePositive)) := by
  dsimp [xiCanonicalSpeedProbabilityMeasureOfRules, xiCanonicalLimitProbabilityMeasureOfRules]
  exact xiSpeedProbabilityMeasure_tendsto system connected _ _ _ _ _
    (xiMassParametersOfRules system connected distancePositive)

theorem xiCanonicalVertex_and_speed_same_limit_of_rules :
    Tendsto (xiCanonicalVertexProbabilityMeasureOfRules system connected loopless unique
      plantingNonadjacent distancePositive) atTop
      (nhds (xiCanonicalLimitProbabilityMeasureOfRules system connected loopless unique
        plantingNonadjacent distancePositive)) ∧
    Tendsto (xiCanonicalSpeedProbabilityMeasureOfRules system connected loopless unique
      plantingNonadjacent distancePositive) atTop
      (nhds (xiCanonicalLimitProbabilityMeasureOfRules system connected loopless unique
        plantingNonadjacent distancePositive)) :=
  ⟨xiCanonicalVertexProbabilityMeasure_tendsto_of_rules system connected loopless unique
      plantingNonadjacent distancePositive,
    xiCanonicalSpeedProbabilityMeasure_tendsto_of_rules system connected loopless unique
      plantingNonadjacent distancePositive⟩

include loopless unique plantingNonadjacent

theorem xiCanonicalNativeSpeed_singleton_degree_of_rules (level : ℕ) (vertex : XiVtx system level) :
    xiVertexSpeedMeasure system (xiMassParametersOfRules system connected distancePositive) level {vertex} =
      ((XiSimpleGraph system level).degree vertex : ℝ≥0∞) /
        (2 * (totalEdges system.toRuleData level : ℝ≥0∞)) := by
  classical
  exact xiVertexSpeedMeasure_singleton_degree system connected loopless unique plantingNonadjacent
    (xiMassParametersOfRules system connected distancePositive) level vertex

instance xiCanonicalLimitProbabilityMeasure_isOpenPosMeasure_of_rules :
    (xiCanonicalLimitProbabilityMeasureOfRules system connected loopless unique
      plantingNonadjacent distancePositive).toMeasure.IsOpenPosMeasure := by
  dsimp [xiCanonicalLimitProbabilityMeasureOfRules, xiLimitProbabilityMeasure]
  infer_instance

end EIGS

#print axioms EIGS.xiCanonicalVertexProbabilityMeasure_tendsto_of_rules
#print axioms EIGS.xiCanonicalSpeedProbabilityMeasure_tendsto_of_rules
#print axioms EIGS.xiCanonicalVertex_and_speed_same_limit_of_rules
#print axioms EIGS.xiCanonicalNativeSpeed_singleton_degree_of_rules
#print axioms EIGS.xiCanonicalLimitProbabilityMeasure_isOpenPosMeasure_of_rules