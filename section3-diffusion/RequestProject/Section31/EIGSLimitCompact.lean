import RequestProject.Section31.EIGSMetricOfRules
import RequestProject.Section31.EIGSMetricCompactness

/-! Compactness of the actual path-metric limit under the original rules. -/

namespace EIGS

variable {K : ℕ} {system : EIGSData K}
    {ruleConnected : ∀ colour, (ruleSG system colour).Connected}

theorem XiPathMetricData.limit_compactSpace (parameters : XiPathMetricData system ruleConnected)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    CompactSpace parameters.LimitSpace := by
  have rateGreaterThanOne : 1 < system.distanceSpectralRadius ruleConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius ruleConnected rulesUnique plantingNonadjacent distancePositive)
  exact xiCompletion_compactSpace system ruleConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius ruleConnected) rateGreaterThanOne parameters.eigenpair

theorem xiLimitSpace_compactSpace_of_rules (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    CompactSpace (xiPathMetricDataOfRules system ruleConnected rulesLoopless rulesUnique distancePositive).LimitSpace :=
  XiPathMetricData.limit_compactSpace _ rulesUnique plantingNonadjacent distancePositive

end EIGS

#print axioms EIGS.XiPathMetricData.limit_compactSpace
#print axioms EIGS.xiLimitSpace_compactSpace_of_rules
