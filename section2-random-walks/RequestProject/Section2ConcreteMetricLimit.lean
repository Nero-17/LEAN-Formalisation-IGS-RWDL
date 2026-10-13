import RequestProject.Section2ConcreteMetric

/-! Actual Xi terminal graph distances have a positive normalized limit from
the original connected distance-positive rules. -/

namespace EIGS

open Filter Topology

variable {K : ℕ}

theorem xiSimpleGraph_terminal_distance_normalized_limit (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ rate limit : ℝ, 0 < rate ∧ 0 < limit ∧
      Tendsto (fun level =>
        ((XiSimpleGraph system level).dist (xiPositiveTerminal system level)
          (xiNegativeTerminal system level) : ℝ) / rate ^ level)
        atTop (nhds limit) := by
  let rules := system.connectedRuleSystem rule_connected
  let reachable := fun colour =>
    rule_connected colour (system.plantPlus colour) (system.plantMinus colour)
  have all_paths_use : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour := by
    intro ruleColour edgeColour
    exact ((system.ruleNetwork ruleColour).not_reachable_withoutColour_iff_every_path_uses_colour
      ((system.ruleNetwork ruleColour).colourConsistent_of_edgesUnique (rules_unique ruleColour))
      edgeColour _ _).mp (distance_positive ruleColour edgeColour)
  obtain ⟨rate, limit, vector, rate_positive, limit_positive, vector_positive,
    normalized, eigenpair, convergence⟩ := rules.pathRenormMap_normalized_iterate_limit
      (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt)
      reachable all_paths_use
  refine ⟨rate, limit * vector system.initCol, rate_positive,
    mul_pos limit_positive (vector_positive system.initCol), ?_⟩
  have coordinate_limit := tendsto_pi_nhds.mp convergence system.initCol
  convert coordinate_limit using 1
  ext level
  rw [xiSimpleGraph_terminal_distance_iterate system rule_connected rules_loopless rules_unique]

end EIGS

#print axioms EIGS.xiNetwork_weightedDistance_succ
#print axioms EIGS.xiNetwork_terminal_metric_iterate
#print axioms EIGS.EIGSData.metricLengths_eq_pathRenormMap
#print axioms EIGS.xiNetwork_terminal_path_metric_iterate
#print axioms EIGS.xiSimpleGraph_terminal_distance_iterate
#print axioms EIGS.xiSimpleGraph_terminal_distance_normalized_limit
