import RequestProject.Section2ConcreteSimplicity
import RequestProject.Section2WeightedPathIdentity

/-! Actual Xi terminal metric iteration and identification with the rule-path
renormalisation, under the explicit chosen-orientation convention. -/

namespace EIGS

variable {K : ℕ}

theorem Network.singleEdge_weightedDistance (colour : Fin K)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) :
    (Network.singleEdge colour).weightedDistance lengths false true = lengths colour := by
  let walk : (Network.singleEdge colour).EdgeWalk false true :=
    Network.EdgeWalk.cons (network := Network.singleEdge colour) () (Or.inl ⟨rfl, rfl⟩)
      (Network.EdgeWalk.nil (network := Network.singleEdge colour) true)
  letI : Nonempty ((Network.singleEdge colour).EdgeWalk false true) := ⟨walk⟩
  apply le_antisymm
  · simpa only [walk, Network.EdgeWalk.cost, Network.singleEdge, add_zero] using
      (Network.singleEdge colour).weightedDistance_le_cost nonnegative walk
  · apply le_ciInf
    intro candidate
    have lipschitz : (Network.singleEdge colour).EdgeLipschitz lengths
        (fun vertex : Bool => if vertex then lengths colour else 0) := by
      intro edge
      simp [Network.singleEdge, abs_of_nonneg (nonnegative colour)]
    have bound := Network.EdgeWalk.potential_difference_le_cost (Network.singleEdge colour)
      lipschitz candidate
    simpa only [Bool.false_eq_true, ↓reduceIte, zero_sub, abs_neg,
      abs_of_nonneg (nonnegative colour)] using bound

theorem xiNetwork_weightedDistance_succ (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (level : ℕ)
    (source sink : XiVtx system level) :
    (XiNetwork system (level + 1)).weightedDistance lengths (Sum.inl source) (Sum.inl sink) =
      (XiNetwork system level).weightedDistance
        ((system.ruleFamily rule_connected).metricLengths lengths) source sink := by
  calc
    _ = ((XiNetwork system level).subst (system.ruleFamily rule_connected)).weightedDistance
        lengths (Sum.inl source) (Sum.inl sink) := by
      congr 1
      exact xiNetwork_succ system rule_connected level
    _ = _ := (XiNetwork system level).weightedDistance_subst
      (system.ruleFamily rule_connected) (xiSimpleGraph_connected system rule_connected level)
      rule_connected nonnegative source sink

theorem xiNetwork_terminal_metric_iterate (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (level : ℕ) :
    (XiNetwork system level).weightedDistance lengths
      (xiPositiveTerminal system level) (xiNegativeTerminal system level) =
        ((system.ruleFamily rule_connected).metricLengths^[level] lengths) system.initCol := by
  induction level generalizing lengths with
  | zero => exact Network.singleEdge_weightedDistance system.initCol nonnegative
  | succ level induction_hypothesis =>
    change (XiNetwork system (level + 1)).weightedDistance lengths
      (Sum.inl (xiPositiveTerminal system level)) (Sum.inl (xiNegativeTerminal system level)) = _
    rw [xiNetwork_weightedDistance_succ system rule_connected nonnegative]
    rw [induction_hypothesis (Network.metricLengths_nonnegative
      (system.ruleFamily rule_connected) rule_connected nonnegative)]
    rw [Function.iterate_succ_apply]

theorem EIGSData.metricLengths_eq_pathRenormMap (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) :
    (system.ruleFamily rule_connected).metricLengths lengths =
      ((system.connectedRuleSystem rule_connected).pathRenormMap
        (fun colour => rule_connected colour (system.plantPlus colour) (system.plantMinus colour))).apply
          lengths := by
  ext colour
  exact ((system.ruleNetwork colour).path_eval_eq_weightedDistance
    (rules_loopless colour) (rules_unique colour) _ _
    (rule_connected colour (system.plantPlus colour) (system.plantMinus colour)) nonnegative).symm

theorem xiNetwork_terminal_path_metric_iterate (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (level : ℕ) :
    (XiNetwork system level).weightedDistance lengths
      (xiPositiveTerminal system level) (xiNegativeTerminal system level) =
      (((system.connectedRuleSystem rule_connected).pathRenormMap
        (fun colour => rule_connected colour (system.plantPlus colour) (system.plantMinus colour))).apply^[level]
          lengths) system.initCol := by
  rw [xiNetwork_terminal_metric_iterate system rule_connected nonnegative]
  have iterate_eq : ∀ level,
      (system.ruleFamily rule_connected).metricLengths^[level] lengths =
        ((system.connectedRuleSystem rule_connected).pathRenormMap
          (fun colour => rule_connected colour (system.plantPlus colour)
            (system.plantMinus colour))).apply^[level] lengths := by
    intro level
    induction level with
    | zero => rfl
    | succ level induction_hypothesis =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', induction_hypothesis]
      apply system.metricLengths_eq_pathRenormMap rule_connected rules_loopless rules_unique
      exact Nat.recOn level nonnegative (fun iteration previous_nonnegative => by
        rw [Function.iterate_succ_apply']
        exact RenormMap.apply_nonneg _ previous_nonnegative)
  rw [iterate_eq]

theorem xiSimpleGraph_terminal_distance_iterate (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique) (level : ℕ) :
    ((XiSimpleGraph system level).dist (xiPositiveTerminal system level)
      (xiNegativeTerminal system level) : ℝ) =
      (((system.connectedRuleSystem rule_connected).pathRenormMap
        (fun colour => rule_connected colour (system.plantPlus colour) (system.plantMinus colour))).apply^[level]
          (fun _ => 1)) system.initCol := by
  change ((XiNetwork system level).toSimpleGraph.dist (xiPositiveTerminal system level)
    (xiNegativeTerminal system level) : ℝ) = _
  rw [← (XiNetwork system level).weightedDistance_unit_eq_graphDistance
    (xiSimpleGraph_connected system rule_connected level)
    (xiNetwork_loopless system rule_connected rules_loopless level)]
  exact xiNetwork_terminal_path_metric_iterate system rule_connected rules_loopless
    rules_unique (fun _ => zero_le_one) level

end EIGS
