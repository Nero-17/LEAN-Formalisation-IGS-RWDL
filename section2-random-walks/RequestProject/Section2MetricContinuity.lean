import RequestProject.Section2MetricGeometry

/-! Positive colour-length continuity for every actual finite-network pair,
and the actual multi-step old-vertex metric trace. -/

namespace EIGS.Network

variable {K : ℕ} (network : Network K)

theorem weightedDistance_continuousOn_positive
    (connected : network.toSimpleGraph.Connected) (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (source sink : network.V) :
    ContinuousOn (fun lengths : Fin K → ℝ => network.weightedDistance lengths source sink)
      {lengths | ∀ colour, 0 < lengths colour} := by
  apply ((network.pathThomsonData source sink (connected source sink)).eval_continuousOn_pos).congr
  intro lengths positive
  exact (network.path_eval_eq_weightedDistance loopless unique_edges source sink
    (connected source sink) (fun colour => (positive colour).le)).symm

theorem weightedDistance_continuousAt_positive
    (connected : network.toSimpleGraph.Connected) (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (source sink : network.V)
    {lengths : Fin K → ℝ} (positive : ∀ colour, 0 < lengths colour) :
    ContinuousAt (fun weights : Fin K → ℝ => network.weightedDistance weights source sink) lengths :=
  (network.weightedDistance_continuousOn_positive connected loopless unique_edges source sink).continuousAt
    (ThomsonData.isOpen_pos_orthant.mem_nhds positive)

end EIGS.Network

namespace EIGS

variable {K : ℕ}

theorem xiNetwork_forward_weightedDistance (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (coarse steps : ℕ)
    (source sink : XiVtx system coarse) :
    (XiNetwork system (coarse + steps)).weightedDistance lengths
      (xiForward system coarse steps source) (xiForward system coarse steps sink) =
      (XiNetwork system coarse).weightedDistance
        ((system.ruleFamily rule_connected).metricLengths^[steps] lengths) source sink := by
  induction steps generalizing lengths with
  | zero => rfl
  | succ steps induction_hypothesis =>
    change (XiNetwork system ((coarse + steps) + 1)).weightedDistance lengths
      (Sum.inl (xiForward system coarse steps source))
      (Sum.inl (xiForward system coarse steps sink)) = _
    rw [xiNetwork_weightedDistance_succ system rule_connected nonnegative,
      induction_hypothesis (Network.metricLengths_nonnegative
        (system.ruleFamily rule_connected) rule_connected nonnegative),
      Function.iterate_succ_apply]

theorem EIGSData.metricLengths_iterate_eq_pathRenormMap (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (steps : ℕ) :
    (system.ruleFamily rule_connected).metricLengths^[steps] lengths =
      ((system.connectedRuleSystem rule_connected).pathRenormMap
        (fun colour => rule_connected colour (system.plantPlus colour)
          (system.plantMinus colour))).apply^[steps] lengths := by
  induction steps generalizing lengths with
  | zero => rfl
  | succ steps induction_hypothesis =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      system.metricLengths_eq_pathRenormMap rule_connected rules_loopless rules_unique nonnegative]
    exact induction_hypothesis (RenormMap.apply_nonneg _ nonnegative)

end EIGS

#print axioms EIGS.Network.weightedDistance_continuousAt_positive
#print axioms EIGS.xiNetwork_forward_weightedDistance
