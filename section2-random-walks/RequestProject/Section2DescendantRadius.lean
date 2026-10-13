import RequestProject.Section2StarCounts
import RequestProject.Section2MetricCells

/-! A direct actual descendant-cell radius estimate. It uses actual
ancestor edges, labelled walks inside copies, and exact Perron trace scaling. -/

namespace EIGS

variable {K : ℕ}

theorem xiWeightedDistance_rule_vertex_from_forward_le (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) {rate : ℝ} (rate_nonnegative : 0 ≤ rate)
    (eigenpair : (system.ruleFamily rule_connected).metricLengths lengths = rate • lengths)
    (coarse steps : ℕ) (source : XiVtx system coarse)
    (edge : XiEdge system.toRuleData (coarse + steps))
    (vertex : (system.rule (XiCol system.toRuleData (coarse + steps) edge)).V) :
    (XiNetwork system ((coarse + steps) + 1)).weightedDistance lengths
      (xiForward system coarse (steps + 1) source)
      (embedRuleVtx system (coarse + steps) edge (XiTail system (coarse + steps) edge)
        (XiHead system (coarse + steps) edge) vertex) ≤
      rate * (XiNetwork system (coarse + steps)).weightedDistance lengths
        (xiForward system coarse steps source) (XiTail system (coarse + steps) edge) +
          xiRuleRadius system lengths := by
  have triangle := (XiNetwork system ((coarse + steps) + 1)).weightedDistance_triangle
    (xiSimpleGraph_connected system rule_connected _) nonnegative
      (Sum.inl (xiForward system coarse steps source))
      (Sum.inl (XiTail system (coarse + steps) edge))
      (embedRuleVtx system (coarse + steps) edge (XiTail system (coarse + steps) edge)
        (XiHead system (coarse + steps) edge) vertex)
  have copy_bound := xiWeightedDistance_rule_copy_le system rule_connected
    (coarse + steps) edge nonnegative (system.plantPlus _) vertex
  rw [embedRuleVtx_plantPlus] at copy_bound
  have old_trace := xiNetwork_weightedDistance_succ system rule_connected nonnegative
    (coarse + steps) (xiForward system coarse steps source) (XiTail system (coarse + steps) edge)
  rw [eigenpair, (XiNetwork system (coarse + steps)).weightedDistance_smul lengths rate_nonnegative] at old_trace
  exact triangle.trans (add_le_add old_trace.le (copy_bound.trans (xiRuleRadius_bound system lengths _ vertex)))

theorem xiDescendant_endpoint_distance_bound (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) {rate : ℝ} (rate_ge_two : 2 ≤ rate)
    (eigenpair : (system.ruleFamily rule_connected).metricLengths lengths = rate • lengths)
    (coarse steps : ℕ) (edge : XiEdge system.toRuleData (coarse + steps)) :
    (XiNetwork system (coarse + steps)).weightedDistance lengths
        (xiForward system coarse steps (XiTail system coarse (xiEdgeAncestor system coarse steps edge)))
        (XiTail system (coarse + steps) edge) ≤
      2 * xiRuleRadius system lengths * rate ^ steps - xiRuleRadius system lengths ∧
    (XiNetwork system (coarse + steps)).weightedDistance lengths
        (xiForward system coarse steps (XiTail system coarse (xiEdgeAncestor system coarse steps edge)))
        (XiHead system (coarse + steps) edge) ≤
      2 * xiRuleRadius system lengths * rate ^ steps - xiRuleRadius system lengths := by
  have rate_nonnegative : 0 ≤ rate := (by norm_num : (0 : ℝ) ≤ 2).trans rate_ge_two
  have radius_nonnegative := xiRuleRadius_nonnegative system nonnegative
  have length_bound : ∀ colour, lengths colour ≤ xiRuleRadius system lengths := by
    intro colour
    have terminal_bound := xiRuleRadius_bound system lengths colour (system.plantMinus colour)
    have coordinate := congrFun eigenpair colour
    change (system.ruleNetwork colour).weightedDistance lengths
      (system.plantPlus colour) (system.plantMinus colour) = rate * lengths colour at coordinate
    rw [coordinate] at terminal_bound
    nlinarith [nonnegative colour]
  induction steps with
  | zero =>
    constructor
    · change (XiNetwork system coarse).weightedDistance lengths
        (XiTail system coarse edge) (XiTail system coarse edge) ≤ _
      rw [(XiNetwork system coarse).weightedDistance_self nonnegative]
      simp only [pow_zero, mul_one]
      linarith
    · have edge_bound := (XiNetwork system coarse).weightedDistance_edge nonnegative edge
      change (XiNetwork system coarse).weightedDistance lengths
        (XiTail system coarse edge) (XiHead system coarse edge) ≤ _
      simpa only [pow_zero, mul_one, two_mul, add_sub_cancel_right] using
        edge_bound.trans (length_bound (XiCol system.toRuleData coarse edge))
  | succ steps induction_hypothesis =>
    have parent_bound := (induction_hypothesis edge.1).1
    have next_bound :
        rate * (XiNetwork system (coarse + steps)).weightedDistance lengths
          (xiForward system coarse steps (XiTail system coarse (xiEdgeAncestor system coarse steps edge.1)))
          (XiTail system (coarse + steps) edge.1) + xiRuleRadius system lengths ≤
          2 * xiRuleRadius system lengths * rate ^ (steps + 1) - xiRuleRadius system lengths := by
      calc
        _ ≤ rate * (2 * xiRuleRadius system lengths * rate ^ steps - xiRuleRadius system lengths) +
            xiRuleRadius system lengths := add_le_add
              (mul_le_mul_of_nonneg_left parent_bound rate_nonnegative) le_rfl
        _ ≤ _ := by
          rw [pow_succ]
          nlinarith [mul_nonneg (sub_nonneg.mpr rate_ge_two) radius_nonnegative]
    constructor
    · change (XiNetwork system ((coarse + steps) + 1)).weightedDistance lengths
        (xiForward system coarse (steps + 1)
          (XiTail system coarse (xiEdgeAncestor system coarse steps edge.1)))
        (XiTail system ((coarse + steps) + 1) edge) ≤ _
      rw [XiTail_succ]
      exact (xiWeightedDistance_rule_vertex_from_forward_le system rule_connected nonnegative
        rate_nonnegative eigenpair coarse steps _ edge.1 _).trans next_bound
    · change (XiNetwork system ((coarse + steps) + 1)).weightedDistance lengths
        (xiForward system coarse (steps + 1)
          (XiTail system coarse (xiEdgeAncestor system coarse steps edge.1)))
        (XiHead system ((coarse + steps) + 1) edge) ≤ _
      rw [XiHead_succ]
      exact (xiWeightedDistance_rule_vertex_from_forward_le system rule_connected nonnegative
        rate_nonnegative eigenpair coarse steps _ edge.1 _).trans next_bound

end EIGS

#print axioms EIGS.xiWeightedDistance_rule_vertex_from_forward_le
#print axioms EIGS.xiDescendant_endpoint_distance_bound
