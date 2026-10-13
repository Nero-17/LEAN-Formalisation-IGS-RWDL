import RequestProject.Section2DescendantRadius
import RequestProject.Section2MultiStepSpectralBall
import RequestProject.Section2MetricContinuity

/-! Actual private descendants of an incident coarse edge are contained
in a ball at a uniform multiple of the original distance spectral scale. -/

namespace EIGS

open scoped Classical

variable {K : ℕ}

theorem xiDescendant_private_vertex_distance_bound (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) {rate : ℝ} (rate_ge_two : 2 ≤ rate)
    (eigenpair : (system.ruleFamily rule_connected).metricLengths lengths = rate • lengths)
    (coarse steps : ℕ) (edge : XiEdge system.toRuleData (coarse + steps))
    (interior : {vertex : (system.rule (XiCol system.toRuleData (coarse + steps) edge)).V //
      vertex ≠ system.plantPlus (XiCol system.toRuleData (coarse + steps) edge) ∧
        vertex ≠ system.plantMinus (XiCol system.toRuleData (coarse + steps) edge)}) :
    (XiNetwork system ((coarse + steps) + 1)).weightedDistance lengths
      (xiForward system coarse (steps + 1) (XiTail system coarse (xiEdgeAncestor system coarse steps edge)))
      (Sum.inr ⟨edge, interior⟩) ≤
      2 * xiRuleRadius system lengths * rate ^ (steps + 1) - xiRuleRadius system lengths := by
  have rate_nonnegative : 0 ≤ rate := (by norm_num : (0 : ℝ) ≤ 2).trans rate_ge_two
  have radius_nonnegative := xiRuleRadius_nonnegative system nonnegative
  have parent_bound := (xiDescendant_endpoint_distance_bound system rule_connected nonnegative
    rate_ge_two eigenpair coarse steps edge).1
  have copy_bound := xiWeightedDistance_rule_vertex_from_forward_le system rule_connected nonnegative
    rate_nonnegative eigenpair coarse steps
      (XiTail system coarse (xiEdgeAncestor system coarse steps edge)) edge interior.val
  rw [embedRuleVtx_interior system (coarse + steps) edge _ _ interior.property.1 interior.property.2] at copy_bound
  apply copy_bound.trans
  calc
    _ ≤ rate * (2 * xiRuleRadius system lengths * rate ^ steps - xiRuleRadius system lengths) +
        xiRuleRadius system lengths := add_le_add
          (mul_le_mul_of_nonneg_left parent_bound rate_nonnegative) le_rfl
    _ ≤ _ := by
      rw [pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.mpr rate_ge_two) radius_nonnegative]

theorem xiDescendant_private_vertex_distance_from_incident_center_le (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) {rate : ℝ} (rate_ge_two : 2 ≤ rate)
    (eigenpair : (system.ruleFamily rule_connected).metricLengths lengths = rate • lengths)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (edge : XiEdge system.toRuleData (coarse + steps))
    (incident : XiTail system coarse (xiEdgeAncestor system coarse steps edge) = center ∨
      XiHead system coarse (xiEdgeAncestor system coarse steps edge) = center)
    (interior : {vertex : (system.rule (XiCol system.toRuleData (coarse + steps) edge)).V //
      vertex ≠ system.plantPlus (XiCol system.toRuleData (coarse + steps) edge) ∧
        vertex ≠ system.plantMinus (XiCol system.toRuleData (coarse + steps) edge)}) :
    (XiNetwork system ((coarse + steps) + 1)).weightedDistance lengths
      (xiForward system coarse (steps + 1) center) (Sum.inr ⟨edge, interior⟩) ≤
      3 * xiRuleRadius system lengths * rate ^ (steps + 1) := by
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
  have coarse_bound : (XiNetwork system coarse).weightedDistance lengths center
      (XiTail system coarse (xiEdgeAncestor system coarse steps edge)) ≤ xiRuleRadius system lengths := by
    rcases incident with tail_center | head_center
    · rw [← tail_center, (XiNetwork system coarse).weightedDistance_self nonnegative]
      exact radius_nonnegative
    · rw [← head_center, (XiNetwork system coarse).weightedDistance_symm
        (xiSimpleGraph_connected system rule_connected coarse) nonnegative]
      exact ((XiNetwork system coarse).weightedDistance_edge nonnegative _).trans (length_bound _)
  have old_trace := xiNetwork_forward_weightedDistance system rule_connected nonnegative coarse (steps + 1)
    center (XiTail system coarse (xiEdgeAncestor system coarse steps edge))
  rw [system.metricLengths_iterate_eigenpair rule_connected rate_nonnegative eigenpair,
    (XiNetwork system coarse).weightedDistance_smul lengths (pow_nonneg rate_nonnegative _)] at old_trace
  have old_bound := old_trace.le.trans
    (mul_le_mul_of_nonneg_left coarse_bound (pow_nonneg rate_nonnegative (steps + 1)))
  have private_bound := xiDescendant_private_vertex_distance_bound system rule_connected nonnegative
    rate_ge_two eigenpair coarse steps edge interior
  have triangle := (XiNetwork system ((coarse + steps) + 1)).weightedDistance_triangle
    (xiSimpleGraph_connected system rule_connected _) nonnegative
      (xiForward system coarse (steps + 1) center)
      (xiForward system coarse (steps + 1) (XiTail system coarse (xiEdgeAncestor system coarse steps edge)))
      (Sum.inr ⟨edge, interior⟩)
  exact triangle.trans ((add_le_add old_bound private_bound).trans (by nlinarith))

theorem xiSimpleGraph_private_descendants_in_ball_of_eigenpair (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    {lengths : Fin K → ℝ} (lengths_positive : ∀ colour, 0 < lengths colour)
    {rate : ℝ} (rate_ge_two : 2 ≤ rate)
    (eigenpair : (system.ruleFamily rule_connected).metricLengths lengths = rate • lengths) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ coarse steps (center : XiVtx system coarse)
      (edge : XiEdge system.toRuleData (coarse + steps)),
      (XiTail system coarse (xiEdgeAncestor system coarse steps edge) = center ∨
        XiHead system coarse (xiEdgeAncestor system coarse steps edge) = center) →
      ∀ interior : {vertex : (system.rule (XiCol system.toRuleData (coarse + steps) edge)).V //
        vertex ≠ system.plantPlus (XiCol system.toRuleData (coarse + steps) edge) ∧
          vertex ≠ system.plantMinus (XiCol system.toRuleData (coarse + steps) edge)},
      ∀ radius : ℝ, coefficient * rate ^ (steps + 1) ≤ radius →
        ((XiSimpleGraph system ((coarse + steps) + 1)).dist
          (xiForward system coarse (steps + 1) center) (Sum.inr ⟨edge, interior⟩) : ℝ) < radius := by
  classical
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  let lower := Finset.univ.inf' Finset.univ_nonempty lengths
  let upper := Finset.univ.sup' Finset.univ_nonempty lengths
  have lower_positive : 0 < lower :=
    (Finset.lt_inf'_iff _).mpr (fun colour _ => lengths_positive colour)
  have upper_positive : 0 < upper :=
    (lengths_positive system.initCol).trans_le (Finset.le_sup' lengths (Finset.mem_univ _))
  have rate_positive : 0 < rate := (by norm_num : (0 : ℝ) < 2).trans_le rate_ge_two
  have radius_positive : 0 < xiRuleRadius system lengths := by
    have coordinate := congrFun eigenpair system.initCol
    change (system.ruleNetwork system.initCol).weightedDistance lengths
      (system.plantPlus system.initCol) (system.plantMinus system.initCol) =
        rate * lengths system.initCol at coordinate
    have bound := xiRuleRadius_bound system lengths system.initCol (system.plantMinus system.initCol)
    rw [coordinate] at bound
    exact (mul_pos rate_positive (lengths_positive _)).trans_le bound
  refine ⟨4 * xiRuleRadius system lengths / lower, div_pos (by positivity) lower_positive,
    fun coarse steps center edge incident interior radius radius_bound => ?_⟩
  have metric_bound := xiDescendant_private_vertex_distance_from_incident_center_le system
    rule_connected (fun colour => (lengths_positive colour).le) rate_ge_two eigenpair
      coarse steps center edge incident interior
  have graph_bound := (XiNetwork system ((coarse + steps) + 1)).weightedDistance_length_bounds
    (xiSimpleGraph_connected system rule_connected _)
    (xiNetwork_loopless system rule_connected rules_loopless _)
    lower_positive.le upper_positive.le
    (fun colour => Finset.inf'_le lengths (Finset.mem_univ colour))
    (fun colour => Finset.le_sup' lengths (Finset.mem_univ colour))
    (xiForward system coarse (steps + 1) center) (Sum.inr ⟨edge, interior⟩)
  have scaled_radius := mul_le_mul_of_nonneg_left radius_bound lower_positive.le
  have graph_lower : lower *
      ((XiSimpleGraph system ((coarse + steps) + 1)).dist
        (xiForward system coarse (steps + 1) center) (Sum.inr ⟨edge, interior⟩) : ℝ) ≤
      (XiNetwork system ((coarse + steps) + 1)).weightedDistance lengths
        (xiForward system coarse (steps + 1) center) (Sum.inr ⟨edge, interior⟩) := graph_bound.1
  have cancellation : lower * (4 * xiRuleRadius system lengths / lower * rate ^ (steps + 1)) =
      4 * xiRuleRadius system lengths * rate ^ (steps + 1) := by field_simp
  rw [cancellation] at scaled_radius
  have strict_bound : lower *
      ((XiSimpleGraph system ((coarse + steps) + 1)).dist
        (xiForward system coarse (steps + 1) center) (Sum.inr ⟨edge, interior⟩) : ℝ) < lower * radius := by
    nlinarith [graph_lower, metric_bound, mul_pos radius_positive (pow_pos rate_positive (steps + 1))]
  by_contra not_lt
  have product_nonnegative := mul_nonneg lower_positive.le (sub_nonneg.mpr (le_of_not_gt not_lt))
  nlinarith [strict_bound]

end EIGS

#print axioms EIGS.xiDescendant_private_vertex_distance_bound
#print axioms EIGS.xiDescendant_private_vertex_distance_from_incident_center_le
#print axioms EIGS.xiSimpleGraph_private_descendants_in_ball_of_eigenpair
