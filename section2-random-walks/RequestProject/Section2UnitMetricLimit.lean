import RequestProject.Section2MetricContinuity
import RequestProject.Section2ConcreteSpectralRadius

/-! Every fixed coarse pair in the original unweighted Xi graphs converges to
the compatible Perron weighted metric, with one common positive scale. The
reference vector may be any normalized positive actual metric eigenvector. -/

namespace EIGS

open scoped BigOperators
open Filter Topology

variable {K : ℕ}

theorem xiSimpleGraph_all_coarse_pairs_metric_limit (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    {lengths : Fin K → ℝ} {rate : ℝ}
    (lengths_positive : ∀ colour, 0 < lengths colour) (rate_positive : 0 < rate)
    (normalized : (∑ colour, lengths colour) = 1)
    (metric_eigenpair : (system.ruleFamily rule_connected).metricLengths lengths = rate • lengths) :
    ∃ scale : ℝ, 0 < scale ∧ ∀ coarse (source sink : XiVtx system coarse),
      Tendsto (fun steps =>
        ((XiSimpleGraph system (coarse + steps)).dist
          (xiForward system coarse steps source) (xiForward system coarse steps sink) : ℝ) /
            rate ^ (coarse + steps)) atTop
        (nhds (scale * xiScaledWeightedDistance system lengths rate coarse source sink)) := by
  let rules := system.connectedRuleSystem rule_connected
  let reachable := fun colour =>
    rule_connected colour (system.plantPlus colour) (system.plantMinus colour)
  have all_paths_use := system.rule_paths_use_every_colour rules_unique distance_positive
  have path_eigenpair : (rules.pathRenormMap reachable).apply lengths = rate • lengths := by
    rw [← system.metricLengths_eq_pathRenormMap rule_connected rules_loopless rules_unique
      (fun colour => (lengths_positive colour).le)]
    exact metric_eigenpair
  obtain ⟨scale, scale_positive, vector_convergence⟩ :=
    (rules.pathRenormMap reachable).iterate_normalized_limit_of_strongly_positive
      (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt)
      (rules.pathRenormMap_strongly_positive reachable all_paths_use)
      lengths_positive rate_positive normalized path_eigenpair
  refine ⟨scale, scale_positive, fun coarse source sink => ?_⟩
  have continuous_metric := (XiNetwork system coarse).weightedDistance_continuousAt_positive
    (xiSimpleGraph_connected system rule_connected coarse)
    (xiNetwork_loopless system rule_connected rules_loopless coarse)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent coarse)
    source sink (fun colour => mul_pos scale_positive (lengths_positive colour))
  have metric_convergence := continuous_metric.tendsto.comp vector_convergence
  have normalized_distance (steps : ℕ) :
      ((XiSimpleGraph system (coarse + steps)).dist
        (xiForward system coarse steps source) (xiForward system coarse steps sink) : ℝ) /
          rate ^ steps =
      (XiNetwork system coarse).weightedDistance
        (fun colour => (rules.pathRenormMap reachable).apply^[steps] (fun _ => 1) colour /
          rate ^ steps) source sink := by
    have normalized_lengths :
        (fun colour => (rules.pathRenormMap reachable).apply^[steps] (fun _ => 1) colour /
          rate ^ steps) =
        (rate ^ steps)⁻¹ • (rules.pathRenormMap reachable).apply^[steps] (fun _ => 1) := by
      ext colour
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [normalized_lengths, Network.weightedDistance_smul _ _
      (inv_nonneg.mpr (pow_nonneg rate_positive.le steps))]
    rw [← system.metricLengths_iterate_eq_pathRenormMap rule_connected rules_loopless
      rules_unique (fun _ => zero_le_one) steps]
    rw [← xiNetwork_forward_weightedDistance system rule_connected
      (fun _ => zero_le_one) coarse steps]
    rw [Network.weightedDistance_unit_eq_graphDistance (XiNetwork system (coarse + steps))
      (xiSimpleGraph_connected system rule_connected (coarse + steps))
      (xiNetwork_loopless system rule_connected rules_loopless (coarse + steps))]
    simp only [div_eq_mul_inv, mul_comm]
    rfl
  have step_convergence : Tendsto (fun steps =>
      ((XiSimpleGraph system (coarse + steps)).dist
        (xiForward system coarse steps source) (xiForward system coarse steps sink) : ℝ) /
          rate ^ steps) atTop
      (nhds (scale * (XiNetwork system coarse).weightedDistance lengths source sink)) := by
    convert metric_convergence using 1
    · ext steps
      exact normalized_distance steps
    · exact congrArg nhds (Network.weightedDistance_smul (XiNetwork system coarse) lengths
        scale_positive.le source sink).symm
  convert step_convergence.div_const (rate ^ coarse) using 1
  · ext steps
    simp only [div_div, pow_add, mul_comm]
  · simp only [xiScaledWeightedDistance, div_eq_mul_inv, inv_pow, mul_comm, mul_left_comm]

end EIGS

#print axioms EIGS.xiSimpleGraph_all_coarse_pairs_metric_limit
