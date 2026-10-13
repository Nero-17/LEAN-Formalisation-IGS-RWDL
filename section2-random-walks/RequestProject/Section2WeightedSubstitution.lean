import RequestProject.Section2WeightedMetric

/-! Exact weighted shortest-path trace under actual network substitution.
The lower bound uses an explicit Lipschitz extension on each private copy. -/

namespace EIGS.Network

variable {K : ℕ} (network : Network K) (rules : RuleFamily K)

noncomputable def _root_.EIGS.RuleFamily.metricLengths
    (rules : RuleFamily K) (lengths : Fin K → ℝ) (colour : Fin K) : ℝ :=
  (rules.R colour).weightedDistance lengths (rules.βplus colour) (rules.βminus colour)

theorem metricLengths_nonnegative
    (rules_connected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) :
    0 ≤ rules.metricLengths lengths := fun colour =>
  (rules.R colour).weightedDistance_nonnegative (rules_connected colour) nonnegative _ _

noncomputable def substMetricPotential (lengths : Fin K → ℝ)
    (potential : network.V → ℝ) : (network.subst rules).V → ℝ
  | Sum.inl vertex => potential vertex
  | Sum.inr ⟨edge, interior⟩ => min
      (potential (network.tail edge) + (rules.R (network.color edge)).weightedDistance lengths
        (rules.βplus (network.color edge)) interior.val)
      (potential (network.head edge) + (rules.R (network.color edge)).weightedDistance lengths
        (rules.βminus (network.color edge)) interior.val)

theorem substMetricPotential_on_copy
    (rules_connected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    (potential : network.V → ℝ)
    (lipschitz : network.EdgeLipschitz (rules.metricLengths lengths) potential)
    (edge : network.E) (vertex : (rules.R (network.color edge)).V) :
    network.substMetricPotential rules lengths potential (network.substEmbed rules edge vertex) = min
      (potential (network.tail edge) + (rules.R (network.color edge)).weightedDistance lengths
        (rules.βplus (network.color edge)) vertex)
      (potential (network.head edge) + (rules.R (network.color edge)).weightedDistance lengths
        (rules.βminus (network.color edge)) vertex) := by
  have endpoints := abs_le.mp (lipschitz edge)
  change - (rules.R (network.color edge)).weightedDistance lengths
      (rules.βplus (network.color edge)) (rules.βminus (network.color edge)) ≤
        potential (network.tail edge) - potential (network.head edge) ∧
    potential (network.tail edge) - potential (network.head edge) ≤
      (rules.R (network.color edge)).weightedDistance lengths
        (rules.βplus (network.color edge)) (rules.βminus (network.color edge)) at endpoints
  by_cases plus_eq : vertex = rules.βplus (network.color edge)
  · subst vertex
    rw [substEmbed_plantPlus]
    change potential (network.tail edge) = _
    rw [(rules.R (network.color edge)).weightedDistance_self nonnegative,
      add_zero, (rules.R (network.color edge)).weightedDistance_symm
        (rules_connected (network.color edge)) nonnegative
        (rules.βminus (network.color edge)) (rules.βplus (network.color edge))]
    exact (min_eq_left (by linarith)).symm
  · by_cases minus_eq : vertex = rules.βminus (network.color edge)
    · subst vertex
      rw [substEmbed_plantMinus]
      change potential (network.head edge) = _
      rw [(rules.R (network.color edge)).weightedDistance_self nonnegative, add_zero]
      exact (min_eq_right (by linarith)).symm
    · simp only [substEmbed, plus_eq, minus_eq, ↓reduceDIte, substMetricPotential]

theorem EdgeLipschitz.min {lengths : Fin K → ℝ} {first second : network.V → ℝ}
    (first_lipschitz : network.EdgeLipschitz lengths first)
    (second_lipschitz : network.EdgeLipschitz lengths second) :
    network.EdgeLipschitz lengths (fun vertex => min (first vertex) (second vertex)) := by
  intro edge
  obtain ⟨first_lower, first_upper⟩ := abs_le.mp (first_lipschitz edge)
  obtain ⟨second_lower, second_upper⟩ := abs_le.mp (second_lipschitz edge)
  apply abs_le.mpr
  constructor
  · have bound := min_le_min
      (show first (network.head edge) ≤ first (network.tail edge) + lengths (network.color edge)
        by linarith)
      (show second (network.head edge) ≤ second (network.tail edge) + lengths (network.color edge)
        by linarith)
    rw [min_add_add_right] at bound
    linarith
  · have bound := min_le_min
      (show first (network.tail edge) ≤ first (network.head edge) + lengths (network.color edge)
        by linarith)
      (show second (network.tail edge) ≤ second (network.head edge) + lengths (network.color edge)
        by linarith)
    rw [min_add_add_right] at bound
    linarith

theorem substMetricPotential_lipschitz
    (rules_connected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    (potential : network.V → ℝ)
    (lipschitz : network.EdgeLipschitz (rules.metricLengths lengths) potential) :
    (network.subst rules).EdgeLipschitz lengths
      (network.substMetricPotential rules lengths potential) := by
  intro edge
  change |network.substMetricPotential rules lengths potential
      (network.substEmbed rules edge.1 ((rules.R (network.color edge.1)).tail edge.2)) -
    network.substMetricPotential rules lengths potential
      (network.substEmbed rules edge.1 ((rules.R (network.color edge.1)).head edge.2))| ≤ _
  rw [network.substMetricPotential_on_copy rules rules_connected nonnegative potential lipschitz,
    network.substMetricPotential_on_copy rules rules_connected nonnegative potential lipschitz]
  have plus_lipschitz : (rules.R (network.color edge.1)).EdgeLipschitz lengths
      (fun vertex => potential (network.tail edge.1) +
        (rules.R (network.color edge.1)).weightedDistance lengths
          (rules.βplus (network.color edge.1)) vertex) := by
    intro ruleEdge
    simpa only [add_sub_add_left_eq_sub] using
      (rules.R (network.color edge.1)).weightedDistance_edgeLipschitz
        (rules_connected (network.color edge.1)) nonnegative
        (rules.βplus (network.color edge.1)) ruleEdge
  have minus_lipschitz : (rules.R (network.color edge.1)).EdgeLipschitz lengths
      (fun vertex => potential (network.head edge.1) +
        (rules.R (network.color edge.1)).weightedDistance lengths
          (rules.βminus (network.color edge.1)) vertex) := by
    intro ruleEdge
    simpa only [add_sub_add_left_eq_sub] using
      (rules.R (network.color edge.1)).weightedDistance_edgeLipschitz
        (rules_connected (network.color edge.1)) nonnegative
        (rules.βminus (network.color edge.1)) ruleEdge
  exact EdgeLipschitz.min _ plus_lipschitz minus_lipschitz edge.2

theorem weightedDistance_subst_ge
    (connected : network.toSimpleGraph.Connected)
    (rules_connected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (source sink : network.V) :
    network.weightedDistance (rules.metricLengths lengths) source sink ≤
      (network.subst rules).weightedDistance lengths (Sum.inl source) (Sum.inl sink) := by
  classical
  let selected := fun colour => EdgeWalk.ofGraphWalk
    (Classical.choice (rules_connected colour (rules.βplus colour) (rules.βminus colour)))
  letI : Nonempty ((network.subst rules).EdgeWalk (Sum.inl source) (Sum.inl sink)) :=
    ⟨network.liftEdgeWalk rules selected
      (Classical.choice (network.edgeWalk_nonempty_of_connected connected source sink))⟩
  have metric_nonnegative := metricLengths_nonnegative rules rules_connected nonnegative
  let potential := network.weightedDistance (rules.metricLengths lengths) source
  have lipschitz := network.weightedDistance_edgeLipschitz connected metric_nonnegative source
  have extended_lipschitz := network.substMetricPotential_lipschitz rules rules_connected
    nonnegative potential lipschitz
  apply le_ciInf
  intro walk
  have bound := EdgeWalk.potential_difference_le_cost (network.subst rules) extended_lipschitz walk
  change |network.weightedDistance (rules.metricLengths lengths) source source -
    network.weightedDistance (rules.metricLengths lengths) source sink| ≤ walk.cost lengths at bound
  rw [network.weightedDistance_self metric_nonnegative, zero_sub, abs_neg,
    abs_of_nonneg (network.weightedDistance_nonnegative connected metric_nonnegative source sink)] at bound
  exact bound

theorem weightedDistance_subst_le
    (connected : network.toSimpleGraph.Connected)
    (rules_connected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (source sink : network.V) :
    (network.subst rules).weightedDistance lengths (Sum.inl source) (Sum.inl sink) ≤
      network.weightedDistance (rules.metricLengths lengths) source sink := by
  classical
  let selected := fun colour => EdgeWalk.ofGraphWalk
    (Classical.choice (rules_connected colour (rules.βplus colour) (rules.βminus colour)))
  have edge_bounds (edge : network.E) :
      (network.subst rules).weightedDistance lengths (Sum.inl (network.tail edge))
          (Sum.inl (network.head edge)) ≤ rules.metricLengths lengths (network.color edge) ∧
      (network.subst rules).weightedDistance lengths (Sum.inl (network.head edge))
          (Sum.inl (network.tail edge)) ≤ rules.metricLengths lengths (network.color edge) := by
    letI := (rules.R (network.color edge)).edgeWalk_nonempty_of_connected
      (rules_connected (network.color edge)) (rules.βplus (network.color edge))
      (rules.βminus (network.color edge))
    constructor <;> apply le_ciInf <;> intro walk
    · simpa only [cost_terminalRuleEdgeWalk] using
        (network.subst rules).weightedDistance_le_cost nonnegative
          (network.terminalRuleEdgeWalk rules edge walk)
    · simpa only [EdgeWalk.cost_reverse, cost_terminalRuleEdgeWalk] using
        (network.subst rules).weightedDistance_le_cost nonnegative
          (network.terminalRuleEdgeWalk rules edge walk).reverse
  letI := network.edgeWalk_nonempty_of_connected connected source sink
  apply le_ciInf
  intro walk
  induction walk with
  | nil => simp [(network.subst rules).weightedDistance_self nonnegative, EdgeWalk.cost]
  | @cons first next last edge joins rest induction_hypothesis =>
    have triangle := (network.subst rules).weightedDistance_triangle_of_walks nonnegative
      (Sum.inl first) (Sum.inl next) (Sum.inl last)
      ⟨network.liftEdgeWalk rules selected (EdgeWalk.cons edge joins (.nil next))⟩
      ⟨network.liftEdgeWalk rules selected rest⟩
    have step_bound : (network.subst rules).weightedDistance lengths (Sum.inl first)
        (Sum.inl next) ≤ rules.metricLengths lengths (network.color edge) := by
      rcases joins with ⟨tail_eq, head_eq⟩ | ⟨tail_eq, head_eq⟩
      · simpa only [tail_eq, head_eq] using (edge_bounds edge).1
      · simpa only [tail_eq, head_eq] using (edge_bounds edge).2
    exact triangle.trans (add_le_add step_bound induction_hypothesis)

/-- The weighted shortest-path metric on old vertices is exactly the base
metric with each colour replaced by its actual rule terminal distance. -/
theorem weightedDistance_subst
    (connected : network.toSimpleGraph.Connected)
    (rules_connected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (source sink : network.V) :
    (network.subst rules).weightedDistance lengths (Sum.inl source) (Sum.inl sink) =
      network.weightedDistance (rules.metricLengths lengths) source sink :=
  le_antisymm (network.weightedDistance_subst_le rules connected rules_connected nonnegative source sink)
    (network.weightedDistance_subst_ge rules connected rules_connected nonnegative source sink)

end EIGS.Network
