import RequestProject.Section31.EIGSMetricOfRules
import RequestProject.Section31.EIGSVertexInclusion
import RequestProject.Section2StarGeometry

/-! Actual incident stars, including vertices one adjacent step beyond
their boundary, have uniformly small diameter in the same constructed
metric completion. The fine-depth factor cancels by the metric eigenpair.
-/

namespace EIGS

open scoped BigOperators Classical
noncomputable section
variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (ratePositive : 0 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)

theorem xiCompletionEmbedding_forward (coarse steps : ℕ) (vertex : XiVtx system coarse) :
    xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair
        (coarse + steps) (xiForward system coarse steps vertex) =
      xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair
        coarse vertex := by
  simp only [xiCompletionEmbedding, Function.comp_apply, xiVertexEmbedding_forward]

theorem xiCompletionEmbedding_dist_eq_scaled_weighted (level : ℕ) (first second : XiVtx system level) :
    dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair level first)
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair level second) =
      distanceRate⁻¹ ^ level * (XiNetwork system level).weightedDistance lengths first second := by
  letI := xiLevelMetricSpace system rulesConnected lengths lengthsPositive distanceRate ratePositive level
  rw [(xiCompletionEmbedding_isometry system rulesConnected lengths lengthsPositive distanceRate ratePositive
    metricEigenpair level).dist_eq]
  rfl

theorem xiIncidentStar_completion_distance_le (rateGeTwo : 2 ≤ distanceRate)
    (coarse steps : ℕ) (center : XiVtx system coarse) (vertex : XiVtx system (coarse + steps))
    (inside : xiIncidentStar system coarse center steps vertex) :
    dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair (coarse + steps) vertex)
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair coarse center) ≤
      3 * xiRuleRadius system lengths * distanceRate⁻¹ ^ coarse := by
  rw [dist_comm, ← xiCompletionEmbedding_forward system rulesConnected lengths lengthsPositive distanceRate
    ratePositive metricEigenpair coarse steps center,
    xiCompletionEmbedding_dist_eq_scaled_weighted system rulesConnected lengths lengthsPositive distanceRate
      ratePositive metricEigenpair]
  calc
    _ ≤ distanceRate⁻¹ ^ (coarse + steps) *
        (3 * xiRuleRadius system lengths * distanceRate ^ steps) :=
      mul_le_mul_of_nonneg_left (xiIncidentStar_weightedDistance_bound system rulesConnected
        (fun colour => (lengthsPositive colour).le) rateGeTwo metricEigenpair coarse steps center inside)
        (pow_nonneg (inv_nonneg.mpr ratePositive.le) _)
    _ = 3 * xiRuleRadius system lengths * distanceRate⁻¹ ^ coarse := by
      rw [pow_add]
      calc
        _ = (3 * xiRuleRadius system lengths * distanceRate⁻¹ ^ coarse) *
            (distanceRate⁻¹ ^ steps * distanceRate ^ steps) := by ring
        _ = _ := by simp only [inv_pow, inv_mul_cancel₀ (pow_ne_zero steps ratePositive.ne'), mul_one]

theorem xiCompletionEmbedding_adj_distance_le (level : ℕ) {first second : XiVtx system level}
    (adjacency : (XiSimpleGraph system level).Adj first second) :
    dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair level first)
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair level second) ≤
      (∑ colour, lengths colour) * distanceRate⁻¹ ^ level := by
  have edge_bound (edge : XiEdge system.toRuleData level) :
      dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
            metricEigenpair level (XiTail system level edge))
          (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
            metricEigenpair level (XiHead system level edge)) ≤
        (∑ colour, lengths colour) * distanceRate⁻¹ ^ level := by
    rw [xiCompletionEmbedding_dist_eq_scaled_weighted system rulesConnected lengths lengthsPositive
      distanceRate ratePositive metricEigenpair]
    have bound := ((XiNetwork system level).weightedDistance_edge
      (fun colour => (lengthsPositive colour).le) edge).trans
      (Finset.single_le_sum (fun colour _ => (lengthsPositive colour).le) (Finset.mem_univ _))
    exact (mul_le_mul_of_nonneg_left bound (pow_nonneg (inv_nonneg.mpr ratePositive.le) _)).trans_eq
      (mul_comm _ _)
  rcases adjacency.2 with ⟨edge, tail, head⟩ | ⟨edge, tail, head⟩
  · simpa only [tail, head] using edge_bound edge
  · simpa only [tail, head, dist_comm] using edge_bound edge

/-- The adjacent outside vertex is included, so a genuine star departure
has the same coarse-scale mesh bound as the star itself. -/
theorem xiIncidentStar_adjacent_completion_distance_le (rateGeTwo : 2 ≤ distanceRate)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    {inside outside : XiVtx system (coarse + steps)}
    (inside_star : xiIncidentStar system coarse center steps inside)
    (adjacency : (XiSimpleGraph system (coarse + steps)).Adj inside outside) :
    dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair (coarse + steps) outside)
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair coarse center) ≤
      (3 * xiRuleRadius system lengths + ∑ colour, lengths colour) * distanceRate⁻¹ ^ coarse := by
  have powers : distanceRate⁻¹ ^ (coarse + steps) ≤ distanceRate⁻¹ ^ coarse := by
    rw [pow_add]
    apply mul_le_of_le_one_right (pow_nonneg (inv_nonneg.mpr ratePositive.le) _)
    exact pow_le_one₀ (inv_nonneg.mpr ratePositive.le)
      ((inv_le_one₀ ratePositive).mpr (by linarith))
  have scaled := mul_le_mul_of_nonneg_left powers
    (show 0 ≤ ∑ colour, lengths colour from
      Finset.sum_nonneg (fun colour _ => (lengthsPositive colour).le))
  calc
    _ ≤ dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair (coarse + steps) outside)
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair (coarse + steps) inside) +
      dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair (coarse + steps) inside)
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive
          metricEigenpair coarse center) := dist_triangle _ _ _
    _ ≤ (∑ colour, lengths colour) * distanceRate⁻¹ ^ (coarse + steps) +
        3 * xiRuleRadius system lengths * distanceRate⁻¹ ^ coarse :=
      add_le_add (xiCompletionEmbedding_adj_distance_le system rulesConnected lengths lengthsPositive
        distanceRate ratePositive metricEigenpair (coarse + steps) adjacency.symm)
        (xiIncidentStar_completion_distance_le system rulesConnected lengths lengthsPositive distanceRate
          ratePositive metricEigenpair rateGeTwo coarse steps center inside inside_star)
    _ ≤ _ := by nlinarith

theorem xiCanonicalIncidentStar_completion_mesh_of_rules
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ coarse steps (center : XiVtx system coarse)
      (vertex : XiVtx system (coarse + steps)),
      (xiIncidentStar system coarse center steps vertex ∨
        ∃ inside, xiIncidentStar system coarse center steps inside ∧
          (XiSimpleGraph system (coarse + steps)).Adj inside vertex) →
      dist (parameters.vertexEmbedding (coarse + steps) vertex) (parameters.vertexEmbedding coarse center) ≤
        coefficient * (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse := by
  intro parameters
  have radiusNonnegative := xiRuleRadius_nonnegative system (fun colour => (parameters.lengthsPositive colour).le)
  have rateGeTwo := system.two_le_distanceSpectralRadius rulesConnected rulesUnique
    plantingNonadjacent distancePositive
  refine ⟨3 * xiRuleRadius system parameters.lengths + 1, by positivity, ?_⟩
  intro coarse steps center vertex membership
  rcases membership with inside | ⟨inside, inside_star, adjacent⟩
  · have bound := xiIncidentStar_completion_distance_le system rulesConnected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) parameters.ratePositive
      parameters.eigenpair rateGeTwo coarse steps center vertex inside
    change dist (xiCompletionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair
      (coarse + steps) vertex) _ ≤ _
    exact bound.trans (by
      nlinarith [pow_nonneg (inv_nonneg.mpr parameters.ratePositive.le) coarse])
  · have bound := xiIncidentStar_adjacent_completion_distance_le system rulesConnected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) parameters.ratePositive
      parameters.eigenpair rateGeTwo coarse steps center inside_star adjacent
    simpa only [parameters.normalized] using bound

end
end EIGS

#print axioms EIGS.xiCompletionEmbedding_forward
#print axioms EIGS.xiCompletionEmbedding_dist_eq_scaled_weighted
#print axioms EIGS.xiIncidentStar_completion_distance_le
#print axioms EIGS.xiIncidentStar_adjacent_completion_distance_le
#print axioms EIGS.xiCanonicalIncidentStar_completion_mesh_of_rules
