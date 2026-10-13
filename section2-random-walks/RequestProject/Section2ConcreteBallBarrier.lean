import RequestProject.Section2BallBarrier
import RequestProject.Section2ConcreteMetric

/-! The incident-copy ball barrier instantiated on the actual Xi successor,
using the proved original graph connectivity and actual substitution equality. -/

namespace EIGS

variable {K : ℕ}

theorem xiWeightedBall_subset_incident_copies (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    {radius : ℝ} (radius_nonnegative : 0 ≤ radius)
    (rule_distance_bound : ∀ colour,
      radius ≤ (system.ruleFamily rule_connected).metricLengths lengths colour)
    (level : ℕ) (center : XiVtx system level) (vertex : XiVtx system (level + 1))
    (in_ball : (XiNetwork system (level + 1)).weightedDistance lengths
      (Sum.inl center) vertex < radius) :
    (XiNetwork system level).IncidentCopyVertex (system.ruleFamily rule_connected) center vertex := by
  have substituted_connected : ((XiNetwork system level).subst
      (system.ruleFamily rule_connected)).toSimpleGraph.Connected := by
    rw [← xiNetwork_succ system rule_connected level]
    exact xiSimpleGraph_connected system rule_connected (level + 1)
  have distance_eq : ((XiNetwork system level).subst
      (system.ruleFamily rule_connected)).weightedDistance lengths (Sum.inl center) vertex =
      (XiNetwork system (level + 1)).weightedDistance lengths (Sum.inl center) vertex := by
    congr 1
    exact (xiNetwork_succ system rule_connected level).symm
  exact (XiNetwork system level).weighted_ball_subset_incident_copies
    (system.ruleFamily rule_connected) substituted_connected rule_connected nonnegative
    radius_nonnegative rule_distance_bound center vertex (distance_eq.symm ▸ in_ball)

end EIGS

#print axioms EIGS.xiWeightedBall_subset_incident_copies
