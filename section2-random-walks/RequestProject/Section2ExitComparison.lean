import RequestProject.Section2SimpleCommute
import RequestProject.Section2ConcreteBallBarrier

/-! Monotonicity for the actual survival-series expected exit times. In
particular, the proved geometric containment of a substituted weighted ball
gives the corresponding expected-exit comparison with its incident copies. -/

namespace EIGS

open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V]
variable {graph : SimpleGraph V} [DecidableRel graph.Adj]

theorem surv_mono_domain {inside outside : Finset V} (contained : inside ⊆ outside)
    (steps : ℕ) (vertex : V) :
    surv graph inside steps vertex ≤ surv graph outside steps vertex := by
  induction steps generalizing vertex with
  | zero =>
    by_cases membership : vertex ∈ inside
    · simp only [surv, membership, contained membership, ↓reduceIte, le_refl]
    · simp only [surv, membership, ↓reduceIte]
      split <;> norm_num
  | succ steps induction_hypothesis =>
    by_cases membership : vertex ∈ inside
    · simp only [surv, membership, contained membership, ↓reduceIte]
      exact Finset.sum_le_sum (fun neighbour _ =>
        mul_le_mul_of_nonneg_left (induction_hypothesis neighbour) (transProb_nonneg _ _))
    · rw [surv_zero_of_notMem membership]
      exact surv_nonneg _ _

theorem expExit_mono_domain (connected : graph.Connected)
    {inside outside : Finset V} (contained : inside ⊆ outside)
    (outside_complement : outsideᶜ.Nonempty) (vertex : V) :
    expExit graph inside vertex ≤ expExit graph outside vertex := by
  have inside_complement : insideᶜ.Nonempty := by
    obtain ⟨boundary, boundary_outside⟩ := outside_complement
    refine ⟨boundary, Finset.mem_compl.mpr ?_⟩
    exact fun membership => (Finset.mem_compl.mp boundary_outside) (contained membership)
  exact Summable.tsum_le_tsum (fun steps => surv_mono_domain contained steps vertex)
    (expExit_summable connected inside_complement vertex)
    (expExit_summable connected outside_complement vertex)

namespace Network

variable {K : ℕ} (network : Network K)

theorem expExit_le_mass_mul_effRes (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (connected : network.toSimpleGraph.Connected)
    (domain : Finset network.V) (source sink : network.V) (source_ne_sink : source ≠ sink)
    (sink_outside : sink ∉ domain) :
    expExit network.toSimpleGraph domain source ≤
      2 * (Fintype.card network.E : ℝ) * network.effRes source sink
        (network.flow_nonempty_of_connected connected source sink source_ne_sink) (fun _ => 1) := by
  have contained : domain ⊆ {sink}ᶜ := by
    intro vertex membership
    simp only [Finset.mem_compl, Finset.mem_singleton]
    exact fun equality => sink_outside (equality ▸ membership)
  calc
    expExit network.toSimpleGraph domain source ≤
        expExit network.toSimpleGraph ({sink}ᶜ) source :=
      expExit_mono_domain connected contained (by simp) source
    _ ≤ expExit network.toSimpleGraph ({sink}ᶜ) source +
        expExit network.toSimpleGraph ({source}ᶜ) sink :=
      le_add_of_nonneg_right (expExit_nonneg _)
    _ = _ := network.commute_eq_mass_mul_effRes loopless unique_edges connected
      source sink source_ne_sink

theorem weighted_ball_expExit_le_incident_copies (rules : RuleFamily K)
    (substituted_connected : (network.subst rules).toSimpleGraph.Connected)
    (rules_connected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    {radius : ℝ} (radius_nonnegative : 0 ≤ radius)
    (rule_distance_bound : ∀ colour, radius ≤ rules.metricLengths lengths colour)
    (center : network.V)
    (star_complement : (Finset.univ.filter (network.IncidentCopyVertex rules center))ᶜ.Nonempty) :
    expExit (network.subst rules).toSimpleGraph
        (Finset.univ.filter (fun vertex =>
          (network.subst rules).weightedDistance lengths (Sum.inl center) vertex < radius))
        (Sum.inl center) ≤
      expExit (network.subst rules).toSimpleGraph
        (Finset.univ.filter (network.IncidentCopyVertex rules center)) (Sum.inl center) := by
  apply expExit_mono_domain substituted_connected _ star_complement
  intro vertex membership
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    network.weighted_ball_subset_incident_copies rules substituted_connected rules_connected
      nonnegative radius_nonnegative rule_distance_bound center vertex
      (Finset.mem_filter.mp membership).2⟩

end Network
end EIGS

#print axioms EIGS.surv_mono_domain
#print axioms EIGS.expExit_mono_domain
#print axioms EIGS.Network.expExit_le_mass_mul_effRes
#print axioms EIGS.Network.weighted_ball_expExit_le_incident_copies
