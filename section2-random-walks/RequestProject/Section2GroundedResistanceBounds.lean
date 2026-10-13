import RequestProject.Section2GroundedTrace
import RequestProject.Section2ResistanceSpectralRadius
import RequestProject.Section2BallLower

/-! Exact coarse grounding gives actual resistance bounds at the canonical
nonlinear spectral scale, and a genuine upper bound for actual graph balls. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem Network.parallel_resistance_bounds (network : Network K)
    (loopless : network.Loopless) (unique_edges : network.EdgesUnique) (center : network.V)
    (degree_positive : 0 < (network.toSimpleGraph.degree center : ℝ))
    (resistances : Fin K → ℝ) (resistances_positive : ∀ colour, 0 < resistances colour)
    {lower upper : ℝ} (lower_positive : 0 < lower) (upper_positive : 0 < upper)
    (lower_bound : ∀ colour, lower ≤ resistances colour)
    (upper_bound : ∀ colour, resistances colour ≤ upper) :
    lower / network.toSimpleGraph.degree center ≤
        (∑ edge, if network.tail edge = center ∨ network.head edge = center then
          (resistances (network.color edge))⁻¹ else 0)⁻¹ ∧
      (∑ edge, if network.tail edge = center ∨ network.head edge = center then
          (resistances (network.color edge))⁻¹ else 0)⁻¹ ≤
        upper / network.toSimpleGraph.degree center := by
  classical
  have count_identity := network.incident_edge_count_eq_degree loopless unique_edges center
  have conductance_lower : (network.toSimpleGraph.degree center : ℝ) / upper ≤
      ∑ edge, if network.tail edge = center ∨ network.head edge = center then
        (resistances (network.color edge))⁻¹ else 0 := by
    rw [div_eq_mul_inv, ← count_identity, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro edge _
    by_cases incident : network.tail edge = center ∨ network.head edge = center
    · simp only [incident, ↓reduceIte, one_mul]
      simpa only [one_div] using one_div_le_one_div_of_le (resistances_positive _)
        (upper_bound (network.color edge))
    · simp only [incident, ↓reduceIte, zero_mul, le_refl]
  have conductance_upper : (∑ edge, if network.tail edge = center ∨ network.head edge = center then
      (resistances (network.color edge))⁻¹ else 0) ≤ (network.toSimpleGraph.degree center : ℝ) / lower := by
    rw [div_eq_mul_inv, ← count_identity, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro edge _
    by_cases incident : network.tail edge = center ∨ network.head edge = center
    · simp only [incident, ↓reduceIte, one_mul]
      simpa only [one_div] using one_div_le_one_div_of_le lower_positive
        (lower_bound (network.color edge))
    · simp only [incident, ↓reduceIte, zero_mul, le_refl]
  have conductance_positive := (div_pos degree_positive upper_positive).trans_le conductance_lower
  constructor
  · simpa only [one_div, inv_div] using
      one_div_le_one_div_of_le conductance_positive conductance_upper
  · simpa only [one_div, inv_div] using
      one_div_le_one_div_of_le (div_pos degree_positive upper_positive) conductance_lower

theorem xiSimpleGraph_degree_positive (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (level : ℕ) (vertex : XiVtx system level) :
    0 < ((XiSimpleGraph system level).degree vertex : ℝ) := by
  letI : Nontrivial (XiVtx system level) :=
    ⟨⟨xiPositiveTerminal system level, xiNegativeTerminal system level, xiTerminals_distinct system level⟩⟩
  obtain ⟨neighbor, adjacent⟩ :=
    (xiSimpleGraph_connected system rule_connected level).preconnected.exists_adj_of_nontrivial vertex
  exact_mod_cast ((XiSimpleGraph system level).degree_pos_iff_exists_adj vertex).mpr ⟨neighbor, adjacent⟩

theorem xiCoarseGroundedDomain_resistance_spectral_bounds (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ coarse steps (center : XiVtx system coarse),
      lower * (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps /
          (XiSimpleGraph system coarse).degree center ≤
        effResToBoundary (XiSimpleGraph system (coarse + steps))
          (xiCoarseGroundedDomain system coarse steps center) (xiForward system coarse steps center) ∧
      effResToBoundary (XiSimpleGraph system (coarse + steps))
          (xiCoarseGroundedDomain system coarse steps center) (xiForward system coarse steps center) ≤
        upper * (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps /
          (XiSimpleGraph system coarse).degree center := by
  obtain ⟨lower, upper, lower_positive, upper_positive, bounds⟩ :=
    system.resistanceSpectralRadius_iterate_bounds rule_connected distance_positive
  have rate_positive := (system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive).1
  refine ⟨lower, upper, lower_positive, upper_positive, fun coarse steps center => ?_⟩
  rw [xiCoarseGroundedDomain_resistance_eq system rule_connected rules_loopless rules_unique planting_nonadjacent]
  exact (XiNetwork system coarse).parallel_resistance_bounds
    (xiNetwork_loopless system rule_connected rules_loopless coarse)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent coarse)
    center (xiSimpleGraph_degree_positive system rule_connected coarse center)
    ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
    (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)
    (mul_pos lower_positive (pow_pos rate_positive steps))
    (mul_pos upper_positive (pow_pos rate_positive steps))
    (fun colour => (bounds steps colour).1) (fun colour => (bounds steps colour).2)

theorem xiIncidentStar_forward_iff (system : EIGSData K) (coarse steps : ℕ)
    (center vertex : XiVtx system coarse) :
    xiIncidentStar system coarse center steps (xiForward system coarse steps vertex) ↔ vertex = center := by
  induction steps with
  | zero => rfl
  | succ steps induction_hypothesis => exact induction_hypothesis

theorem xiIncidentStar_subset_coarseGroundedDomain (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) {vertex : XiVtx system (coarse + steps)}
    (vertex_star : xiIncidentStar system coarse center steps vertex) :
    vertex ∈ xiCoarseGroundedDomain system coarse steps center := by
  classical
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
  rintro image_membership
  obtain ⟨old_vertex, old_other, rfl⟩ := Finset.mem_image.mp image_membership
  exact (Finset.ne_of_mem_erase old_other)
    ((xiIncidentStar_forward_iff system coarse steps center old_vertex).mp vertex_star)

theorem xiSimpleGraph_ball_resistance_spectral_upper (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ coefficient upper : ℝ, 0 < coefficient ∧ 0 < upper ∧
      ∀ coarse steps (center : XiVtx system coarse) (radius : ℝ),
        0 < radius → radius ≤ coefficient * (system.distanceSpectralRadius rule_connected) ^ steps →
        effResToBoundary (XiSimpleGraph system (coarse + steps))
          (finiteGraphBall (XiSimpleGraph system (coarse + steps))
            (xiForward system coarse steps center) radius) (xiForward system coarse steps center) ≤
          upper * (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps /
            (XiSimpleGraph system coarse).degree center := by
  obtain ⟨coefficient, coefficient_positive, containment⟩ :=
    xiSimpleGraph_ball_subset_multistep_star_at_distanceSpectralRadius system rule_connected rules_loopless
      rules_unique distance_positive
  obtain ⟨_, upper, _, upper_positive, resistance_bounds⟩ :=
    xiCoarseGroundedDomain_resistance_spectral_bounds system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  refine ⟨coefficient, upper, coefficient_positive, upper_positive,
    fun coarse steps center radius radius_positive radius_bound => ?_⟩
  have ball_contained : finiteGraphBall (XiSimpleGraph system (coarse + steps))
      (xiForward system coarse steps center) radius ⊆ xiCoarseGroundedDomain system coarse steps center := by
    intro vertex vertex_inside
    apply xiIncidentStar_subset_coarseGroundedDomain system coarse steps center
    exact containment coarse steps center radius radius_positive radius_bound vertex
      (Finset.mem_filter.mp vertex_inside).2
  have center_inside : xiForward system coarse steps center ∈
      finiteGraphBall (XiSimpleGraph system (coarse + steps)) (xiForward system coarse steps center) radius := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [SimpleGraph.dist_self, Nat.cast_zero] using radius_positive⟩
  exact (effResToBoundary_mono_domain (XiSimpleGraph system (coarse + steps))
    (xiSimpleGraph_connected system rule_connected _) ball_contained
    (xiCoarseGroundedDomain_complement_nonempty system coarse steps center) center_inside).trans
    (resistance_bounds coarse steps center).2

end EIGS

#print axioms EIGS.Network.parallel_resistance_bounds
#print axioms EIGS.xiSimpleGraph_degree_positive
#print axioms EIGS.xiCoarseGroundedDomain_resistance_spectral_bounds
#print axioms EIGS.xiIncidentStar_forward_iff
#print axioms EIGS.xiIncidentStar_subset_coarseGroundedDomain
#print axioms EIGS.xiSimpleGraph_ball_resistance_spectral_upper
