import RequestProject.Section2SupportedTrace
import RequestProject.Section2StarGeometry

/-! Exact resistance of the actual descendant incident star and the resulting
large-ball resistance lower bound on proper actual domains. -/

namespace EIGS

open scoped BigOperators Classical
open IGS.Sec31

variable {K : ℕ}

noncomputable def xiIncidentStarDomain (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) : Finset (XiVtx system (coarse + steps)) :=
  Finset.univ.filter (xiIncidentStar system coarse center steps)

theorem xiIncidentStarDomain_center_mem (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) :
    xiForward system coarse steps center ∈ xiIncidentStarDomain system coarse steps center := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (xiIncidentStar_forward_iff system coarse steps center center).mpr rfl⟩

theorem xiIncidentStarDomain_complement_nonempty (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) : (xiIncidentStarDomain system coarse steps center)ᶜ.Nonempty := by
  obtain ⟨vertex, vertex_outside⟩ := xiCoarseGroundedDomain_complement_nonempty system coarse steps center
  refine ⟨vertex, Finset.mem_compl.mpr (fun vertex_inside => ?_)⟩
  exact (Finset.mem_compl.mp vertex_outside)
    (xiIncidentStar_subset_coarseGroundedDomain system coarse steps center
      (Finset.mem_filter.mp vertex_inside).2)

theorem xiIncidentStarDomain_resistance_eq (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (center : XiVtx system coarse) :
    effResToBoundary (XiSimpleGraph system (coarse + steps))
      (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) =
      (∑ edge : XiEdge system.toRuleData coarse,
        if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
          (((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
            (XiCol system.toRuleData coarse edge))⁻¹ else 0)⁻¹ := by
  classical
  obtain ⟨extension, extension_old, extension_supported, extension_energy⟩ :=
    exists_xiPotential_iterated_trace_supported system rule_connected coarse steps center
      (fun _ => 1) (fun _ => by norm_num)
  have unit_energy : ∀ values : XiVtx system (coarse + steps) → ℝ,
      ((XiNetwork system (coarse + steps)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values =
        dirichletEnergy (XiSimpleGraph system (coarse + steps)) values :=
    (XiNetwork system (coarse + steps)).unit_potential_energy_eq_dirichletEnergy
      (xiNetwork_loopless system rule_connected rules_loopless _)
      (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent _)
  have extension_source : extension (xiForward system coarse steps center) = 1 := by
    simpa only [if_pos rfl] using extension_old center
  have extension_zero : ∀ vertex, vertex ∉ xiIncidentStarDomain system coarse steps center → extension vertex = 0 := by
    intro vertex vertex_outside
    apply extension_supported vertex
    simpa only [xiIncidentStarDomain, Finset.mem_filter, Finset.mem_univ, true_and] using vertex_outside
  have extension_minimum : ∀ competitor : XiVtx system (coarse + steps) → ℝ,
      competitor (xiForward system coarse steps center) = 1 →
      (∀ vertex, vertex ∉ xiIncidentStarDomain system coarse steps center → competitor vertex = 0) →
      dirichletEnergy (XiSimpleGraph system (coarse + steps)) extension ≤
        dirichletEnergy (XiSimpleGraph system (coarse + steps)) competitor := by
    intro competitor competitor_source competitor_zero
    have competitor_old : (fun vertex => competitor (xiForward system coarse steps vertex)) =
        (fun vertex => if vertex = center then 1 else 0) := by
      funext old_vertex
      by_cases old_center : old_vertex = center
      · subst old_vertex
        simpa only [if_pos rfl] using competitor_source
      · rw [if_neg old_center]
        apply competitor_zero
        simpa only [xiIncidentStarDomain, Finset.mem_filter, Finset.mem_univ, true_and,
          xiIncidentStar_forward_iff] using old_center
    have lower_bound := xiPotential_iterated_restriction_le system rule_connected coarse steps
      (fun _ => 1) (fun _ => by norm_num) competitor
    have trace_equal := congrArg
      (((XiNetwork system coarse).potentialNetwork ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)).energy)
      competitor_old
    exact ((unit_energy extension).symm.trans (extension_energy.trans trace_equal.symm)).le.trans
      (lower_bound.trans_eq (unit_energy competitor))
  have resistance_identity := effResToBoundary_eq_inverse_minimum_energy
    (XiSimpleGraph system (coarse + steps)) (xiSimpleGraph_connected system rule_connected _)
    (xiIncidentStarDomain_complement_nonempty system coarse steps center)
    (xiIncidentStarDomain_center_mem system coarse steps center) extension extension_source extension_zero extension_minimum
  have energy_identity : dirichletEnergy (XiSimpleGraph system (coarse + steps)) extension =
      ∑ edge : XiEdge system.toRuleData coarse,
        if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
          (((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
            (XiCol system.toRuleData coarse edge))⁻¹ else 0 := by
    rw [← unit_energy extension, extension_energy]
    exact (XiNetwork system coarse).delta_potential_energy
      (xiNetwork_loopless system rule_connected rules_loopless coarse) _ _ center
  exact resistance_identity.trans (congrArg Inv.inv energy_identity)

theorem xiIncidentStarDomain_resistance_spectral_bounds (system : EIGSData K)
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
          (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) ∧
      effResToBoundary (XiSimpleGraph system (coarse + steps))
          (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) ≤
        upper * (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps /
          (XiSimpleGraph system coarse).degree center := by
  obtain ⟨lower, upper, lower_positive, upper_positive, bounds⟩ :=
    xiCoarseGroundedDomain_resistance_spectral_bounds system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  refine ⟨lower, upper, lower_positive, upper_positive, fun coarse steps center => ?_⟩
  rw [xiIncidentStarDomain_resistance_eq system rule_connected rules_loopless rules_unique planting_nonadjacent,
    ← xiCoarseGroundedDomain_resistance_eq system rule_connected rules_loopless rules_unique planting_nonadjacent]
  exact bounds coarse steps center

theorem xiSimpleGraph_large_ball_resistance_spectral_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ coefficient lower : ℝ, 0 < coefficient ∧ 0 < lower ∧
      ∀ coarse steps (center : XiVtx system coarse) (radius : ℝ),
        coefficient * (system.distanceSpectralRadius rule_connected) ^ steps ≤ radius →
        (finiteGraphBall (XiSimpleGraph system (coarse + steps))
          (xiForward system coarse steps center) radius)ᶜ.Nonempty →
        lower * (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps /
            (XiSimpleGraph system coarse).degree center ≤
          effResToBoundary (XiSimpleGraph system (coarse + steps))
            (finiteGraphBall (XiSimpleGraph system (coarse + steps))
              (xiForward system coarse steps center) radius) (xiForward system coarse steps center) := by
  obtain ⟨lengths, lengths_positive, _, _, eigenpair⟩ :=
    system.metricLengths_spectral_eigenpair rule_connected rules_loopless rules_unique distance_positive
  obtain ⟨coefficient, coefficient_positive, containment⟩ :=
    xiIncidentStar_subset_large_ball_of_eigenpair system rule_connected rules_loopless lengths_positive
      (system.two_le_distanceSpectralRadius rule_connected rules_unique planting_nonadjacent distance_positive) eigenpair
  obtain ⟨lower, _, lower_positive, _, bounds⟩ :=
    xiIncidentStarDomain_resistance_spectral_bounds system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  refine ⟨coefficient, lower, coefficient_positive, lower_positive,
    fun coarse steps center radius radius_bound complement_nonempty => ?_⟩
  apply (bounds coarse steps center).1.trans
  apply effResToBoundary_mono_domain (XiSimpleGraph system (coarse + steps))
    (xiSimpleGraph_connected system rule_connected _)
    (fun vertex membership => containment coarse steps center radius radius_bound vertex (Finset.mem_filter.mp membership).2)
    complement_nonempty (xiIncidentStarDomain_center_mem system coarse steps center)

end EIGS

#print axioms EIGS.xiIncidentStarDomain_center_mem
#print axioms EIGS.xiIncidentStarDomain_complement_nonempty
#print axioms EIGS.xiIncidentStarDomain_resistance_eq
#print axioms EIGS.xiIncidentStarDomain_resistance_spectral_bounds
#print axioms EIGS.xiSimpleGraph_large_ball_resistance_spectral_lower
