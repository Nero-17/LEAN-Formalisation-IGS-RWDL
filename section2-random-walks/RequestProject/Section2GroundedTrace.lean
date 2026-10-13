import RequestProject.Section2BoundaryCapacity
import RequestProject.Section2ForwardComposition
import RequestProject.Section31.EIGSDiscreteTrace

/-! Exact actual multistep resistance when all other coarse vertices are
grounded. The conductances retain their actual nonlinear resistance iterates. -/

namespace EIGS

open scoped BigOperators Classical
open IGS.Sec31

variable {K : ℕ}

theorem xiForward_injective (system : EIGSData K) (coarse steps : ℕ) :
    Function.Injective (xiForward system coarse steps) := by
  induction steps with
  | zero => exact Function.injective_id
  | succ steps induction_hypothesis =>
      intro first second same_image
      exact induction_hypothesis (Sum.inl.inj same_image)

noncomputable def xiCoarseGroundedDomain (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) : Finset (XiVtx system (coarse + steps)) :=
  Finset.univ \ ((Finset.univ.erase center).image (xiForward system coarse steps))

theorem xiCoarseGroundedDomain_center_mem (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) :
    xiForward system coarse steps center ∈ xiCoarseGroundedDomain system coarse steps center := by
  classical
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
  rintro image_membership
  obtain ⟨vertex, vertex_other, same_image⟩ := Finset.mem_image.mp image_membership
  exact (Finset.ne_of_mem_erase vertex_other) ((xiForward_injective system coarse steps) same_image)

theorem xiCoarseGroundedDomain_other_not_mem (system : EIGSData K) (coarse steps : ℕ)
    (center vertex : XiVtx system coarse) (vertex_other : vertex ≠ center) :
    xiForward system coarse steps vertex ∉ xiCoarseGroundedDomain system coarse steps center := by
  classical
  intro vertex_inside
  exact (Finset.mem_sdiff.mp vertex_inside).2
    (Finset.mem_image.mpr ⟨vertex, Finset.mem_erase.mpr ⟨vertex_other, Finset.mem_univ _⟩, rfl⟩)

theorem xiCoarseGroundedDomain_complement_nonempty (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) : (xiCoarseGroundedDomain system coarse steps center)ᶜ.Nonempty := by
  classical
  letI : Nontrivial (XiVtx system coarse) :=
    ⟨⟨xiPositiveTerminal system coarse, xiNegativeTerminal system coarse, xiTerminals_distinct system coarse⟩⟩
  obtain ⟨vertex, vertex_other⟩ := exists_ne center
  exact ⟨xiForward system coarse steps vertex, Finset.mem_compl.mpr
    (xiCoarseGroundedDomain_other_not_mem system coarse steps center vertex vertex_other)⟩

theorem Network.unit_potential_energy_eq_dirichletEnergy (network : Network K)
    (loopless : network.Loopless) (unique_edges : network.EdgesUnique) (values : network.V → ℝ) :
    (network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values =
      dirichletEnergy network.toSimpleGraph values := by
  change (∑ edge, (1 : ℝ)⁻¹ * (values (network.tail edge) - values (network.head edge)) ^ 2) = _
  simp only [inv_one, one_mul]
  exact network.potential_energy_eq_simpleGraph loopless unique_edges values

theorem Network.delta_potential_energy (network : Network K) (loopless : network.Loopless)
    (resistances : Fin K → ℝ) (resistances_positive : ∀ colour, 0 < resistances colour)
    (center : network.V) :
    (network.potentialNetwork resistances resistances_positive).energy
        (fun vertex => if vertex = center then 1 else 0) =
      ∑ edge, if network.tail edge = center ∨ network.head edge = center then
        (resistances (network.color edge))⁻¹ else 0 := by
  change (∑ edge, (resistances (network.color edge))⁻¹ *
    ((if network.tail edge = center then (1 : ℝ) else 0) -
      (if network.head edge = center then 1 else 0)) ^ 2) = _
  apply Finset.sum_congr rfl
  intro edge _
  by_cases tail_center : network.tail edge = center <;>
    by_cases head_center : network.head edge = center
  · exact False.elim (loopless edge (tail_center.trans head_center.symm))
  all_goals simp [tail_center, head_center]

theorem xiCoarseGroundedDomain_resistance_eq (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (center : XiVtx system coarse) :
    effResToBoundary (XiSimpleGraph system (coarse + steps))
      (xiCoarseGroundedDomain system coarse steps center) (xiForward system coarse steps center) =
      (∑ edge : XiEdge system.toRuleData coarse,
        if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
          (((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
            (XiCol system.toRuleData coarse edge))⁻¹ else 0)⁻¹ := by
  classical
  let coarse_values := fun vertex : XiVtx system coarse => if vertex = center then (1 : ℝ) else 0
  obtain ⟨extension, extension_old, extension_energy, minimum⟩ :=
    exists_xiUnit_iterated_trace system rule_connected coarse steps coarse_values
  have fine_loopless := xiNetwork_loopless system rule_connected rules_loopless (coarse + steps)
  have fine_unique := xiNetwork_edges_unique system rule_connected rules_loopless rules_unique
    planting_nonadjacent (coarse + steps)
  have unit_energy : ∀ values : XiVtx system (coarse + steps) → ℝ,
      ((XiNetwork system (coarse + steps)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values =
        dirichletEnergy (XiSimpleGraph system (coarse + steps)) values :=
    (XiNetwork system (coarse + steps)).unit_potential_energy_eq_dirichletEnergy fine_loopless fine_unique
  have extension_source : extension (xiForward system coarse steps center) = 1 := by
    rw [extension_old]
    simp only [coarse_values, if_pos rfl]
  have extension_zero : ∀ vertex, vertex ∉ xiCoarseGroundedDomain system coarse steps center →
      extension vertex = 0 := by
    intro vertex vertex_outside
    have in_image : vertex ∈ (Finset.univ.erase center).image (xiForward system coarse steps) := by
      simpa only [xiCoarseGroundedDomain, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using vertex_outside
    obtain ⟨old_vertex, old_other, rfl⟩ := Finset.mem_image.mp in_image
    rw [extension_old]
    simp only [coarse_values, if_neg (Finset.ne_of_mem_erase old_other)]
  have extension_minimum : ∀ competitor : XiVtx system (coarse + steps) → ℝ,
      competitor (xiForward system coarse steps center) = 1 →
      (∀ vertex, vertex ∉ xiCoarseGroundedDomain system coarse steps center → competitor vertex = 0) →
      dirichletEnergy (XiSimpleGraph system (coarse + steps)) extension ≤
        dirichletEnergy (XiSimpleGraph system (coarse + steps)) competitor := by
    intro competitor competitor_source competitor_zero
    rw [← unit_energy extension, ← unit_energy competitor, extension_energy]
    apply minimum
    intro old_vertex
    by_cases old_center : old_vertex = center
    · subst old_vertex
      simpa only [coarse_values, if_pos rfl] using competitor_source
    · simpa only [coarse_values, if_neg old_center] using
        competitor_zero _ (xiCoarseGroundedDomain_other_not_mem system coarse steps center old_vertex old_center)
  have resistance_identity := effResToBoundary_eq_inverse_minimum_energy
    (XiSimpleGraph system (coarse + steps)) (xiSimpleGraph_connected system rule_connected _)
    (xiCoarseGroundedDomain_complement_nonempty system coarse steps center)
    (xiCoarseGroundedDomain_center_mem system coarse steps center) extension extension_source
    extension_zero extension_minimum
  have energy_identity : dirichletEnergy (XiSimpleGraph system (coarse + steps)) extension =
      ∑ edge : XiEdge system.toRuleData coarse,
        if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
          (((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
            (XiCol system.toRuleData coarse edge))⁻¹ else 0 := by
    rw [← unit_energy extension, extension_energy]
    exact (XiNetwork system coarse).delta_potential_energy
      (xiNetwork_loopless system rule_connected rules_loopless coarse) _ _ center
  exact resistance_identity.trans (congrArg Inv.inv energy_identity)

end EIGS

#print axioms EIGS.xiForward_injective
#print axioms EIGS.xiCoarseGroundedDomain_center_mem
#print axioms EIGS.xiCoarseGroundedDomain_other_not_mem
#print axioms EIGS.xiCoarseGroundedDomain_complement_nonempty
#print axioms EIGS.Network.unit_potential_energy_eq_dirichletEnergy
#print axioms EIGS.Network.delta_potential_energy
#print axioms EIGS.xiCoarseGroundedDomain_resistance_eq
