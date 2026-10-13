import RequestProject.Section2StarResistance
import RequestProject.Section31.EIGSNonstationaryHarmonics

/-! The actual Green voltage on the actual recursive incident star equals the
constructed nonstationary trace minimizer of the coarse source spike. -/

namespace EIGS

open scoped BigOperators Classical
open IGS.Sec31

variable {K : ℕ}

theorem xiPotentialValues_delta_supported (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse depth : ℕ) (center : XiVtx system coarse)
    (resistances : Fin K → ℝ) (resistances_positive : ∀ colour, 0 < resistances colour)
    (vertex : XiVtx system (coarse + depth))
    (outside : ¬ xiIncidentStar system coarse center depth vertex) :
    xiPotentialValues system rule_connected coarse depth resistances resistances_positive
      (fun point => if point = center then 1 else 0) vertex = 0 := by
  obtain ⟨extension, extension_old, extension_supported, extension_energy⟩ :=
    exists_xiPotential_iterated_trace_supported system rule_connected coarse depth center resistances resistances_positive
  have extension_minimal : ∀ competitor : XiVtx system (coarse + depth) → ℝ,
      (∀ point, competitor (xiForward system coarse depth point) = if point = center then 1 else 0) →
      ((XiNetwork system (coarse + depth)).potentialNetwork resistances resistances_positive).energy extension ≤
        ((XiNetwork system (coarse + depth)).potentialNetwork resistances resistances_positive).energy competitor := by
    intro competitor competitor_old
    have restriction_equal : (fun point => competitor (xiForward system coarse depth point)) =
        (fun point => if point = center then 1 else 0) := funext competitor_old
    have energy_equal := congrArg
      (((XiNetwork system coarse).potentialNetwork ((system.ruleFamily rule_connected).Psi^[depth] resistances)
        (ruleFamily_Psi_iterate_positive system rule_connected resistances resistances_positive depth)).energy)
      restriction_equal
    exact (extension_energy.trans energy_equal.symm).le.trans
      (xiPotential_iterated_restriction_le system rule_connected coarse depth resistances resistances_positive competitor)
  have extension_equal := xiPotentialValues_unique system rule_connected coarse depth resistances resistances_positive
    (fun point => if point = center then 1 else 0) extension extension_old extension_minimal
  rw [← extension_equal]
  exact extension_supported vertex outside

theorem xiIncidentStar_boundaryVoltageProfile_eq_potentialValues (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse depth : ℕ) (center : XiVtx system coarse) :
    boundaryVoltageProfile (XiSimpleGraph system (coarse + depth))
        (xiIncidentStarDomain system coarse depth center) (xiForward system coarse depth center) =
      xiPotentialValues system rule_connected coarse depth (fun _ => 1) (fun _ => by norm_num)
        (fun point => if point = center then 1 else 0) := by
  classical
  let voltage := boundaryVoltageProfile (XiSimpleGraph system (coarse + depth))
    (xiIncidentStarDomain system coarse depth center) (xiForward system coarse depth center)
  let trace_values := xiPotentialValues system rule_connected coarse depth (fun _ => 1) (fun _ => by norm_num)
    (fun point => if point = center then 1 else 0)
  have voltage_old : ∀ point, voltage (xiForward system coarse depth point) = if point = center then 1 else 0 := by
    intro point
    by_cases point_center : point = center
    · subst point
      rw [if_pos rfl]
      exact boundaryVoltageProfile_source _ (xiSimpleGraph_connected system rule_connected _)
        (xiIncidentStarDomain_complement_nonempty system coarse depth center)
        (xiIncidentStarDomain_center_mem system coarse depth center)
    · rw [if_neg point_center]
      apply boundaryVoltageProfile_zero
      simpa only [xiIncidentStarDomain, Finset.mem_filter, Finset.mem_univ, true_and,
        xiIncidentStar_forward_iff] using point_center
  have trace_old := xiPotentialValues_boundary system rule_connected coarse depth (fun _ => 1)
    (fun _ => by norm_num) (fun point => if point = center then 1 else 0)
  have unit_energy : ∀ values : XiVtx system (coarse + depth) → ℝ,
      ((XiNetwork system (coarse + depth)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values =
        dirichletEnergy (XiSimpleGraph system (coarse + depth)) values :=
    (XiNetwork system (coarse + depth)).unit_potential_energy_eq_dirichletEnergy
      (xiNetwork_loopless system rule_connected rules_loopless _)
      (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent _)
  have voltage_energy :
      ((XiNetwork system (coarse + depth)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy voltage =
        ((XiNetwork system (coarse + depth)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy trace_values := by
    rw [unit_energy voltage, boundaryVoltageProfile_energy _ (xiSimpleGraph_connected system rule_connected _)
      (xiIncidentStarDomain_complement_nonempty system coarse depth center)
      (xiIncidentStarDomain_center_mem system coarse depth center),
      xiIncidentStarDomain_resistance_eq system rule_connected rules_loopless rules_unique planting_nonadjacent, inv_inv]
    rw [xiPotentialValues_energy]
    exact ((XiNetwork system coarse).delta_potential_energy
      (xiNetwork_loopless system rule_connected rules_loopless coarse) _ _ center).symm
  change voltage = trace_values
  apply (XiNetwork system (coarse + depth)).potential_minimum_unique (fun _ => 1) (fun _ => by norm_num)
    (xiSimpleGraph_connected system rule_connected _) (Finset.univ.image (xiForward system coarse depth))
    ⟨xiForward system coarse depth center, by simp⟩ trace_values
  · intro point membership
    obtain ⟨old_point, _, rfl⟩ := Finset.mem_image.mp membership
    exact (voltage_old old_point).trans (trace_old old_point).symm
  · intro _ _; rfl
  · intro competitor competitor_boundary
    rw [voltage_energy]
    apply xiPotentialValues_minimal system rule_connected coarse depth (fun _ => 1) (fun _ => by norm_num)
      (fun point => if point = center then 1 else 0) competitor
    intro point
    exact (competitor_boundary _ (by simp)).trans (trace_old point)
  · intro competitor competitor_boundary
    apply xiPotentialValues_minimal system rule_connected coarse depth (fun _ => 1) (fun _ => by norm_num)
      (fun point => if point = center then 1 else 0) competitor
    intro point
    exact (competitor_boundary _ (by simp)).trans (trace_old point)

end EIGS

#print axioms EIGS.xiPotentialValues_delta_supported
#print axioms EIGS.xiIncidentStar_boundaryVoltageProfile_eq_potentialValues
