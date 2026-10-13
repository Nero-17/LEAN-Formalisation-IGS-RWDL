import RequestProject.Section2FirstStepTrace
import RequestProject.Section2StarVoltageProfile

/-! Actual unit-trace composition and the star Green voltage at the same
native fine level. All trace minimizers are constructed from the real network. -/

namespace EIGS

open scoped Classical

variable {K : ℕ}

theorem xiUnitPotentialAt_eq_potentialValues (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse depth : ℕ) (old_values : XiVtx system coarse → ℝ) :
    xiUnitPotentialAt system rule_connected coarse (coarse + depth) (Nat.le_add_right _ _) old_values =
      xiPotentialValues system rule_connected coarse depth (fun _ => 1) (fun _ => by norm_num) old_values := by
  apply xiPotentialValues_unique system rule_connected coarse depth (fun _ => 1) (fun _ => by norm_num) old_values
  · intro vertex
    rw [← xiVertexInclusion_eq_forward]
    exact xiUnitPotentialAt_boundary system rule_connected coarse (coarse + depth) _ old_values vertex
  · intro competitor competitor_old
    apply xiUnitPotentialAt_minimal system rule_connected coarse (coarse + depth) _ old_values competitor
    intro vertex
    rw [xiVertexInclusion_eq_forward]
    exact competitor_old vertex

theorem xiUnitPotentialAt_first_decomposition (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse depth : ℕ) (old_values : XiVtx system coarse → ℝ) :
    xiUnitPotentialAt system rule_connected coarse ((coarse + 1) + depth) (by omega) old_values =
      xiPotentialValues system rule_connected (coarse + 1) depth (fun _ => 1) (fun _ => by norm_num)
        (xiPotentialStep system rule_connected ((system.ruleFamily rule_connected).Psi^[depth] (fun _ => 1))
          (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) depth)
          coarse old_values) := by
  have decomposition := xiUnitPotentialAt_eq_mesoscopic_potentialValues system rule_connected
    coarse (coarse + 1) depth (Nat.le_add_right _ _) old_values
  have first_restriction := xiUnitPotentialAt_first_restriction system rule_connected coarse depth old_values
  exact decomposition.trans (congrArg
    (xiPotentialValues system rule_connected (coarse + 1) depth (fun _ => 1) (fun _ => by norm_num)) first_restriction)

theorem xiIncidentStar_boundaryVoltageProfile_eq_unitPotentialAt (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse depth : ℕ) (center : XiVtx system coarse) :
    boundaryVoltageProfile (XiSimpleGraph system (coarse + depth))
        (xiIncidentStarDomain system coarse depth center) (xiForward system coarse depth center) =
      xiUnitPotentialAt system rule_connected coarse (coarse + depth) (Nat.le_add_right _ _)
        (fun point => if point = center then 1 else 0) :=
  (xiIncidentStar_boundaryVoltageProfile_eq_potentialValues system rule_connected rules_loopless rules_unique
    planting_nonadjacent coarse depth center).trans
      (xiUnitPotentialAt_eq_potentialValues system rule_connected coarse depth _).symm

end EIGS

#print axioms EIGS.xiUnitPotentialAt_eq_potentialValues
#print axioms EIGS.xiUnitPotentialAt_first_decomposition
#print axioms EIGS.xiIncidentStar_boundaryVoltageProfile_eq_unitPotentialAt
