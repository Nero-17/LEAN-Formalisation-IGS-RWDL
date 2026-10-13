import RequestProject.Section2RulePositiveBranch
import RequestProject.Section31.EIGSNonstationaryHarmonics
import RequestProject.Section2ConcreteSimplicity

/-! A uniformly positive genuine first-generation branch in every actual
coarse edge incident to the source. The voltage is the constructed trace
minimizer with the actual reverse Psi-iterate resistance. -/

namespace EIGS

open IGS.Sec31
open scoped Classical

variable {K : ℕ}

theorem xiPotentialStep_restricted_minimal (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (resistances : Fin K → ℝ) (resistances_positive : ∀ colour, 0 < resistances colour)
    (coarse : ℕ) (old_values : XiVtx system coarse → ℝ) (edge : XiEdge system.toRuleData coarse)
    (competitor : (system.rule (XiCol system.toRuleData coarse edge)).V → ℝ)
    (competitor_plus : competitor (system.plantPlus (XiCol system.toRuleData coarse edge)) = old_values (XiTail system coarse edge))
    (competitor_minus : competitor (system.plantMinus (XiCol system.toRuleData coarse edge)) = old_values (XiHead system coarse edge)) :
    ((system.ruleNetwork (XiCol system.toRuleData coarse edge)).potentialNetwork resistances resistances_positive).energy
      (fun vertex => xiPotentialStep system rule_connected resistances resistances_positive coarse old_values
        (embedRuleVtx system coarse edge (XiTail system coarse edge) (XiHead system coarse edge) vertex)) ≤
      ((system.ruleNetwork (XiCol system.toRuleData coarse edge)).potentialNetwork resistances resistances_positive).energy competitor := by
  classical
  have profiles_exist := fun colour =>
    (system.ruleNetwork colour).exists_minimum_potential_energy_eq_inverse_effRes resistances resistances_positive
      (rule_connected colour) (system.plantPlus colour) (system.plantMinus colour) (system.plant_ne colour)
  choose profiles profiles_plus profiles_minus profiles_minimal profiles_energy using profiles_exist
  have restriction_equality :
      (fun vertex => xiPotentialStep system rule_connected resistances resistances_positive coarse old_values
        (embedRuleVtx system coarse edge (XiTail system coarse edge) (XiHead system coarse edge) vertex)) =
      (fun vertex => old_values (XiHead system coarse edge) +
        (old_values (XiTail system coarse edge) - old_values (XiHead system coarse edge)) *
          profiles (XiCol system.toRuleData coarse edge) vertex) := by
    rw [xiPotentialStep_eq_affine_profiles system rule_connected resistances resistances_positive
      profiles profiles_plus profiles_minus profiles_minimal]
    funext vertex
    exact (XiNetwork system coarse).substAffineProfiles_restrict (system.ruleFamily rule_connected)
      profiles profiles_plus profiles_minus old_values edge vertex
  refine (congrArg
    (((system.ruleNetwork (XiCol system.toRuleData coarse edge)).potentialNetwork resistances resistances_positive).energy)
    restriction_equality).le.trans ?_
  apply ((system.ruleNetwork (XiCol system.toRuleData coarse edge)).potentialNetwork resistances resistances_positive).min_affine
    {system.plantPlus (XiCol system.toRuleData coarse edge), system.plantMinus (XiCol system.toRuleData coarse edge)}
    (profiles (XiCol system.toRuleData coarse edge)) (profiles (XiCol system.toRuleData coarse edge))
    (old_values (XiHead system coarse edge))
    (old_values (XiTail system coarse edge) - old_values (XiHead system coarse edge))
  · intro trial trial_boundary
    apply profiles_minimal _ trial
    · simpa [profiles_plus] using trial_boundary (system.plantPlus _) (by simp)
    · simpa [profiles_minus] using trial_boundary (system.plantMinus _) (by simp)
  · intro vertex membership
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using membership :
      vertex = system.plantPlus (XiCol system.toRuleData coarse edge) ∨
        vertex = system.plantMinus (XiCol system.toRuleData coarse edge)) with plus_eq | minus_eq
    · subst vertex
      rw [competitor_plus, profiles_plus]
      ring
    · subst vertex
      rw [competitor_minus, profiles_minus]
      ring

theorem xiPotentialStep_positive_incident_child (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower_voltage : ℝ, 0 < lower_voltage ∧ ∀ coarse steps (center : XiVtx system coarse)
      (edge : XiEdge system.toRuleData coarse),
      XiTail system coarse edge = center ∨ XiHead system coarse edge = center →
      ∃ child : (system.rule (XiCol system.toRuleData coarse edge)).E,
        lower_voltage ≤ xiPotentialStep system rule_connected
          ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
          (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)
          coarse (fun vertex => if vertex = center then 1 else 0)
          (XiTail system (coarse + 1) ⟨edge, child⟩) ∧
        lower_voltage ≤ xiPotentialStep system rule_connected
          ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
          (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)
          coarse (fun vertex => if vertex = center then 1 else 0)
          (XiHead system (coarse + 1) ⟨edge, child⟩) := by
  obtain ⟨lower_voltage, lower_positive, _, branch_exists⟩ :=
    rule_Psi_positive_incident_edge system rule_connected distance_positive
  refine ⟨lower_voltage, lower_positive, fun coarse steps center edge incident => ?_⟩
  let local_values := fun vertex => xiPotentialStep system rule_connected
    ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
    (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)
    coarse (fun vertex => if vertex = center then 1 else 0)
    (embedRuleVtx system coarse edge (XiTail system coarse edge) (XiHead system coarse edge) vertex)
  have plus_value : local_values (system.plantPlus (XiCol system.toRuleData coarse edge)) =
      (if XiTail system coarse edge = center then 1 else 0) := by
    dsimp [local_values]
    rw [embedRuleVtx_plantPlus, xiPotentialStep_old]
  have minus_value : local_values (system.plantMinus (XiCol system.toRuleData coarse edge)) =
      (if XiHead system coarse edge = center then 1 else 0) := by
    dsimp [local_values]
    rw [embedRuleVtx_plantMinus, xiPotentialStep_old]
  have terminals_distinct := system.plant_ne (XiCol system.toRuleData coarse edge)
  have endpoints_distinct := xiNetwork_loopless system rule_connected rules_loopless coarse edge
  have local_minimal := xiPotentialStep_restricted_minimal system rule_connected
    ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
    (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)
    coarse (fun vertex => if vertex = center then 1 else 0) edge
  have positive_child : ∃ child : (system.rule (XiCol system.toRuleData coarse edge)).E,
      lower_voltage ≤ local_values ((system.rule (XiCol system.toRuleData coarse edge)).tail child) ∧
        lower_voltage ≤ local_values ((system.rule (XiCol system.toRuleData coarse edge)).head child) := by
    rcases incident with tail_center | head_center
    · have head_not_center : XiHead system coarse edge ≠ center := fun same => endpoints_distinct (tail_center.trans same.symm)
      have source_value : local_values (system.plantPlus _) = 1 := by simpa only [tail_center, if_pos rfl] using plus_value
      have sink_value : local_values (system.plantMinus _) = 0 := by simpa only [if_neg head_not_center] using minus_value
      obtain ⟨child, _, tail_lower, head_lower⟩ := branch_exists (XiCol system.toRuleData coarse edge) steps
        (system.plantPlus _) (system.plantMinus _) local_values terminals_distinct (planting_nonadjacent _)
        source_value sink_value (fun trial trial_plus trial_minus => local_minimal trial
          (by simpa only [tail_center, if_pos rfl] using trial_plus)
          (by simpa only [if_neg head_not_center] using trial_minus))
      exact ⟨child, tail_lower, head_lower⟩
    · have tail_not_center : XiTail system coarse edge ≠ center := fun same => endpoints_distinct (same.trans head_center.symm)
      have source_value : local_values (system.plantMinus _) = 1 := by simpa only [head_center, if_pos rfl] using minus_value
      have sink_value : local_values (system.plantPlus _) = 0 := by simpa only [if_neg tail_not_center] using plus_value
      obtain ⟨child, _, tail_lower, head_lower⟩ := branch_exists (XiCol system.toRuleData coarse edge) steps
        (system.plantMinus _) (system.plantPlus _) local_values terminals_distinct.symm
        (fun adjacency => planting_nonadjacent _ adjacency.symm)
        source_value sink_value (fun trial trial_minus trial_plus => local_minimal trial
          (by simpa only [if_neg tail_not_center] using trial_plus)
          (by simpa only [head_center, if_pos rfl] using trial_minus))
      exact ⟨child, tail_lower, head_lower⟩
  obtain ⟨child, tail_lower, head_lower⟩ := positive_child
  refine ⟨child, ?_, ?_⟩
  · rw [XiTail_succ]
    exact tail_lower
  · rw [XiHead_succ]
    exact head_lower

end EIGS

#print axioms EIGS.xiPotentialStep_restricted_minimal
#print axioms EIGS.xiPotentialStep_positive_incident_child
