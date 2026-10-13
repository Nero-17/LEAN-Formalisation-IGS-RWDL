import RequestProject.Section2Concrete

/-! The canonical positive eigenvalue of the actual nonlinear Thomson map,
constructed from the original distance-positive rules. -/

namespace EIGS.EIGSData

open scoped BigOperators

variable {K : ℕ}

noncomputable def resistanceSpectralRadius (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) : ℝ :=
  Classical.choose ((system.connectedRuleSystem rule_connected).distance_positive_eigenvalue_exists_unique
    (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt) distance_positive)

theorem resistanceSpectralRadius_positive_eigenpair (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    0 < system.resistanceSpectralRadius rule_connected distance_positive ∧
      ∃ vector : Fin K → ℝ, (∀ colour, 0 < vector colour) ∧
        (system.ruleFamily rule_connected).Psi vector =
          system.resistanceSpectralRadius rule_connected distance_positive • vector := by
  exact (Classical.choose_spec
    ((system.connectedRuleSystem rule_connected).distance_positive_eigenvalue_exists_unique
      (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt) distance_positive)).1

theorem resistanceSpectralRadius_eq_of_positive_eigenpair (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    {rate : ℝ} (rate_positive : 0 < rate) {vector : Fin K → ℝ}
    (vector_positive : ∀ colour, 0 < vector colour)
    (eigenpair : (system.ruleFamily rule_connected).Psi vector = rate • vector) :
    rate = system.resistanceSpectralRadius rule_connected distance_positive := by
  exact (Classical.choose_spec
    ((system.connectedRuleSystem rule_connected).distance_positive_eigenvalue_exists_unique
      (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt) distance_positive)).2 rate
    ⟨rate_positive, vector, vector_positive, eigenpair⟩

theorem resistanceSpectralRadius_iterate_bounds (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ steps colour,
      lower * (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps ≤
          (system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1) colour ∧
      (system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1) colour ≤
        upper * (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps := by
  obtain ⟨rate_positive, vector, vector_positive, eigenpair⟩ :=
    system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive
  obtain ⟨lower, upper, lower_positive, upper_positive, bounds⟩ :=
    (system.connectedRuleSystem rule_connected).toRenormMap.iterate_one_two_sided
      vector_positive rate_positive eigenpair
  refine ⟨lower, upper, lower_positive, upper_positive, fun steps colour => ?_⟩
  simpa only [ruleFamily_Psi] using bounds steps colour

end EIGS.EIGSData

#print axioms EIGS.EIGSData.resistanceSpectralRadius_positive_eigenpair
#print axioms EIGS.EIGSData.resistanceSpectralRadius_eq_of_positive_eigenpair
#print axioms EIGS.EIGSData.resistanceSpectralRadius_iterate_bounds
