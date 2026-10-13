import RequestProject.Section2Concrete
import RequestProject.Section2MatrixPerron

/-! Mass growth on the original rule system, with its Perron vector constructed. -/

namespace EIGS

open scoped BigOperators

variable {K : ℕ}

theorem rule_contains_each_colour (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (ruleColour edgeColour : Fin K) :
    ∃ edge : (system.rule ruleColour).E, (system.rule ruleColour).col edge = edgeColour := by
  by_contra no_colour
  push_neg at no_colour
  have graph_eq : (system.ruleNetwork ruleColour).withoutColour edgeColour =
      ruleSG system ruleColour := by
    ext source sink
    constructor
    · rintro ⟨distinct, forward | reverse⟩
      · obtain ⟨edge, colour_ne, tail_eq, head_eq⟩ := forward
        exact ⟨distinct, Or.inl ⟨edge, tail_eq, head_eq⟩⟩
      · obtain ⟨edge, colour_ne, tail_eq, head_eq⟩ := reverse
        exact ⟨distinct, Or.inr ⟨edge, tail_eq, head_eq⟩⟩
    · rintro ⟨distinct, forward | reverse⟩
      · obtain ⟨edge, tail_eq, head_eq⟩ := forward
        exact ⟨distinct, Or.inl ⟨edge, no_colour edge, tail_eq, head_eq⟩⟩
      · obtain ⟨edge, tail_eq, head_eq⟩ := reverse
        exact ⟨distinct, Or.inr ⟨edge, no_colour edge, tail_eq, head_eq⟩⟩
  apply distance_positive ruleColour edgeColour
  rw [graph_eq]
  exact rule_connected ruleColour (system.plantPlus ruleColour) (system.plantMinus ruleColour)

theorem massMatrixR_positive (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∀ ruleColour edgeColour, 0 < massMatrixR system.toRuleData ruleColour edgeColour := by
  intro ruleColour edgeColour
  obtain ⟨edge, colour_eq⟩ := rule_contains_each_colour system rule_connected distance_positive
    ruleColour edgeColour
  apply Nat.cast_pos.mpr
  apply Finset.card_pos.mpr
  exact ⟨edge, by simpa [EIGSData.toRuleData] using colour_eq⟩

theorem massMatrix_positive_eigenpair (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ (vector : Fin K → ℝ) (rate : ℝ),
      (∀ colour, 0 < vector colour) ∧ 0 < rate ∧ (∑ colour, vector colour) = 1 ∧
        (massMatrixR system.toRuleData).mulVec vector = rate • vector := by
  exact positive_matrix_eigenpair
    (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt)
    (massMatrixR system.toRuleData) (massMatrixR_positive system rule_connected distance_positive)

theorem eigs_mass_growth_from_rules (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ rate lower upper : ℝ, 0 < rate ∧ 0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * rate ^ level ≤ (totalEdges system.toRuleData level : ℝ) ∧
        (totalEdges system.toRuleData level : ℝ) ≤ upper * rate ^ level := by
  obtain ⟨vector, rate, vector_positive, rate_positive, normalized, eigenpair⟩ :=
    massMatrix_positive_eigenpair system rule_connected distance_positive
  obtain ⟨lower, upper, lower_positive, upper_positive, growth⟩ :=
    mass_geometric_growth system vector_positive eigenpair rate_positive
  exact ⟨rate, lower, upper, rate_positive, lower_positive, upper_positive, growth⟩

end EIGS
