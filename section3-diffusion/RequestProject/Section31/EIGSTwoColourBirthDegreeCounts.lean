import RequestProject.Section31.EIGSTwoColourStationaryNormalizedDegree

/-! Actual cardinalities of the two private birth-degree classes of Figure 3.
Both are derived from the literal private-vertex sigma type. Candidate. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section

theorem fintype_card_sigma_predicate {Base : Type*} [Fintype Base]
    {Fiber : Base → Type*} [∀ base, Fintype (Fiber base)]
    (predicate : (Σ base, Fiber base) → Prop) [DecidablePred predicate] :
    Fintype.card {vertex : Σ base, Fiber base // predicate vertex} =
      ∑ base, Fintype.card {vertex : Fiber base // predicate ⟨base, vertex⟩} := by
  let rearrange : {vertex : Σ base, Fiber base // predicate vertex} ≃
      Σ base, {vertex : Fiber base // predicate ⟨base, vertex⟩} :=
    { toFun := fun vertex => ⟨vertex.val.1, ⟨vertex.val.2, vertex.property⟩⟩
      invFun := fun vertex => ⟨⟨vertex.1, vertex.2.val⟩, vertex.2.property⟩
      left_inv := by rintro ⟨⟨base, vertex⟩, property⟩; rfl
      right_inv := by rintro ⟨base, vertex, property⟩; rfl }
  exact (Fintype.card_congr rearrange).trans Fintype.card_sigma

abbrev twoColourBirthDegreeThree (level : ℕ) (vertex : XiNewVertices twoColourSystem level) : Prop :=
  XiCol twoColourSystem.toRuleData level vertex.1 = 0 ∧
    (vertex.2.val = 1 ∨ vertex.2.val = 3)

theorem twoColourSystem_rule_birth_degree_three_count (colour : Fin 2) :
    Fintype.card {vertex : {vertex : Fin 5 // vertex ≠ 0 ∧ vertex ≠ 4} //
      colour = 0 ∧ (vertex.val = 1 ∨ vertex.val = 3)} =
      if colour = 0 then 2 else 0 := by
  fin_cases colour <;> decide

theorem twoColourSystem_rule_birth_degree_two_count (colour : Fin 2) :
    Fintype.card {vertex : {vertex : Fin 5 // vertex ≠ 0 ∧ vertex ≠ 4} //
      ¬ (colour = 0 ∧ (vertex.val = 1 ∨ vertex.val = 3))} =
      if colour = 0 then 1 else 3 := by
  fin_cases colour <;> decide

theorem twoColourSystem_birth_degree_three_count (level : ℕ) :
    Fintype.card {vertex : XiNewVertices twoColourSystem level //
      twoColourBirthDegreeThree level vertex} =
      2 * chiCount twoColourSystem.toRuleData level 0 := by
  unfold twoColourBirthDegreeThree XiNewVertices
  rw [fintype_card_sigma_predicate]
  simp only [chiCount, Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge _
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {vertex : {vertex : Fin 5 // vertex ≠ 0 ∧ vertex ≠ 4} //
    XiCol twoColourSystem.toRuleData level edge = 0 ∧ (vertex.val = 1 ∨ vertex.val = 3)} = _
  rw [Nat.card_eq_fintype_card, twoColourSystem_rule_birth_degree_three_count]
  split_ifs <;> norm_num

theorem twoColourSystem_birth_degree_two_count (level : ℕ) :
    Fintype.card {vertex : XiNewVertices twoColourSystem level //
      ¬ twoColourBirthDegreeThree level vertex} =
      chiCount twoColourSystem.toRuleData level 0 +
        3 * chiCount twoColourSystem.toRuleData level 1 := by
  unfold twoColourBirthDegreeThree XiNewVertices
  rw [fintype_card_sigma_predicate]
  have splitColour (colour : Fin 2) :
      (if colour = 0 then 1 else 3 : ℕ) =
        (if colour = 0 then 1 else 0) + 3 * (if colour = 1 then 1 else 0) := by
    fin_cases colour <;> decide
  simp only [Finset.mul_sum, chiCount, Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {vertex : {vertex : Fin 5 // vertex ≠ 0 ∧ vertex ≠ 4} //
    ¬ (XiCol twoColourSystem.toRuleData level edge = 0 ∧ (vertex.val = 1 ∨ vertex.val = 3))} = _
  rw [Nat.card_eq_fintype_card, twoColourSystem_rule_birth_degree_two_count, splitColour]

end
end EIGS

#print axioms EIGS.twoColourSystem_birth_degree_three_count
#print axioms EIGS.twoColourSystem_birth_degree_two_count
