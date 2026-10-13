import RequestProject.Section31.EIGSZeroBoundaryCellMass
import RequestProject.Section31.EIGSHarmonicLipschitzApproximation

/-! Uniform positive mass of every actual descendant fibre, with its original
ancestor scale. This uses only actual replanted edge-count growth. -/

namespace EIGS

open scoped BigOperators

variable {K : ℕ}

theorem xiDescendant_fraction_uniform_lower (system : EIGSData K)
    (mass : XiMassParameters system) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ initialLevel offset (ancestor : XiEdge system.toRuleData initialLevel),
      constant / mass.rate ^ initialLevel ≤
      (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset : ℝ) /
        totalEdges system.toRuleData (initialLevel + offset) := by
  classical
  obtain ⟨originalLower, originalUpper, originalLowerPositive, originalUpperPositive, originalBounds⟩ :=
    mass_geometric_growth system mass.amplitude_positive mass.eigenpair mass.rate_positive
  have replantedBounds : ∀ colour : Fin K, ∃ lower upper : ℝ,
      0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * mass.rate ^ level ≤ (totalEdges {system.toRuleData with ι := colour} level : ℝ) ∧
      (totalEdges {system.toRuleData with ι := colour} level : ℝ) ≤ upper * mass.rate ^ level := by
    intro colour
    exact mass_geometric_growth {system with initCol := colour}
      mass.amplitude_positive mass.eigenpair mass.rate_positive
  choose childLower childUpper childLowerPositive childUpperPositive childBounds using replantedBounds
  obtain ⟨lower, lowerPositive, lowerBound⟩ := exists_positive_colour_length_lower_bound system childLower childLowerPositive
  refine ⟨lower / originalUpper, div_pos lowerPositive originalUpperPositive, ?_⟩
  intro initialLevel offset ancestor
  have numeratorBound : lower * mass.rate ^ offset ≤
      (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset : ℝ) :=
    (mul_le_mul_of_nonneg_right (lowerBound _) (pow_pos mass.rate_positive offset).le).trans (childBounds _ offset).1
  have denominatorPositive : 0 < (totalEdges system.toRuleData (initialLevel + offset) : ℝ) :=
    (mul_pos originalLowerPositive (pow_pos mass.rate_positive _)).trans_le (originalBounds _).1
  calc
    (lower / originalUpper) / mass.rate ^ initialLevel =
        (lower * mass.rate ^ offset) / (originalUpper * mass.rate ^ (initialLevel + offset)) := by
      rw [pow_add]
      field_simp [ne_of_gt originalUpperPositive, ne_of_gt mass.rate_positive]
    _ ≤ (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset : ℝ) /
        (originalUpper * mass.rate ^ (initialLevel + offset)) :=
      div_le_div_of_nonneg_right numeratorBound (mul_pos originalUpperPositive (pow_pos mass.rate_positive _)).le
    _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) denominatorPositive (originalBounds _).2

theorem xiNativeCellSquareMass_ge_descendant_fraction (system : EIGSData K)
    (initialLevel offset : ℕ) (ancestor : XiEdge system.toRuleData initialLevel)
    (values : XiVtx system (initialLevel + offset) → ℝ) (squareBound : ℝ)
    (endpointBound : ∀ edge : XiEdge system.toRuleData (initialLevel + offset),
      xiEdgeAncestor system initialLevel offset edge = ancestor →
        squareBound ≤ (values (XiTail system (initialLevel + offset) edge)) ^ 2 ∧
        squareBound ≤ (values (XiHead system (initialLevel + offset) edge)) ^ 2) :
    ((totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset : ℝ) /
      totalEdges system.toRuleData (initialLevel + offset)) * squareBound ≤
      xiNativeCellSquareMass system initialLevel offset ancestor values := by
  classical
  have countSum :
      (∑ edge : XiEdge system.toRuleData (initialLevel + offset),
        if xiEdgeAncestor system initialLevel offset edge = ancestor then squareBound + squareBound else 0) =
      (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset : ℝ) *
        (squareBound + squareBound) := by
    rw [← xiDescendant_cardinality system initialLevel offset ancestor]
    simp [Fintype.card_subtype, ← Finset.sum_filter, mul_add]
  calc
    _ = (∑ edge : XiEdge system.toRuleData (initialLevel + offset),
        if xiEdgeAncestor system initialLevel offset edge = ancestor then squareBound + squareBound else 0) /
      (2 * totalEdges system.toRuleData (initialLevel + offset)) := by rw [countSum]; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro edge _
      by_cases descendant : xiEdgeAncestor system initialLevel offset edge = ancestor
      · simpa only [descendant, ↓reduceIte] using add_le_add (endpointBound edge descendant).1 (endpointBound edge descendant).2
      · simp [descendant]

theorem xiNativeCellSquareMass_uniform_lower (system : EIGSData K)
    (mass : XiMassParameters system) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ initialLevel offset (ancestor : XiEdge system.toRuleData initialLevel)
      (values : XiVtx system (initialLevel + offset) → ℝ) (squareBound : ℝ),
      0 ≤ squareBound →
      (∀ edge : XiEdge system.toRuleData (initialLevel + offset),
        xiEdgeAncestor system initialLevel offset edge = ancestor →
          squareBound ≤ (values (XiTail system (initialLevel + offset) edge)) ^ 2 ∧
          squareBound ≤ (values (XiHead system (initialLevel + offset) edge)) ^ 2) →
      constant / mass.rate ^ initialLevel * squareBound ≤
        xiNativeCellSquareMass system initialLevel offset ancestor values := by
  obtain ⟨constant, constantPositive, fractionBound⟩ := xiDescendant_fraction_uniform_lower system mass
  refine ⟨constant, constantPositive, ?_⟩
  intro initialLevel offset ancestor values squareBound squareBoundNonnegative endpointBound
  exact (mul_le_mul_of_nonneg_right (fractionBound initialLevel offset ancestor) squareBoundNonnegative).trans
    (xiNativeCellSquareMass_ge_descendant_fraction system initialLevel offset ancestor values squareBound endpointBound)

end EIGS
