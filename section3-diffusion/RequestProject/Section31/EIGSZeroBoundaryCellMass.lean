import RequestProject.Section31.EIGSNativeEndpointNorm

/-! Actual descendant-edge allocation of the native squared norm. Each fine
edge belongs to exactly one ancestor, so shared terminal degrees are allocated
exactly. For a skeleton-zero increment these terms have zero terminal value;
no estimate on the mass of a whole closed cell is assumed here. -/

namespace EIGS

open scoped BigOperators

variable {K : ℕ}

noncomputable def xiNativeCellSquareMass (system : EIGSData K)
    (initialLevel offset : ℕ) (ancestor : XiEdge system.toRuleData initialLevel)
    (values : XiVtx system (initialLevel + offset) → ℝ) : ℝ :=
  (∑ edge : XiEdge system.toRuleData (initialLevel + offset),
    if xiEdgeAncestor system initialLevel offset edge = ancestor then
      (values (XiTail system (initialLevel + offset) edge)) ^ 2 +
        (values (XiHead system (initialLevel + offset) edge)) ^ 2 else 0) /
    (2 * totalEdges system.toRuleData (initialLevel + offset))

theorem xiNativeCellSquareMass_nonnegative (system : EIGSData K)
    (initialLevel offset : ℕ) (ancestor : XiEdge system.toRuleData initialLevel)
    (values : XiVtx system (initialLevel + offset) → ℝ) :
    0 ≤ xiNativeCellSquareMass system initialLevel offset ancestor values := by
  classical
  unfold xiNativeCellSquareMass
  positivity

theorem xiFiniteSpeedL2_norm_sq_sum_cells (system : EIGSData K)
    (mass : XiMassParameters system) (initialLevel offset : ℕ)
    (values : XiVtx system (initialLevel + offset) → ℝ) :
    ‖xiFiniteSpeedL2 system mass (initialLevel + offset) values‖ ^ 2 =
      ∑ ancestor : XiEdge system.toRuleData initialLevel,
        xiNativeCellSquareMass system initialLevel offset ancestor values := by
  classical
  rw [xiFiniteSpeedL2_norm_sq_endpoints]
  unfold xiNativeCellSquareMass
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro edge _
  simp

theorem xiNativeCellSquareMass_le_descendant_fraction (system : EIGSData K)
    (initialLevel offset : ℕ) (ancestor : XiEdge system.toRuleData initialLevel)
    (values : XiVtx system (initialLevel + offset) → ℝ) (squareBound : ℝ)
    (endpointBound : ∀ edge : XiEdge system.toRuleData (initialLevel + offset),
      xiEdgeAncestor system initialLevel offset edge = ancestor →
        (values (XiTail system (initialLevel + offset) edge)) ^ 2 ≤ squareBound ∧
        (values (XiHead system (initialLevel + offset) edge)) ^ 2 ≤ squareBound) :
    xiNativeCellSquareMass system initialLevel offset ancestor values ≤
      ((totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset : ℝ) /
        totalEdges system.toRuleData (initialLevel + offset)) * squareBound := by
  classical
  have countSum :
      (∑ edge : XiEdge system.toRuleData (initialLevel + offset),
        if xiEdgeAncestor system initialLevel offset edge = ancestor then
          squareBound + squareBound else 0) =
      (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset : ℝ) *
        (squareBound + squareBound) := by
    rw [← xiDescendant_cardinality system initialLevel offset ancestor]
    simp [Fintype.card_subtype, ← Finset.sum_filter, mul_add]
  calc
    xiNativeCellSquareMass system initialLevel offset ancestor values ≤
        (∑ edge : XiEdge system.toRuleData (initialLevel + offset),
          if xiEdgeAncestor system initialLevel offset edge = ancestor then
            squareBound + squareBound else 0) /
          (2 * totalEdges system.toRuleData (initialLevel + offset)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro edge _
      by_cases descendant : xiEdgeAncestor system initialLevel offset edge = ancestor
      · simpa only [descendant, ↓reduceIte] using add_le_add (endpointBound edge descendant).1 (endpointBound edge descendant).2
      · simp [descendant]
    _ = _ := by rw [countSum]; ring

theorem xiDescendant_fraction_uniform_bound (system : EIGSData K)
    (mass : XiMassParameters system) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ initialLevel offset (ancestor : XiEdge system.toRuleData initialLevel),
      (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset : ℝ) /
        totalEdges system.toRuleData (initialLevel + offset) ≤ constant / mass.rate ^ initialLevel := by
  classical
  obtain ⟨lower, _, lowerPositive, _, originalBounds⟩ :=
    mass_geometric_growth system mass.amplitude_positive mass.eigenpair mass.rate_positive
  have replantedBounds : ∀ colour : Fin K, ∃ lower upper : ℝ,
      0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * mass.rate ^ level ≤ (totalEdges {system.toRuleData with ι := colour} level : ℝ) ∧
      (totalEdges {system.toRuleData with ι := colour} level : ℝ) ≤ upper * mass.rate ^ level := by
    intro colour
    exact mass_geometric_growth {system with initCol := colour}
      mass.amplitude_positive mass.eigenpair mass.rate_positive
  choose childLower childUpper childLowerPositive childUpperPositive childBounds using replantedBounds
  have sumPositive : 0 < ∑ colour, childUpper colour :=
    (childUpperPositive system.initCol).trans_le
      (Finset.single_le_sum (fun colour _ => (childUpperPositive colour).le) (Finset.mem_univ system.initCol))
  refine ⟨(∑ colour, childUpper colour) / lower, div_pos sumPositive lowerPositive, ?_⟩
  intro initialLevel offset ancestor
  have numeratorBound :
      (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset : ℝ) ≤
        (∑ colour, childUpper colour) * mass.rate ^ offset :=
    (childBounds (XiCol system.toRuleData initialLevel ancestor) offset).2.trans
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun colour _ => (childUpperPositive colour).le) (Finset.mem_univ _))
        (pow_pos mass.rate_positive offset).le)
  calc
    (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset : ℝ) /
        totalEdges system.toRuleData (initialLevel + offset) ≤
      ((∑ colour, childUpper colour) * mass.rate ^ offset) /
        totalEdges system.toRuleData (initialLevel + offset) :=
      div_le_div_of_nonneg_right numeratorBound (Nat.cast_nonneg _)
    _ ≤ ((∑ colour, childUpper colour) * mass.rate ^ offset) /
        (lower * mass.rate ^ (initialLevel + offset)) :=
      div_le_div_of_nonneg_left (mul_pos sumPositive (pow_pos mass.rate_positive offset)).le
        (mul_pos lowerPositive (pow_pos mass.rate_positive _)) (originalBounds _).1
    _ = _ := by
      rw [pow_add]
      field_simp [ne_of_gt mass.rate_positive, ne_of_gt lowerPositive] <;> ring

theorem xiNativeCellSquareMass_uniform_bound (system : EIGSData K)
    (mass : XiMassParameters system) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ initialLevel offset (ancestor : XiEdge system.toRuleData initialLevel)
      (values : XiVtx system (initialLevel + offset) → ℝ) (squareBound : ℝ),
      0 ≤ squareBound →
      (∀ edge : XiEdge system.toRuleData (initialLevel + offset),
        xiEdgeAncestor system initialLevel offset edge = ancestor →
          (values (XiTail system (initialLevel + offset) edge)) ^ 2 ≤ squareBound ∧
          (values (XiHead system (initialLevel + offset) edge)) ^ 2 ≤ squareBound) →
      xiNativeCellSquareMass system initialLevel offset ancestor values ≤
        constant / mass.rate ^ initialLevel * squareBound := by
  obtain ⟨constant, constantPositive, fractionBound⟩ := xiDescendant_fraction_uniform_bound system mass
  refine ⟨constant, constantPositive, ?_⟩
  intro initialLevel offset ancestor values squareBound squareBoundNonnegative endpointBound
  exact (xiNativeCellSquareMass_le_descendant_fraction system initialLevel offset ancestor values squareBound endpointBound).trans
    (mul_le_mul_of_nonneg_right (fractionBound initialLevel offset ancestor) squareBoundNonnegative)

end EIGS
