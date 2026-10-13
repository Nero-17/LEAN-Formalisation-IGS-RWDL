import RequestProject.Section31.EIGSHarmonicFamilyCells
import RequestProject.Section31.EIGSDescendantMassLower

/-! A uniform reverse native norm estimate on genuine harmonic families.
Fixed-depth descendant cells adjacent to the larger endpoint have positive
mass and retain at least half of that endpoint's absolute value. -/

namespace EIGS

open scoped BigOperators

variable {K : ℕ}

private theorem interval_distance_endpoint (first second value endpoint : ℝ)
    (range : min first second ≤ value ∧ value ≤ max first second)
    (incidence : first = endpoint ∨ second = endpoint) : |value - endpoint| ≤ |first - second| := by
  rcases le_total first second with ordered | ordered
  · rw [min_eq_left ordered, max_eq_right ordered] at range
    rw [abs_of_nonpos (sub_nonpos.2 ordered)]
    rcases incidence with rfl | rfl <;> exact abs_le.2 ⟨by linarith [range.1, range.2], by linarith [range.1, range.2]⟩
  · rw [min_eq_right ordered, max_eq_left ordered] at range
    rw [abs_of_nonneg (sub_nonneg.2 ordered)]
    rcases incidence with rfl | rfl <;> exact abs_le.2 ⟨by linarith [range.1, range.2], by linarith [range.1, range.2]⟩

private theorem larger_endpoint_square_lower (endpoint other value : ℝ)
    (larger : |other| ≤ |endpoint|) (near : |value - endpoint| ≤ |endpoint - other| / 4) :
    (endpoint ^ 2 + other ^ 2) / 8 ≤ value ^ 2 := by
  have differenceBound : |endpoint - other| ≤ 2 * |endpoint| :=
    (abs_sub endpoint other).trans (by linarith)
  have triangle : |endpoint| ≤ |value - endpoint| + |value| := by
    have := abs_add_le (endpoint - value) value
    simpa only [sub_add_cancel, abs_sub_comm endpoint value] using this
  have lower : |endpoint| ≤ 2 * |value| := by linarith
  have squareBound := (sq_le_sq₀ (abs_nonneg endpoint) (by positivity : 0 ≤ 2 * |value|)).2 lower
  have otherSquare := (sq_le_sq₀ (abs_nonneg other) (abs_nonneg endpoint)).2 larger
  simp only [sq_abs] at otherSquare
  nlinarith [sq_abs endpoint, sq_abs value]

theorem exists_xiHarmonicFamily_native_lower (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (contractionFactor : ℝ) (factorPositive : 0 < contractionFactor) (factorStrict : contractionFactor < 1)
    (stepContraction : ∀ level (oldValues : XiVtx system level → ℝ)
      (edge : XiEdge system.toRuleData (level + 1)),
      |xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level oldValues (XiTail system (level + 1) edge) -
        xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level oldValues (XiHead system (level + 1) edge)| ≤
        |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor) :
    ∃ constant : ℝ, 0 < constant ∧ ∃ depth : ℕ, ∀ initialLevel
      (values : ∀ level, XiVtx system level → ℝ),
      (∀ level, initialLevel ≤ level → values (level + 1) =
        xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair level (values level)) →
      ∀ offset,
      constant / mass.rate ^ initialLevel *
        (∑ edge : XiEdge system.toRuleData initialLevel,
          ((values initialLevel (XiTail system initialLevel edge)) ^ 2 +
            (values initialLevel (XiHead system initialLevel edge)) ^ 2)) ≤
        ‖xiFiniteSpeedL2 system mass (initialLevel + depth + offset) (values (initialLevel + depth + offset))‖ ^ 2 := by
  classical
  obtain ⟨massConstant, massConstantPositive, cellMassLower⟩ := xiNativeCellSquareMass_uniform_lower system mass
  obtain ⟨depth, depthBound⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 4) factorStrict
  refine ⟨massConstant / (8 * mass.rate ^ depth),
    div_pos massConstantPositive (mul_pos (by norm_num) (pow_pos mass.rate_positive depth)), depth, ?_⟩
  intro initialLevel values stepAgreement offset
  have localDecay := xiHarmonicFamily_local_edge_decay system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair initialLevel values stepAgreement contractionFactor factorPositive.le stepContraction depth
  have oldValues := xiHarmonicFamily_boundary system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair initialLevel values stepAgreement depth
  have selectedExists : ∀ ancestor : XiEdge system.toRuleData initialLevel,
      ∃ selected : XiEdge system.toRuleData (initialLevel + depth),
        xiEdgeAncestor system initialLevel depth selected = ancestor ∧
        ∀ edge : XiEdge system.toRuleData (initialLevel + depth + offset),
          xiEdgeAncestor system (initialLevel + depth) offset edge = selected →
          ((values initialLevel (XiTail system initialLevel ancestor)) ^ 2 +
            (values initialLevel (XiHead system initialLevel ancestor)) ^ 2) / 8 ≤
              (values (initialLevel + depth + offset) (XiTail system (initialLevel + depth + offset) edge)) ^ 2 ∧
          ((values initialLevel (XiTail system initialLevel ancestor)) ^ 2 +
            (values initialLevel (XiHead system initialLevel ancestor)) ^ 2) / 8 ≤
              (values (initialLevel + depth + offset) (XiHead system (initialLevel + depth + offset) edge)) ^ 2 := by
    intro ancestor
    have endpointChoice : ∃ endpoint : XiVtx system initialLevel,
        (XiTail system initialLevel ancestor = endpoint ∨ XiHead system initialLevel ancestor = endpoint) ∧
        ∀ value : ℝ,
          |value - values initialLevel endpoint| ≤
            |values initialLevel (XiTail system initialLevel ancestor) - values initialLevel (XiHead system initialLevel ancestor)| / 4 →
          ((values initialLevel (XiTail system initialLevel ancestor)) ^ 2 +
            (values initialLevel (XiHead system initialLevel ancestor)) ^ 2) / 8 ≤ value ^ 2 := by
      by_cases tailLarger : |values initialLevel (XiHead system initialLevel ancestor)| ≤
          |values initialLevel (XiTail system initialLevel ancestor)|
      · exact ⟨XiTail system initialLevel ancestor, Or.inl rfl,
          fun value near => larger_endpoint_square_lower _ _ value tailLarger near⟩
      · refine ⟨XiHead system initialLevel ancestor, Or.inr rfl, ?_⟩
        intro value near
        have bound := larger_endpoint_square_lower _ _ value (le_of_not_ge tailLarger)
          (by simpa only [abs_sub_comm] using near)
        simpa only [add_comm] using bound
    obtain ⟨endpoint, endpointIncidence, endpointLower⟩ := endpointChoice
    obtain ⟨selected, selectedAncestor, selectedIncidence⟩ := exists_xiDescendant_incident_edge system rulesConnected
      initialLevel depth ancestor endpoint endpointIncidence
    refine ⟨selected, selectedAncestor, ?_⟩
    intro edge ancestorEquality
    have edgeRange := xiHarmonicFamily_descendant_range system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair (initialLevel + depth) values
      (fun level ordered => stepAgreement level (by omega)) offset edge
    rw [ancestorEquality] at edgeRange
    have selectedValues :
        values (initialLevel + depth) (XiTail system (initialLevel + depth) selected) = values initialLevel endpoint ∨
        values (initialLevel + depth) (XiHead system (initialLevel + depth) selected) = values initialLevel endpoint := by
      rcases selectedIncidence with equality | equality
      · exact Or.inl ((congrArg (values (initialLevel + depth)) equality).trans (oldValues endpoint))
      · exact Or.inr ((congrArg (values (initialLevel + depth)) equality).trans (oldValues endpoint))
    have widthBound := localDecay selected
    rw [selectedAncestor] at widthBound
    have widthQuarter := widthBound.trans (mul_le_mul_of_nonneg_right depthBound.le (abs_nonneg _))
    constructor
    · apply endpointLower
      exact (interval_distance_endpoint _ _ _ _ edgeRange.1 selectedValues).trans (by linarith [widthQuarter])
    · apply endpointLower
      exact (interval_distance_endpoint _ _ _ _ edgeRange.2 selectedValues).trans (by linarith [widthQuarter])
  choose selected selectedAncestor selectedBound using selectedExists
  have selectedInjective : Function.Injective selected := by
    intro first second equality
    exact (selectedAncestor first).symm.trans ((congrArg (xiEdgeAncestor system initialLevel depth) equality).trans (selectedAncestor second))
  rw [xiFiniteSpeedL2_norm_sq_sum_cells system mass (initialLevel + depth) offset]
  calc
    _ = ∑ ancestor : XiEdge system.toRuleData initialLevel,
        massConstant / mass.rate ^ (initialLevel + depth) *
          (((values initialLevel (XiTail system initialLevel ancestor)) ^ 2 +
            (values initialLevel (XiHead system initialLevel ancestor)) ^ 2) / 8) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ancestor _
      rw [pow_add]
      field_simp [ne_of_gt mass.rate_positive]
      <;> ring
    _ ≤ ∑ ancestor : XiEdge system.toRuleData initialLevel,
        xiNativeCellSquareMass system (initialLevel + depth) offset (selected ancestor) (values (initialLevel + depth + offset)) := by
      apply Finset.sum_le_sum
      intro ancestor _
      exact cellMassLower (initialLevel + depth) offset (selected ancestor) _ _ (by positivity) (selectedBound ancestor)
    _ ≤ _ := by
      rw [← Finset.sum_image (f := fun edge => xiNativeCellSquareMass system (initialLevel + depth) offset edge
        (values (initialLevel + depth + offset))) (s := Finset.univ) (g := selected)
        (fun first _ second _ equality => selectedInjective equality)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun edge _ _ => xiNativeCellSquareMass_nonnegative system (initialLevel + depth) offset edge _)

end EIGS
