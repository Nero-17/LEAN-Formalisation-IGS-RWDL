import RequestProject.Section31.EIGSVertexMarginals

/-! Actual uniform vertex ancestor laws converge against every finite coarse
test, including the separate vanishing coarse-skeleton state. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal Classical

noncomputable section

variable {K : ℕ} (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

include ruleConnected plantingNonadjacent distancePositive

theorem xiVertexCountingMeasure_ancestor_integral_limit (mass : XiMassParameters system)
    (coarseLevel : ℕ) (test : Option (XiEdge system.toRuleData coarseLevel) → ℝ) :
    Tendsto (fun offset => ∫ state, test state ∂
      (xiVertexCountingMeasure system (coarseLevel + offset)).map
        (xiVertexAncestorEdge system coarseLevel offset)) atTop
      (𝓝 (∫ edge, test (some edge) ∂mass.edgeLaw coarseLevel)) := by
  have singletonLimits : ∀ state : Option (XiEdge system.toRuleData coarseLevel),
      Tendsto (fun offset => (((xiVertexCountingMeasure system (coarseLevel + offset)).map
        (xiVertexAncestorEdge system coarseLevel offset)) {state}).toReal) atTop
        (𝓝 (match state with | none => 0 | some edge => (mass.edgeLaw coarseLevel {edge}).toReal)) := by
    intro state
    cases state with
    | none =>
        exact xiVertexCountingMeasure_ancestor_none_limit system ruleConnected
          plantingNonadjacent distancePositive coarseLevel
    | some edge =>
        exact xiVertexCountingMeasure_ancestor_mass_limit system ruleConnected
          plantingNonadjacent distancePositive mass coarseLevel edge
  have sumLimit := tendsto_finset_sum
    (Finset.univ : Finset (Option (XiEdge system.toRuleData coarseLevel)))
    (fun state _ => (singletonLimits state).mul_const (test state))
  simpa only [integral_fintype _ Integrable.of_finite, measureReal_def, smul_eq_mul,
    Fintype.sum_option, zero_mul, zero_add] using sumLimit

theorem xiVertexCountingMeasure_ancestor_test_limit (mass : XiMassParameters system)
    (coarseLevel : ℕ) (test : Option (XiEdge system.toRuleData coarseLevel) → ℝ) :
    Tendsto (fun offset => ∫ vertex,
      test (xiVertexAncestorEdge system coarseLevel offset vertex)
        ∂xiVertexCountingMeasure system (coarseLevel + offset)) atTop
      (𝓝 (∫ address, test (some (xiAddressEdge system coarseLevel address)) ∂mass.addressMeasure)) := by
  have finiteIntegral : ∀ offset,
      (∫ vertex, test (xiVertexAncestorEdge system coarseLevel offset vertex)
        ∂xiVertexCountingMeasure system (coarseLevel + offset)) =
      ∫ state, test state ∂(xiVertexCountingMeasure system (coarseLevel + offset)).map
        (xiVertexAncestorEdge system coarseLevel offset) := by
    intro offset
    exact (integral_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable).symm
  have addressIntegral :
      (∫ address, test (some (xiAddressEdge system coarseLevel address)) ∂mass.addressMeasure) =
      ∫ edge, test (some edge) ∂mass.edgeLaw coarseLevel := by
    rw [← mass.addressMeasure_coordinate coarseLevel]
    have testMeasurable : Measurable (fun edge : XiEdge system.toRuleData coarseLevel =>
        test (some edge)) := Measurable.of_discrete
    exact (integral_map (measurable_xiAddressEdge system coarseLevel).aemeasurable
      testMeasurable.aestronglyMeasurable).symm
  simp_rw [finiteIntegral, addressIntegral]
  exact xiVertexCountingMeasure_ancestor_integral_limit system ruleConnected plantingNonadjacent
    distancePositive mass coarseLevel test

end
end EIGS

#print axioms EIGS.xiVertexCountingMeasure_ancestor_integral_limit
#print axioms EIGS.xiVertexCountingMeasure_ancestor_test_limit

