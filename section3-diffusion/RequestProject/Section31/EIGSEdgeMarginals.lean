import RequestProject.Section31.EIGSEdgeDescendants
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual ancestor-marginal integration, for the geometric projection step. -/

namespace EIGS.XiMassParameters

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section

variable {K : ℕ} {system : EIGSData K} (parameters : XiMassParameters system)

theorem edgeLaw_singleton (level : ℕ) (edge : XiEdge system.toRuleData level) :
    parameters.edgeLaw level {edge} = ENNReal.ofReal (parameters.edgeWeight level edge) := by
  exact (parameters.edgePMF level).toMeasure_apply_singleton edge (measurableSet_singleton edge)

theorem addressMeasure_coordinate_singleton (level : ℕ) (edge : XiEdge system.toRuleData level) :
    parameters.addressMeasure {address | xiAddressEdge system level address = edge} =
      parameters.edgeLaw level {edge} := by
  rw [parameters.addressMeasure_cylinder, parameters.edgeLaw_singleton]
  rfl

/-- Integrals of every finite-level test function converge on the actual ancestor laws. -/
theorem uniformEdgeMeasure_ancestor_integral_limit (initialLevel : ℕ)
    (test : XiEdge system.toRuleData initialLevel → ℝ) :
    Tendsto (fun offset => ∫ edge, test edge ∂
      (parameters.uniformEdgeMeasure (initialLevel + offset)).map
        (xiEdgeAncestor system initialLevel offset))
      atTop (𝓝 (∫ edge, test edge ∂parameters.edgeLaw initialLevel)) := by
  have singleton_limits : ∀ edge : XiEdge system.toRuleData initialLevel,
      Tendsto (fun offset =>
        (((parameters.uniformEdgeMeasure (initialLevel + offset)).map
          (xiEdgeAncestor system initialLevel offset)) {edge}).toReal)
        atTop (𝓝 (parameters.edgeLaw initialLevel {edge}).toReal) := by
    intro edge
    simpa only [parameters.addressMeasure_coordinate_singleton] using
      parameters.uniformEdgeMeasure_ancestor_mass_limit initialLevel edge
  have sum_limit := tendsto_finset_sum (Finset.univ : Finset (XiEdge system.toRuleData initialLevel))
    (fun edge _ => (singleton_limits edge).mul_const (test edge))
  simpa only [integral_fintype _ Integrable.of_finite, measureReal_def, smul_eq_mul] using sum_limit

/-- The same convergence expressed directly on the original uniform fine edges
and on the independently constructed compatible infinite addresses. -/
theorem uniformEdgeMeasure_ancestor_test_limit (initialLevel : ℕ)
    (test : XiEdge system.toRuleData initialLevel → ℝ) :
    Tendsto (fun offset => ∫ edge,
      test (xiEdgeAncestor system initialLevel offset edge)
        ∂parameters.uniformEdgeMeasure (initialLevel + offset))
      atTop (𝓝 (∫ address, test (xiAddressEdge system initialLevel address)
        ∂parameters.addressMeasure)) := by
  have fine_integral : ∀ offset,
      (∫ edge, test (xiEdgeAncestor system initialLevel offset edge)
        ∂parameters.uniformEdgeMeasure (initialLevel + offset)) =
      (∫ edge, test edge ∂(parameters.uniformEdgeMeasure (initialLevel + offset)).map
        (xiEdgeAncestor system initialLevel offset)) := by
    intro offset
    exact (integral_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable).symm
  have address_integral :
      (∫ address, test (xiAddressEdge system initialLevel address) ∂parameters.addressMeasure) =
      (∫ edge, test edge ∂parameters.edgeLaw initialLevel) := by
    rw [← parameters.addressMeasure_coordinate initialLevel]
    exact (integral_map (measurable_xiAddressEdge system initialLevel).aemeasurable
      Measurable.of_discrete.aestronglyMeasurable).symm
  simp_rw [fine_integral, address_integral]
  exact parameters.uniformEdgeMeasure_ancestor_integral_limit initialLevel test

end
end EIGS.XiMassParameters
