import RequestProject.Section31.EIGSZeroBoundaryCellMass
import RequestProject.Section31.EIGSNonstationaryHarmonics

/-! A uniform native norm bound for actual nonstationary harmonic extensions.
The proof combines their proved endpoint interval property with exact allocation
of the actual speed measure to descendant edges. -/

namespace EIGS

open scoped BigOperators

variable {K : ℕ}

theorem xiEdgeAncestor_eq_xiAncestorEdge (system : EIGSData K)
    (initialLevel offset : ℕ) (edge : XiEdge system.toRuleData (initialLevel + offset)) :
    xiEdgeAncestor system initialLevel offset edge = xiAncestorEdge system initialLevel offset edge := by
  induction offset with
  | zero => rfl
  | succ offset induction => exact induction edge.1

private theorem square_le_endpoint_squares (first second value : ℝ)
    (lower : min first second ≤ value) (upper : value ≤ max first second) :
    value ^ 2 ≤ first ^ 2 + second ^ 2 := by
  have ordered : ∀ first second : ℝ, first ≤ value → value ≤ second →
      value ^ 2 ≤ first ^ 2 + second ^ 2 := by
    intro first second lower upper
    by_cases nonnegative : 0 ≤ value
    · have squareBound := (sq_le_sq₀ nonnegative (nonnegative.trans upper)).2 upper
      linarith [sq_nonneg first]
    · have nonpositive : value ≤ 0 := le_of_not_ge nonnegative
      have squareBound := (sq_le_sq₀ (neg_nonneg.2 nonpositive)
        (neg_nonneg.2 (lower.trans nonpositive))).2 (neg_le_neg lower)
      nlinarith [sq_nonneg second]
  rcases le_total first second with endpointsOrdered | endpointsOrdered
  · exact ordered first second (by simpa [min_eq_left endpointsOrdered] using lower)
      (by simpa [max_eq_right endpointsOrdered] using upper)
  · simpa [add_comm] using ordered second first
      (by simpa [min_eq_right endpointsOrdered] using lower)
      (by simpa [max_eq_left endpointsOrdered] using upper)

theorem exists_xiPotentialValues_native_norm_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ initialLevel offset
      (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
      (initialValues : XiVtx system initialLevel → ℝ),
      ‖xiFiniteSpeedL2 system mass (initialLevel + offset)
        (xiPotentialValues system rulesConnected initialLevel offset resistances resistancesPositive initialValues)‖ ^ 2 ≤
      constant / mass.rate ^ initialLevel *
        ∑ edge : XiEdge system.toRuleData initialLevel,
          ((initialValues (XiTail system initialLevel edge)) ^ 2 +
            (initialValues (XiHead system initialLevel edge)) ^ 2) := by
  classical
  obtain ⟨constant, constantPositive, cellBound⟩ := xiNativeCellSquareMass_uniform_bound system mass
  refine ⟨constant, constantPositive, ?_⟩
  intro initialLevel offset resistances resistancesPositive initialValues
  rw [xiFiniteSpeedL2_norm_sq_sum_cells, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ancestor _
  apply cellBound initialLevel offset ancestor _ _ (by positivity)
  intro edge descendant
  have ancestorEquality : xiAncestorEdge system initialLevel offset edge = ancestor :=
    (xiEdgeAncestor_eq_xiAncestorEdge system initialLevel offset edge).symm.trans descendant
  have endpointRange := xiPotentialValues_descendant_endpoint_range system rulesConnected
    initialLevel initialValues offset resistances resistancesPositive edge
  rw [ancestorEquality] at endpointRange
  exact ⟨square_le_endpoint_squares _ _ _ endpointRange.1.1 endpointRange.1.2,
    square_le_endpoint_squares _ _ _ endpointRange.2.1 endpointRange.2.2⟩

end EIGS
