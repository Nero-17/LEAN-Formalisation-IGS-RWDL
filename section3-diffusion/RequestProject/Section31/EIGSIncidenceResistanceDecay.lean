import RequestProject.Section31.EIGSSpeedDegree
import RequestProject.Section2DegreeResistanceGap
import RequestProject.Section2SpectralGrowth
import RequestProject.Section2ResistanceSpectralRadius

/-! The actual inverse incidence--resistance scale of each fixed-birth vertex
tends to zero. The strict degree--resistance spectral gap is derived from rules. -/

namespace EIGS

open Filter Topology
open scoped BigOperators

variable {K : ℕ}

theorem xiIncidence_resistance_inverse_tendsto_zero (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (birth : ℕ) (vertex : XiVtx system birth) :
    Tendsto (fun age : ℕ =>
      1 / ((xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) *
        resistanceRate ^ (birth + age))) atTop (nhds 0) := by
  obtain ⟨degreePositive, degreeGrowth⟩ := degree_spectral_growth_from_primitive_rules system rulesConnected primitiveDegree
  obtain ⟨lower, upper, lowerPositive, upperPositive, growthBounds⟩ := degreeGrowth birth vertex
  have productGap := degree_resistance_spectral_product_gt_one system rulesConnected plantingNonadjacent distancePositive primitiveDegree
  have resistanceEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext eigenpair)
  rw [← resistanceEquality] at productGap
  have lowerBound : ∀ age : ℕ,
      lower * resistanceRate ^ birth *
          (finiteRealMatrixSpectralRadius (degreeMatrix system) * resistanceRate) ^ age ≤
        (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) *
          resistanceRate ^ (birth + age) := by
    intro age
    have degreeBound := (growthBounds age).1
    rw [← xiSimpleGraph_degree_eq_degree_state_sum system rulesConnected rulesLoopless rulesUnique plantingNonadjacent,
      ← xiVertexIncidenceCount_eq_degree system rulesConnected rulesLoopless rulesUnique plantingNonadjacent] at degreeBound
    have multiplied := mul_le_mul_of_nonneg_right degreeBound (pow_pos ratePositive (birth + age)).le
    convert multiplied using 1 <;> rw [pow_add, mul_pow] <;> ring
  have inverseBound : ∀ age : ℕ,
      1 / ((xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) *
          resistanceRate ^ (birth + age)) ≤
        (lower * resistanceRate ^ birth)⁻¹ *
          (finiteRealMatrixSpectralRadius (degreeMatrix system) * resistanceRate)⁻¹ ^ age := by
    intro age
    have comparison := one_div_le_one_div_of_le
      (mul_pos (mul_pos lowerPositive (pow_pos ratePositive birth)) (pow_pos (mul_pos degreePositive ratePositive) age))
      (lowerBound age)
    simpa only [one_div, mul_inv_rev, mul_pow, inv_pow, mul_comm, mul_left_comm, mul_assoc] using comparison
  have geometric := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_pos.2 (mul_pos degreePositive ratePositive)).le
    ((inv_lt_one₀ (mul_pos degreePositive ratePositive)).2 productGap)
  have upperConvergence := geometric.const_mul (lower * resistanceRate ^ birth)⁻¹
  apply squeeze_zero (fun age => by positivity) inverseBound
  simpa only [mul_zero] using upperConvergence

end EIGS
