import RequestProject.Section2PrimitiveIntegerGrowth
import RequestProject.Section2DegreeMassGap
import RequestProject.Section2DegreeResistanceGap
import RequestProject.Section31.EIGSAnalyticTimeScale

/-! The finite-born heat exponent is strictly between zero and one under
the original primitive-degree standing condition. The strict matrix gaps
and the admissible resistance eigenvalue are actual-model conclusions. -/

namespace EIGS

theorem degree_heat_exponent_between_zero_one
    (massRate degreeRate resistanceRate : ℝ)
    (massPositive : 0 < massRate) (degreePositive : 0 < degreeRate)
    (resistancePositive : 0 < resistanceRate)
    (degreeMass : degreeRate < massRate) (degreeResistance : 1 < degreeRate * resistanceRate) :
    0 < (Real.log massRate - Real.log degreeRate) / Real.log (massRate * resistanceRate) ∧
      (Real.log massRate - Real.log degreeRate) / Real.log (massRate * resistanceRate) < 1 := by
  have timeGreaterThanOne : 1 < massRate * resistanceRate :=
    degreeResistance.trans (mul_lt_mul_of_pos_right degreeMass resistancePositive)
  have denominatorPositive := Real.log_pos timeGreaterThanOne
  have numeratorPositive : 0 < Real.log massRate - Real.log degreeRate :=
    sub_pos.mpr (Real.log_lt_log degreePositive degreeMass)
  refine ⟨div_pos numeratorPositive denominatorPositive, ?_⟩
  apply (div_lt_one denominatorPositive).mpr
  have degreeResistanceLog := Real.log_pos degreeResistance
  rw [Real.log_mul degreePositive.ne' resistancePositive.ne'] at degreeResistanceLog
  rw [Real.log_mul massPositive.ne' resistancePositive.ne']
  linarith

theorem xiFiniteBorn_heat_exponent_between_zero_one {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    0 < (Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log (mass.rate * resistanceRate) ∧
      (Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log (mass.rate * resistanceRate) < 1 := by
  have degreePositive : 0 < finiteRealMatrixSpectralRadius (degreeMatrix system) :=
    zero_lt_one.trans (degree_spectralRadius_gt_one_of_primitive system primitiveDegree)
  have degreeMass : finiteRealMatrixSpectralRadius (degreeMatrix system) < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_primitive system rulesConnected rulesLoopless
      plantingNonadjacent distancePositive primitiveDegree
  have degreeResistance : 1 < finiteRealMatrixSpectralRadius (degreeMatrix system) * resistanceRate := by
    rw [system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
      ratePositive vectorPositive (by funext colour; exact renormalizationEigenpair colour)]
    exact degree_resistance_spectral_product_gt_one system rulesConnected plantingNonadjacent distancePositive primitiveDegree
  exact degree_heat_exponent_between_zero_one mass.rate
    (finiteRealMatrixSpectralRadius (degreeMatrix system)) resistanceRate mass.rate_positive
    degreePositive ratePositive degreeMass degreeResistance

end EIGS

#print axioms EIGS.degree_heat_exponent_between_zero_one
#print axioms EIGS.xiFiniteBorn_heat_exponent_between_zero_one
