import RequestProject.Section31.EIGSDegreeHeatExponent
import RequestProject.Section31.EIGSPositiveDegreeSpectralGaps

/-! The actual finite-born energy/evaluation estimate uses positive degree
spectral data in place of primitivity. No target heat estimate is assumed.
Candidate source, awaiting compilation. -/

namespace EIGS

theorem xiFiniteBorn_heat_exponent_between_zero_one_of_positive_degree_data {K : ℕ} (system : EIGSData K)
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
    (degreeData : XiPositiveDegreeSpectralData system) :
    0 < (Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log (mass.rate * resistanceRate) ∧
      (Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log (mass.rate * resistanceRate) < 1 := by
  have degreePositive : 0 < finiteRealMatrixSpectralRadius (degreeMatrix system) :=
    zero_lt_one.trans degreeData.rate_gt_one
  have degreeMass : finiteRealMatrixSpectralRadius (degreeMatrix system) < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_positive_degree_data system rulesConnected rulesLoopless
      plantingNonadjacent distancePositive degreeData
  have degreeResistance : 1 < finiteRealMatrixSpectralRadius (degreeMatrix system) * resistanceRate := by
    rw [system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
      ratePositive vectorPositive (by funext colour; exact renormalizationEigenpair colour)]
    exact degree_resistance_spectral_product_gt_one_of_positive_degree_data system rulesConnected plantingNonadjacent distancePositive degreeData
  exact degree_heat_exponent_between_zero_one mass.rate
    (finiteRealMatrixSpectralRadius (degreeMatrix system)) resistanceRate mass.rate_positive
    degreePositive ratePositive degreeMass degreeResistance


end EIGS

#print axioms EIGS.xiFiniteBorn_heat_exponent_between_zero_one_of_positive_degree_data

