import RequestProject.Section31.EIGSActualRecurrenceCriterion
import RequestProject.Section31.EIGSAnalyticTimeScale

/-! Connect the actual fractional-eccentricity recurrence definition with
the global spectral exponent formula. Identifying this formula with the
almost-everywhere heat-kernel limit is a separate actual theorem. -/

namespace EIGS

open scoped Classical
noncomputable section
variable {K : ℕ}

theorem xiActualRecurrent_iff_globalSpectralFormula_lt_two (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    xiActualRecurrent system ↔
      2 * Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData)) /
        Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius connected distancePositive) < 2 := by
  let mass := xiMassParametersOfRules system connected distancePositive
  obtain ⟨resistancePositive, vector, vectorPositive, eigenpair⟩ :=
    system.resistanceSpectralRadius_positive_eigenpair connected distancePositive
  have timeGreaterThanOne := xiAnalyticTimeRate_gt_one system connected loopless unique
    plantingNonadjacent distancePositive mass
    (system.resistanceSpectralRadius connected distancePositive) resistancePositive vector vectorPositive eigenpair
  rw [XiMassParameters.rate_eq_spectralRadius system mass] at timeGreaterThanOne
  have massPositive : 0 < realMatrixSpectralRadius (massMatrixR system.toRuleData) := by
    rw [← XiMassParameters.rate_eq_spectralRadius system mass]
    exact mass.rate_positive
  rw [xiActualRecurrent_iff_resistanceSpectralRadius_gt_one system connected loopless unique
    plantingNonadjacent distancePositive, div_lt_iff₀ (Real.log_pos timeGreaterThanOne),
    Real.log_mul massPositive.ne' resistancePositive.ne']
  constructor
  · intro growth
    linarith [Real.log_pos growth]
  · intro exponentBound
    apply (Real.log_pos_iff resistancePositive.le).mp
    linarith

end
end EIGS

#print axioms EIGS.xiActualRecurrent_iff_globalSpectralFormula_lt_two
