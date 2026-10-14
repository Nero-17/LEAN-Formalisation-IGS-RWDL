import RequestProject.Section31.AELogarithmicBallHausdorffLower
import RequestProject.Section31.EIGSCoveringNumberDimensionOfRules

/-! Actual-model Hausdorff lower bounds from the original physical
almost-everywhere small-ball estimates, with no dimension conclusion input. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 12000000
variable {K : ℕ}

theorem xiCompletion_hausdorff_dimension_lower_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let mass := xiMassParametersOfRules system connected distancePositive
    ∀ lowerExponent : ℝ≥0, 0 < lowerExponent →
      (lowerExponent : ℝ) < Real.log mass.rate / Real.log (system.distanceSpectralRadius connected) →
      (lowerExponent : ℝ≥0∞) ≤ dimH (Set.univ : Set parameters.LimitSpace) := by
  intro parameters mass lowerExponent lowerPositive strictLower
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  let physicalMeasure := xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
  have ballUpper := xiTypicalBallMassUpperAllRadii_of_rules system connected loopless unique
    plantingNonadjacent distancePositive primitiveDegree 1 zero_lt_one
  apply hausdorff_dimension_lower_of_ae_logarithmic_ball_upper physicalMeasure
    (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected))
    (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + 1)
    lowerExponent lowerPositive strictLower
  filter_upwards [ballUpper] with point property
  obtain ⟨coefficient, threshold, coefficientPositive, thresholdPositive, bound⟩ := property
  refine ⟨coefficient, threshold, coefficientPositive, thresholdPositive, ?_⟩
  intro radius radiusPositive radiusSmall
  simpa only [mul_assoc] using bound radius radiusPositive radiusSmall

end
end EIGS

#print axioms EIGS.xiCompletion_hausdorff_dimension_lower_of_rules
