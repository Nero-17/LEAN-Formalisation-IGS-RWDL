import RequestProject.Section31.CompactBallMassHausdorffDimension
import RequestProject.Section31.EIGSVertexMassLimits
import RequestProject.Section31.EIGSAllPointBallMassLowerOfRules
import RequestProject.Section31.EIGSTypicalBallMassUpperAllRadiiOfRules

/-! The actual completion covering-number logarithmic limit. All volume
inputs come from the original rules and their actual physical measure. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical ENNReal NNReal
noncomputable section
variable {K : ℕ}

theorem xiCompletion_hausdorff_dimension_of_rules (system : EIGSData K)
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
    dimH (Set.univ : Set parameters.LimitSpace) =
      ENNReal.ofReal (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) := by
  intro parameters mass
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    distanceGreaterThanOne parameters.eigenpair
  let physicalMeasure := xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
  have dimensionNonnegative : 0 ≤ Real.log mass.rate /
      Real.log (system.distanceSpectralRadius connected) :=
    div_nonneg (Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans
      (XiMassParameters.rate_ge_two system connected plantingNonadjacent mass)))
      (Real.log_nonneg distanceGreaterThanOne.le)
  obtain ⟨massConstant, radiusThreshold, massConstantPositive, radiusThresholdPositive, ballLower⟩ :=
    exists_xiAllPointBallMassLower_of_rules system connected loopless unique plantingNonadjacent
      distancePositive primitiveDegree
  have ballUpper := xiTypicalBallMassUpperAllRadii_of_rules system connected loopless unique
    plantingNonadjacent distancePositive primitiveDegree 1 zero_lt_one
  apply compact_hausdorff_dimension_eq_of_ball_mass_bounds physicalMeasure
    (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected))
    (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + 1)
    massConstant radiusThreshold dimensionNonnegative massConstantPositive radiusThresholdPositive ballLower
  filter_upwards [ballUpper] with point property
  obtain ⟨coefficient, threshold, coefficientPositive, thresholdPositive, bound⟩ := property
  refine ⟨coefficient, threshold, coefficientPositive, thresholdPositive, ?_⟩
  intro radius radiusPositive radiusSmall
  simpa only [mul_assoc] using bound radius radiusPositive radiusSmall

end
end EIGS

#print axioms EIGS.xiCompletion_hausdorff_dimension_of_rules
