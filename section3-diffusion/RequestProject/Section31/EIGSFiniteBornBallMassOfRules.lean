import RequestProject.Section31.EIGSFiniteBornGeometricBallMassLower
import RequestProject.Section31.EIGSAllPointGeometricBallMassUpper
import RequestProject.Section31.GeometricBallMassLower
import RequestProject.Section31.GeometricLogarithmicBallMassUpper
import RequestProject.Section31.EIGSMetricOfRules
import RequestProject.Section31.NashTwoScaleOptimization
import RequestProject.Section2DegreeMassGap
import RequestProject.Section2PrimitiveIntegerGrowth

/-! Finite-born two-sided physical ball volume at all small radii.
The final assumptions are the original rules and the standing primitive
degree condition. Actual stars, incidence growth and completion geometry
are consumed internally. This file uses the native completion metric. -/

namespace EIGS
open MeasureTheory Metric IGS.Sec31
open scoped Classical
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiFiniteBornBallMass_of_rules (system : EIGSData K)
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
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    ∀ birth (vertex : XiVtx system birth), ∃ lower upper threshold : ℝ,
      0 < lower ∧ 0 < upper ∧ 0 < threshold ∧ ∀ radius : ℝ,
      0 < radius → radius ≤ threshold →
      lower * radius ^ ((Real.log mass.rate -
        Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log (system.distanceSpectralRadius connected)) ≤
        (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
          (Metric.ball (parameters.vertexEmbedding birth vertex) radius) ∧
      (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
          (Metric.ball (parameters.vertexEmbedding birth vertex) radius) ≤
        upper * radius ^ ((Real.log mass.rate -
          Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
          Real.log (system.distanceSpectralRadius connected)) := by
  intro parameters distanceGreaterThanOne mass
  let degreeRate := finiteRealMatrixSpectralRadius (degreeMatrix system)
  let exponent := Real.log (mass.rate / degreeRate) / Real.log (system.distanceSpectralRadius connected)
  let physicalMeasure := xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
  have degreeGreaterThanOne : 1 < degreeRate := degree_spectralRadius_gt_one_of_primitive system primitiveDegree
  have degreePositive := zero_lt_one.trans degreeGreaterThanOne
  have degreeMass : degreeRate < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_primitive system connected loopless
      plantingNonadjacent distancePositive primitiveDegree
  have ratioGreaterThanOne : 1 < mass.rate / degreeRate := (one_lt_div degreePositive).mpr degreeMass
  have ratioPositive := zero_lt_one.trans ratioGreaterThanOne
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    (system.distanceSpectralRadius connected) (mass.rate / degreeRate) distanceGreaterThanOne ratioGreaterThanOne.le
  have exponentIdentity : exponent = (Real.log mass.rate - Real.log degreeRate) /
      Real.log (system.distanceSpectralRadius connected) := by
    dsimp only [exponent]
    rw [Real.log_div mass.rate_positive.ne' degreePositive.ne']
  obtain ⟨upperCoefficient, upperRadius, upperCoefficientPositive, upperRadiusPositive, geometricUpper⟩ :=
    exists_xiAllPointGeometricBallMassUpper system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass primitiveDegree
  have geometricLower := exists_xiFiniteBornGeometricBallMassLower system connected parameters.lengths
    parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne
    parameters.eigenpair mass primitiveDegree
  intro birth vertex
  let center := parameters.vertexEmbedding birth vertex
  let volume := fun radius : ℝ => physicalMeasure.real (Metric.ball center radius)
  have volumeMonotone : Monotone volume :=
    fun _ _ comparison => measureReal_mono (Metric.ball_subset_ball comparison)
  obtain ⟨lowerCoefficient, lowerRadius, lowerCoefficientPositive, lowerRadiusPositive, lowerAtLevel⟩ :=
    geometricLower birth vertex
  have lowerAll := geometric_ball_mass_lower_all_radii volume volumeMonotone
    (system.distanceSpectralRadius connected) (mass.rate / degreeRate) exponent lowerCoefficient lowerRadius
    distanceGreaterThanOne ratioPositive exponentNonnegative growthIdentity lowerCoefficientPositive
    lowerRadiusPositive lowerAtLevel
  have upperAtLevel : ∀ level : ℕ, 0 ≤ level →
      volume (upperRadius * (system.distanceSpectralRadius connected)⁻¹ ^ level) ≤
        upperCoefficient * (level + 2 : ℝ) ^ (0 : ℝ) / (mass.rate / degreeRate) ^ level := by
    intro level _
    have ratioIdentity : (degreeRate / mass.rate) ^ level = 1 / (mass.rate / degreeRate) ^ level := by
      rw [div_pow, div_pow]
      field_simp [(pow_pos degreePositive level).ne', (pow_pos mass.rate_positive level).ne']
    have upperBound := geometricUpper level center
    change volume (upperRadius * (system.distanceSpectralRadius connected)⁻¹ ^ level) ≤
      upperCoefficient * (degreeRate / mass.rate) ^ level at upperBound
    rw [ratioIdentity] at upperBound
    simpa only [Real.rpow_zero, mul_one, mul_one_div] using upperBound
  obtain ⟨upperConstant, upperThreshold, upperConstantPositive, upperThresholdPositive, upperAll⟩ :=
    geometric_logarithmic_ball_mass_upper_all_radii volume volumeMonotone
      (system.distanceSpectralRadius connected) (mass.rate / degreeRate) exponent 0 upperRadius upperCoefficient
      distanceGreaterThanOne exponentNonnegative growthIdentity (by norm_num)
      upperRadiusPositive upperCoefficientPositive 0 upperAtLevel
  refine ⟨lowerCoefficient / ((mass.rate / degreeRate) * lowerRadius ^ exponent),
    upperConstant, min lowerRadius upperThreshold,
    div_pos lowerCoefficientPositive (mul_pos ratioPositive (Real.rpow_pos_of_pos lowerRadiusPositive _)),
    upperConstantPositive, lt_min lowerRadiusPositive upperThresholdPositive, ?_⟩
  intro radius radiusPositive radiusSmall
  have lowerBound := lowerAll radius radiusPositive (radiusSmall.trans (min_le_left _ _))
  have upperBound := upperAll radius radiusPositive (radiusSmall.trans (min_le_right _ _))
  simp only [Real.rpow_zero, mul_one] at upperBound
  rw [← exponentIdentity]
  exact ⟨lowerBound, upperBound⟩

end
end EIGS

#print axioms EIGS.exists_xiFiniteBornBallMass_of_rules
