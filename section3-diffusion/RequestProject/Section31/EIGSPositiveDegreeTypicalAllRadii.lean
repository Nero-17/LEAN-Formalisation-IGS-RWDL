import RequestProject.Section31.EIGSTypicalBallMassUpperAllRadiiOfRules
import RequestProject.Section31.EIGSPositiveDegreeTypicalBallMass

/-! Actual volume and covering dimension from positive degree spectral data.
Both native and diameter-normalized metrics retain their original definitions.
Candidate source; no compilation is claimed. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

theorem xiTypicalBallMassUpperAllRadii_of_rules_of_positive_degree_data (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (degreeData : XiPositiveDegreeSpectralData system) (epsilon : ℝ)
    (epsilonPositive : 0 < epsilon) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    ∀ᵐ point ∂xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass,
      ∃ coefficient threshold : ℝ, 0 < coefficient ∧ 0 < threshold ∧
        ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
          (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
            (Metric.ball point radius) ≤
          coefficient * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) *
            |Real.log radius| ^
              (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + epsilon) := by
  intro parameters distanceGreaterThanOne mass
  letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    distanceGreaterThanOne parameters.eigenpair
  let physicalMeasure := xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
  let degreeRate := finiteRealMatrixSpectralRadius (degreeMatrix system)
  let exponent := Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)
  let logExponent := 1 / (Real.log mass.rate / Real.log degreeRate - 1) + epsilon
  have degreeGreaterThanOne : 1 < degreeRate := degreeData.rate_gt_one
  have degreePositive := zero_lt_one.trans degreeGreaterThanOne
  have degreeMass : degreeRate < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_positive_degree_data system connected loopless
      plantingNonadjacent distancePositive degreeData
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    (system.distanceSpectralRadius connected) mass.rate distanceGreaterThanOne
    (degreeGreaterThanOne.trans degreeMass).le
  obtain ⟨width, widthLarge, widthIdentity⟩ := logarithmic_collar_width_for_exact_exponent
    mass.rate degreeRate epsilon degreeGreaterThanOne degreeMass epsilonPositive
  have widthPositive : 0 < width :=
    (div_pos zero_lt_one (Real.log_pos ((one_lt_div degreePositive).mpr degreeMass))).trans widthLarge
  have logExponentNonnegative : 0 ≤ logExponent := by
    change 0 ≤ 1 / (Real.log mass.rate / Real.log degreeRate - 1) + epsilon
    rw [← widthIdentity]
    exact mul_nonneg widthPositive.le (Real.log_pos degreeGreaterThanOne).le
  obtain ⟨massConstant, massConstantPositive, spatialFraction, spatialFractionPositive, addressBound⟩ :=
    exists_xiTypicalLogarithmicBallMass_of_rules_of_positive_degree_data system connected loopless unique
      plantingNonadjacent distancePositive degreeData width widthLarge
  let radiusScale := spatialFraction / 2
  have radiusScalePositive : 0 < radiusScale := by dsimp only [radiusScale]; positivity
  let coefficient := massConstant * degreeRate
  have coefficientPositive : 0 < coefficient := mul_pos massConstantPositive degreePositive
  let radii := fun level : ℕ => radiusScale * (system.distanceSpectralRadius connected)⁻¹ ^ level
  let bounds := fun level : ℕ => coefficient * (level + 2 : ℝ) ^ logExponent / mass.rate ^ level
  have addressGood : ∀ᵐ address ∂mass.addressMeasure, ∃ threshold : ℕ, ∀ level : ℕ,
      threshold ≤ level → physicalMeasure.real (Metric.ball
        (xiAddressLimit system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair address)
        (radii level)) ≤ bounds level := by
    filter_upwards [addressBound] with address eventualBound
    obtain ⟨threshold, afterThreshold⟩ := Filter.eventually_atTop.mp eventualBound
    refine ⟨threshold, ?_⟩
    intro level after
    have radiusFit : radii level < spatialFraction *
        (system.distanceSpectralRadius connected)⁻¹ ^ level := by
      dsimp only [radii, radiusScale]
      exact mul_lt_mul_of_pos_right (by linarith)
        (pow_pos (inv_pos.mpr (zero_lt_one.trans distanceGreaterThanOne)) level)
    have closedBound := afterThreshold level after (radii level) radiusFit
    have degreeCost := logarithmic_ceiling_degree_cost_le degreeRate width
      degreeGreaterThanOne widthPositive.le level
    rw [widthIdentity] at degreeCost
    have costBound := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left degreeCost massConstantPositive.le)
      (pow_nonneg mass.rate_positive.le level)
    exact (measureReal_mono Metric.ball_subset_closedBall).trans
      (closedBound.trans (costBound.trans_eq (by dsimp only [bounds, coefficient, logExponent]; ring)))
  have physicalGood : ∀ᵐ point ∂physicalMeasure, ∃ threshold : ℕ, ∀ level : ℕ,
      threshold ≤ level → physicalMeasure.real (Metric.ball point (radii level)) ≤ bounds level :=
    (ae_map_iff
      (measurable_xiAddressLimit system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair).aemeasurable
      (measurableSet_eventual_geometric_ball_mass_bound physicalMeasure radii bounds)).mpr addressGood
  filter_upwards [physicalGood] with point good
  obtain ⟨threshold, afterThreshold⟩ := good
  exact geometric_logarithmic_ball_mass_upper_all_radii
    (fun radius => physicalMeasure.real (Metric.ball point radius))
    (fun _ _ comparison => measureReal_mono (Metric.ball_subset_ball comparison))
    (system.distanceSpectralRadius connected) mass.rate exponent logExponent radiusScale coefficient
    distanceGreaterThanOne exponentNonnegative growthIdentity logExponentNonnegative
    radiusScalePositive coefficientPositive threshold afterThreshold


end
end EIGS

#print axioms EIGS.xiTypicalBallMassUpperAllRadii_of_rules_of_positive_degree_data

