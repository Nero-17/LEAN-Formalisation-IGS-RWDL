import RequestProject.Section31.EIGSAllPointBallMassLowerOfRules
import RequestProject.Section31.EIGSPositiveDegreeSpectralGaps

/-! Actual volume and covering dimension from positive degree spectral data.
Both native and diameter-normalized metrics retain their original definitions.
Candidate source; no compilation is claimed. -/

namespace EIGS

open MeasureTheory Filter Topology Metric IGS.Sec31
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem exists_xiAllPointBallMassLower_of_rules_of_positive_degree_data (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (degreeData : XiPositiveDegreeSpectralData system) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    ∃ coefficient threshold : ℝ, 0 < coefficient ∧ 0 < threshold ∧
      ∀ point : parameters.LimitSpace, ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        coefficient * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) ≤
          (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
            (Metric.ball point radius) := by
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system connected distancePositive
  have massGreaterThanOne : 1 < mass.rate := by
    have degreeGreaterThanOne := degreeData.rate_gt_one
    have degreeMass := degree_spectralRadius_lt_mass_of_positive_degree_data system connected loopless
      plantingNonadjacent distancePositive degreeData
    rw [← XiMassParameters.rate_eq_spectralRadius system mass] at degreeMass
    exact degreeGreaterThanOne.trans degreeMass
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    (system.distanceSpectralRadius connected) mass.rate distanceGreaterThanOne massGreaterThanOne.le
  obtain ⟨massLower, radiusFactor, massLowerPositive, radiusFactorPositive, geometricLower⟩ :=
    exists_xiAllPointGeometricBallMassLower system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
  dsimp only
  refine ⟨massLower / (mass.rate * radiusFactor ^
    (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected))), radiusFactor,
    div_pos massLowerPositive (mul_pos mass.rate_positive
      (Real.rpow_pos_of_pos radiusFactorPositive _)), radiusFactorPositive, ?_⟩
  intro point radius radiusPositive radiusSmall
  apply geometric_ball_mass_lower_all_radii
    (fun size => (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
      (Metric.ball point size))
    (fun _ _ comparison => measureReal_mono (Metric.ball_subset_ball comparison))
    (system.distanceSpectralRadius connected) mass.rate
    (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) massLower radiusFactor
    distanceGreaterThanOne mass.rate_positive exponentNonnegative growthIdentity massLowerPositive
    radiusFactorPositive (fun level => geometricLower level point) radius radiusPositive radiusSmall


end
end EIGS

#print axioms EIGS.exists_xiAllPointBallMassLower_of_rules_of_positive_degree_data

