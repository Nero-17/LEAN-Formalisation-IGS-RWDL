import RequestProject.Section31.EIGSLocallyFiniteUniformDegree
import RequestProject.Section31.EIGSBoundedIncidenceBallMassUpper
import RequestProject.Section31.EIGSAllPointGeometricBallMassLower
import RequestProject.Section31.EIGSMetricOfRules
import RequestProject.Section31.GeometricBallMassLower
import RequestProject.Section31.NashTwoScaleOptimization

/-! Native uniform power ball masses for the two literal nu=1 rules.
All rule certificates, bounded incidence counts, path parameters and mass
parameters are filled internally. The two graph models remain distinct.
Candidate source, awaiting compilation. -/

namespace EIGS
open MeasureTheory Metric IGS.Sec31
open scoped Classical
noncomputable section

theorem locallyFiniteRuleSystem_native_ball_mass_upper (canonical : Bool) :
    let system := locallyFiniteRuleSystem canonical
    let connected := locallyFiniteRuleSystem_connected canonical
    let parameters := xiPathMetricDataOfRules system connected
      (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
      (locallyFiniteRuleSystem_distancePositive canonical)
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected (locallyFiniteRuleSystem_edgesUnique canonical)
          (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical))
    let mass := xiMassParametersOfRules system connected (locallyFiniteRuleSystem_distancePositive canonical)
    ∃ coefficient threshold : ℝ, 0 < coefficient ∧ 0 < threshold ∧
      ∀ point : parameters.LimitSpace, ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
          (Metric.ball point radius) ≤
            coefficient * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) := by
  intro system connected parameters distanceGreaterThanOne mass
  have massAtLeastOne : 1 ≤ mass.rate := (by norm_num : (1 : ℝ) ≤ 2).trans
    (XiMassParameters.rate_ge_two system connected (locallyFiniteRuleSystem_plantingNonadjacent canonical) mass)
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    (system.distanceSpectralRadius connected) mass.rate distanceGreaterThanOne massAtLeastOne
  obtain ⟨coefficient, radiusFactor, coefficientPositive, radiusFactorPositive, geometricUpper⟩ :=
    exists_xiBoundedIncidenceGeometricBallMassUpper system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass 3
      (by norm_num) (locallyFiniteRuleSystem_incidence_le_three canonical)
  exact uniform_geometric_ball_mass_upper_all_radii
    (fun point radius => (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
      (Metric.ball point radius))
    (fun _ _ _ comparison => measureReal_mono (Metric.ball_subset_ball comparison))
    (system.distanceSpectralRadius connected) mass.rate
    (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) radiusFactor coefficient
    distanceGreaterThanOne exponentNonnegative growthIdentity radiusFactorPositive coefficientPositive geometricUpper

theorem locallyFiniteRuleSystem_native_ball_mass_lower (canonical : Bool) :
    let system := locallyFiniteRuleSystem canonical
    let connected := locallyFiniteRuleSystem_connected canonical
    let parameters := xiPathMetricDataOfRules system connected
      (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
      (locallyFiniteRuleSystem_distancePositive canonical)
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected (locallyFiniteRuleSystem_edgesUnique canonical)
          (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical))
    let mass := xiMassParametersOfRules system connected (locallyFiniteRuleSystem_distancePositive canonical)
    ∃ coefficient threshold : ℝ, 0 < coefficient ∧ 0 < threshold ∧
      ∀ point : parameters.LimitSpace, ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        coefficient * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) ≤
          (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
            (Metric.ball point radius) := by
  intro system connected parameters distanceGreaterThanOne mass
  have massAtLeastOne : 1 ≤ mass.rate := (by norm_num : (1 : ℝ) ≤ 2).trans
    (XiMassParameters.rate_ge_two system connected (locallyFiniteRuleSystem_plantingNonadjacent canonical) mass)
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    (system.distanceSpectralRadius connected) mass.rate distanceGreaterThanOne massAtLeastOne
  obtain ⟨coefficient, radiusFactor, coefficientPositive, radiusFactorPositive, geometricLower⟩ :=
    exists_xiAllPointGeometricBallMassLower system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
  refine ⟨coefficient / (mass.rate * radiusFactor ^
    (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected))), radiusFactor,
    div_pos coefficientPositive (mul_pos mass.rate_positive
      (Real.rpow_pos_of_pos radiusFactorPositive _)), radiusFactorPositive, ?_⟩
  intro point radius radiusPositive radiusSmall
  exact geometric_ball_mass_lower_all_radii
    (fun size => (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
      (Metric.ball point size))
    (fun _ _ comparison => measureReal_mono (Metric.ball_subset_ball comparison))
    (system.distanceSpectralRadius connected) mass.rate
    (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) coefficient radiusFactor
    distanceGreaterThanOne mass.rate_positive exponentNonnegative growthIdentity coefficientPositive
    radiusFactorPositive (fun level => geometricLower level point) radius radiusPositive radiusSmall

end
end EIGS

#print axioms EIGS.locallyFiniteRuleSystem_native_ball_mass_upper
#print axioms EIGS.locallyFiniteRuleSystem_native_ball_mass_lower
