import RequestProject.Section31.EIGSLocallyFiniteNativeBallMass
import RequestProject.Section31.CompactCoveringNumberDimension
import RequestProject.Section31.CompactBallMassHausdorffDimension

/-! Covering and Hausdorff dimensions of the literal locally finite rules
in their native metric. All power ball bounds are already actual consumers;
no primitive degree data or finite stationary-degree fibers are required.
Candidate source, awaiting compilation. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical ENNReal NNReal
noncomputable section

theorem locallyFiniteRuleSystem_native_dimensions (canonical : Bool) :
    let system := locallyFiniteRuleSystem canonical
    let connected := locallyFiniteRuleSystem_connected canonical
    let parameters := xiPathMetricDataOfRules system connected
      (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
      (locallyFiniteRuleSystem_distancePositive canonical)
    let mass := xiMassParametersOfRules system connected (locallyFiniteRuleSystem_distancePositive canonical)
    Tendsto (fun radius : ℝ => Real.log (realCoveringNumber parameters.LimitSpace radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected))) ∧
    dimH (Set.univ : Set parameters.LimitSpace) =
      ENNReal.ofReal (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) := by
  intro system connected parameters mass
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical))
  letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    distanceGreaterThanOne parameters.eigenpair
  let physicalMeasure := xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
  have dimensionNonnegative : 0 ≤ Real.log mass.rate / Real.log (system.distanceSpectralRadius connected) :=
    div_nonneg (Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans
      (XiMassParameters.rate_ge_two system connected (locallyFiniteRuleSystem_plantingNonadjacent canonical) mass)))
      (Real.log_nonneg distanceGreaterThanOne.le)
  obtain ⟨lower, lowerThreshold, lowerPositive, lowerThresholdPositive, ballLower⟩ :=
    locallyFiniteRuleSystem_native_ball_mass_lower canonical
  obtain ⟨upper, upperThreshold, upperPositive, upperThresholdPositive, ballUpper⟩ :=
    locallyFiniteRuleSystem_native_ball_mass_upper canonical
  have almostEverywhere : ∀ᵐ point ∂physicalMeasure, ∃ coefficient threshold : ℝ,
      0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        physicalMeasure.real (Metric.ball point radius) ≤
          coefficient * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) *
            |Real.log radius| ^ (0 : ℝ) := by
    exact Eventually.of_forall (fun point => ⟨upper, upperThreshold, upperPositive, upperThresholdPositive,
      fun radius radiusPositive radiusSmall => by
        simpa only [Real.rpow_zero, mul_one] using ballUpper point radius radiusPositive radiusSmall⟩)
  constructor
  · exact compact_coveringNumber_logarithmic_limit_of_ball_mass_bounds physicalMeasure
      (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) 0 lower lowerThreshold
      (by norm_num) lowerPositive lowerThresholdPositive ballLower
      (by simpa only [mul_assoc] using almostEverywhere)
  · exact compact_hausdorff_dimension_eq_of_ball_mass_bounds physicalMeasure
      (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) 0 lower lowerThreshold
      dimensionNonnegative lowerPositive lowerThresholdPositive ballLower almostEverywhere

end
end EIGS

#print axioms EIGS.locallyFiniteRuleSystem_native_dimensions
