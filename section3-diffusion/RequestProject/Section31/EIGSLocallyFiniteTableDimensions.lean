import RequestProject.Section31.EIGSLocallyFiniteDiameterDimensions
import RequestProject.Section31.EIGSLocallyFiniteCanonicalRates
import RequestProject.Section2WalkDimension

/-! Actual Table 1 geometric and walk dimensions. The two models are
distinguished: false is Laakso (lambda=4, mu*rho=18), true is canonical Xi
(lambda=3, mu*rho=33/2). Degree dimension infinity is the manuscript's
locally finite convention; no finite stationary-degree fiber theorem is
applied here. Candidate source, awaiting compilation. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical ENNReal NNReal
noncomputable section

theorem locallyFiniteRuleSystem_table_geometric_dimensions (canonical : Bool) :
    let system := locallyFiniteRuleSystem canonical
    let connected := locallyFiniteRuleSystem_connected canonical
    let parameters := xiPathMetricDataOfRules system connected
      (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
      (locallyFiniteRuleSystem_distancePositive canonical)
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected (locallyFiniteRuleSystem_edgesUnique canonical)
          (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical))
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace system connected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
    Tendsto (fun radius : ℝ => Real.log (realCoveringNumber parameters.LimitSpace radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 6 / Real.log (locallyFiniteRuleDistance canonical))) ∧
    dimH (Set.univ : Set parameters.LimitSpace) = ENNReal.ofReal (Real.log 6 / Real.log (locallyFiniteRuleDistance canonical)) ∧
    Tendsto (fun radius : ℝ =>
      Real.log (@realCoveringNumber parameters.LimitSpace normalizedMetric radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 6 / Real.log (locallyFiniteRuleDistance canonical))) ∧
    @dimH parameters.LimitSpace (@MetricSpace.toEMetricSpace parameters.LimitSpace normalizedMetric)
      (Set.univ : Set parameters.LimitSpace) = ENNReal.ofReal (Real.log 6 / Real.log (locallyFiniteRuleDistance canonical)) := by
  intro system connected parameters distanceGreaterThanOne normalizedMetric
  let mass := xiMassParametersOfRules system connected (locallyFiniteRuleSystem_distancePositive canonical)
  have dimensionEquality : Real.log mass.rate / Real.log (system.distanceSpectralRadius connected) =
      Real.log 6 / Real.log (locallyFiniteRuleDistance canonical) := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass,
      locallyFiniteRuleSystem_massSpectralRadius, locallyFiniteRuleSystem_distanceSpectralRadius]
  have native := locallyFiniteRuleSystem_native_dimensions canonical
  have normalized := locallyFiniteRuleSystem_diameter_dimensions canonical
  dsimp only at native normalized
  rw [dimensionEquality] at native normalized
  exact ⟨native.1, native.2, normalized.1, normalized.2⟩

theorem locallyFiniteRuleSystem_table_walk_dimension (canonical : Bool)
    (radiusLower radiusUpper : ℝ) (radiusLowerPositive : 0 < radiusLower) (radiusUpperPositive : 0 < radiusUpper) :
    ∃ buffer : ℕ, ∀ initialLevel (vertex : XiVtx (locallyFiniteRuleSystem canonical) initialLevel)
      (depth : ℕ → ℕ) (radius : ℕ → ℝ), Tendsto radius atTop atTop →
      (∀ᶠ index in atTop, depth index + buffer ≤ index ∧
        radiusLower * (locallyFiniteRuleSystem canonical).distanceSpectralRadius
          (locallyFiniteRuleSystem_connected canonical) ^ depth index ≤ radius index ∧
        radius index ≤ radiusUpper * (locallyFiniteRuleSystem canonical).distanceSpectralRadius
          (locallyFiniteRuleSystem_connected canonical) ^ depth index) →
      Tendsto (fun index =>
        Real.log (expExit (XiSimpleGraph (locallyFiniteRuleSystem canonical) (initialLevel + index))
          (finiteGraphBall (XiSimpleGraph (locallyFiniteRuleSystem canonical) (initialLevel + index))
            (xiForward (locallyFiniteRuleSystem canonical) initialLevel index vertex) (radius index))
          (xiForward (locallyFiniteRuleSystem canonical) initialLevel index vertex)) / Real.log (radius index))
        atTop (𝓝 (Real.log (if canonical then (33 / 2 : ℝ) else 18) /
          Real.log (locallyFiniteRuleDistance canonical))) := by
  have actual := xiSimpleGraph_admissible_walk_dimension_limit (locallyFiniteRuleSystem canonical)
    (locallyFiniteRuleSystem_connected canonical) (locallyFiniteRuleSystem_loopless canonical)
    (locallyFiniteRuleSystem_edgesUnique canonical) (locallyFiniteRuleSystem_plantingNonadjacent canonical)
    (locallyFiniteRuleSystem_distancePositive canonical) radiusLower radiusUpper radiusLowerPositive radiusUpperPositive
  have timeRateEquality :
      realMatrixSpectralRadius (massMatrixR (locallyFiniteRuleSystem canonical).toRuleData) *
        (locallyFiniteRuleSystem canonical).resistanceSpectralRadius
          (locallyFiniteRuleSystem_connected canonical) (locallyFiniteRuleSystem_distancePositive canonical) =
      (if canonical then (33 / 2 : ℝ) else 18) := by
    rw [locallyFiniteRuleSystem_massSpectralRadius, locallyFiniteRuleSystem_resistanceSpectralRadius]
    cases canonical <;> norm_num [locallyFiniteRuleResistance]
  rw [timeRateEquality] at actual
  obtain ⟨buffer, limits⟩ := actual
  refine ⟨buffer, ?_⟩
  intro initialLevel vertex depth radius radiusTendsto admissible
  have limit := limits initialLevel vertex depth radius radiusTendsto admissible
  simpa only [locallyFiniteRuleSystem_distanceSpectralRadius] using limit

end
end EIGS

#print axioms EIGS.locallyFiniteRuleSystem_table_geometric_dimensions
#print axioms EIGS.locallyFiniteRuleSystem_table_walk_dimension
