import RequestProject.Section31.EIGSPositiveDegreeCoveringDimension
import RequestProject.Section31.EIGSPositiveDegreeDiameterCoveringDimension
import RequestProject.Section31.EIGSTwoColourPositiveDegreeData
import RequestProject.Section31.EIGSTwoColourActualSpectralParameters
import RequestProject.Section31.EIGSActualTerminalResistanceDimension
import RequestProject.Section2WalkDimension

/-! Actual geometric and discrete-walk dimension limits for Figure 3.
The covering counts, terminal effective resistance and mean exit times
are the actual objects. Degree growth is used via the actual positive
vector, not via a false primitive-matrix assumption. Candidate source. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 12000000

theorem twoColourSystem_native_coveringNumber_dimension :
    let parameters := xiPathMetricDataOfRules twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_distancePositive
    let mass := xiMassParametersOfRules twoColourSystem twoColourSystem_connected twoColourSystem_distancePositive
    Tendsto (fun radius : ℝ => Real.log (realCoveringNumber parameters.LimitSpace radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log (3 + Real.sqrt 6) / Real.log 2)) := by
  have actual := xiCompletion_coveringNumber_dimension_of_rules_of_positive_degree_data twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique
    twoColourSystem_plantingNonadjacent twoColourSystem_distancePositive twoColourPositiveDegreeData
  have actualExponent :
      Real.log (xiMassParametersOfRules twoColourSystem twoColourSystem_connected
        twoColourSystem_distancePositive).rate /
        Real.log (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) =
      Real.log (3 + Real.sqrt 6) / Real.log 2 := by
    rw [XiMassParameters.rate_eq_spectralRadius, twoColourSystem_massSpectralRadius,
      twoColourSystem_distanceSpectralRadius]
  simpa only [actualExponent] using actual

theorem twoColourSystem_diameter_coveringNumber_dimension :
    let parameters := xiPathMetricDataOfRules twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_distancePositive
    let distanceGreaterThanOne : 1 < twoColourSystem.distanceSpectralRadius twoColourSystem_connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (twoColourSystem.two_le_distanceSpectralRadius twoColourSystem_connected twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent twoColourSystem_distancePositive)
    let mass := xiMassParametersOfRules twoColourSystem twoColourSystem_connected twoColourSystem_distancePositive
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace twoColourSystem twoColourSystem_connected parameters.lengths
      parameters.lengthsPositive (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair
    Tendsto (fun radius : ℝ =>
      Real.log (@realCoveringNumber parameters.LimitSpace normalizedMetric radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log (3 + Real.sqrt 6) / Real.log 2)) := by
  have actual := xiDiameterCompletion_coveringNumber_dimension_of_rules_of_positive_degree_data twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique
    twoColourSystem_plantingNonadjacent twoColourSystem_distancePositive twoColourPositiveDegreeData
  have actualExponent :
      Real.log (xiMassParametersOfRules twoColourSystem twoColourSystem_connected
        twoColourSystem_distancePositive).rate /
        Real.log (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) =
      Real.log (3 + Real.sqrt 6) / Real.log 2 := by
    rw [XiMassParameters.rate_eq_spectralRadius, twoColourSystem_massSpectralRadius,
      twoColourSystem_distanceSpectralRadius]
  simpa only [actualExponent] using actual

theorem twoColourSystem_terminal_resistance_dimension_limit :
    Tendsto (fun level =>
      Real.log (effResToBoundary (XiSimpleGraph twoColourSystem level)
        (Finset.univ.erase (xiNegativeTerminal twoColourSystem level)) (xiPositiveTerminal twoColourSystem level)) /
      Real.log ((XiSimpleGraph twoColourSystem level).dist (xiPositiveTerminal twoColourSystem level)
        (xiNegativeTerminal twoColourSystem level) : ℝ)) atTop
      (𝓝 (Real.log twoColourResistanceRate / Real.log 2)) := by
  have actual := xiSimpleGraph_terminal_resistance_dimension_limit twoColourSystem twoColourSystem_connected
    twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
    twoColourSystem_distancePositive
  simpa only [twoColourSystem_resistanceSpectralRadius, twoColourSystem_distanceSpectralRadius] using actual

theorem twoColourSystem_degree_mass_logarithmic_ratio (birth : ℕ) (vertex : XiVtx twoColourSystem birth) :
    Tendsto (fun age => Real.log (totalEdges twoColourSystem.toRuleData (birth + age) : ℝ) /
      Real.log (∑ state, degVec twoColourSystem (birth + age)
        (xiForward twoColourSystem birth age vertex) state)) atTop
      (𝓝 (Real.log (3 + Real.sqrt 6) / Real.log 2)) := by
  obtain ⟨massRatePositive, massLower, massUpper, massLowerPositive, massUpperPositive, massBounds⟩ :=
    eigs_mass_spectral_growth twoColourSystem twoColourSystem_connected twoColourSystem_distancePositive
  rw [twoColourSystem_massSpectralRadius] at massRatePositive massBounds
  obtain ⟨degreeLower, degreeUpper, degreeLowerPositive, degreeUpperPositive, degreeBounds⟩ :=
    twoColourSystem_degree_growth birth vertex
  have depthTendsto : Tendsto (fun age : ℕ => birth + age) atTop atTop := by
    apply tendsto_atTop.2
    intro bound
    exact eventually_atTop.2 ⟨bound, fun age atLeast => by omega⟩
  have massLog := logarithmic_geometric_scale_limit massRatePositive massLowerPositive massUpperPositive
    depthTendsto (Eventually.of_forall (fun age => massBounds (birth + age)))
  have degreeGlobalBounds (age : ℕ) :
      (degreeLower / 2 ^ birth) * (2 : ℝ) ^ (birth + age) ≤
        ∑ state, degVec twoColourSystem (birth + age) (xiForward twoColourSystem birth age vertex) state ∧
      (∑ state, degVec twoColourSystem (birth + age) (xiForward twoColourSystem birth age vertex) state) ≤
        (degreeUpper / 2 ^ birth) * (2 : ℝ) ^ (birth + age) := by
    have lowerIdentity : (degreeLower / 2 ^ birth) * (2 : ℝ) ^ (birth + age) = degreeLower * 2 ^ age := by
      rw [pow_add]; field_simp; ring
    have upperIdentity : (degreeUpper / 2 ^ birth) * (2 : ℝ) ^ (birth + age) = degreeUpper * 2 ^ age := by
      rw [pow_add]; field_simp; ring
    rw [lowerIdentity, upperIdentity]
    exact degreeBounds age
  have degreeLog := logarithmic_geometric_scale_limit (by norm_num : (0 : ℝ) < 2)
    (by positivity : 0 < degreeLower / (2 : ℝ) ^ birth)
    (by positivity : 0 < degreeUpper / (2 : ℝ) ^ birth)
    depthTendsto (Eventually.of_forall degreeGlobalBounds)
  apply (massLog.div degreeLog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne').congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with age agePositive
  have depthNonzero : ((birth + age : ℕ) : ℝ) ≠ 0 := by
    have positive : 0 < birth + age := by omega
    exact_mod_cast positive.ne'
  exact div_div_div_cancel_right₀ depthNonzero _ _

theorem twoColourSystem_admissible_walk_dimension_limit
    (radiusLower radiusUpper : ℝ) (radiusLowerPositive : 0 < radiusLower)
    (radiusUpperPositive : 0 < radiusUpper) :
    ∃ buffer : ℕ, ∀ initialLevel (vertex : XiVtx twoColourSystem initialLevel)
      (depth : ℕ → ℕ) (radius : ℕ → ℝ),
      Tendsto radius atTop atTop →
      (∀ᶠ index in atTop, depth index + buffer ≤ index ∧
        radiusLower * (2 : ℝ) ^ depth index ≤ radius index ∧
        radius index ≤ radiusUpper * (2 : ℝ) ^ depth index) →
      Tendsto (fun index =>
        Real.log (expExit (XiSimpleGraph twoColourSystem (initialLevel + index))
          (finiteGraphBall (XiSimpleGraph twoColourSystem (initialLevel + index))
            (xiForward twoColourSystem initialLevel index vertex) (radius index))
          (xiForward twoColourSystem initialLevel index vertex)) /
        Real.log (radius index)) atTop
        (𝓝 (Real.log ((3 + Real.sqrt 6) * twoColourResistanceRate) / Real.log 2)) := by
  have actual := xiSimpleGraph_admissible_walk_dimension_limit twoColourSystem twoColourSystem_connected
    twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
    twoColourSystem_distancePositive radiusLower radiusUpper radiusLowerPositive radiusUpperPositive
  simpa only [twoColourSystem_massSpectralRadius, twoColourSystem_distanceSpectralRadius,
    twoColourSystem_resistanceSpectralRadius] using actual

end
end EIGS

#print axioms EIGS.twoColourSystem_native_coveringNumber_dimension
#print axioms EIGS.twoColourSystem_diameter_coveringNumber_dimension
#print axioms EIGS.twoColourSystem_terminal_resistance_dimension_limit
#print axioms EIGS.twoColourSystem_degree_mass_logarithmic_ratio
#print axioms EIGS.twoColourSystem_admissible_walk_dimension_limit

