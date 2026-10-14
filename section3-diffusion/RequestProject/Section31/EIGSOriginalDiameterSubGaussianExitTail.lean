import RequestProject.Section31.EIGSNativeSubGaussianMaximalTail
import RequestProject.Section31.EIGSOriginalDiameterNativeDistanceLower
import RequestProject.Section31.GraphFloorExitRadiusEvent
import RequestProject.Section31.EIGSFiniteHorizonStepPathLawOfRules

/-! The paper's optimized finite exit estimate for the original unweighted
graph distance divided by its actual diameter. The first exit is literal
graphFloorExitTime. All rules, time and metric comparisons are discharged
internally, with no target tail or Azuma hypothesis. -/

namespace EIGS
open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

def xiOriginalDiameterGraphBall (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (level : ℕ) (center : XiVtx system level) (radius : ℝ) : Finset (XiVtx system level) :=
  finiteGraphBall (XiSimpleGraph system level) center
    (radius * xiFiniteLevelDiameter system rulesConnected (fun _ => (1 : ℝ)⁻¹)
      (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level)

theorem exists_xiOriginalDiameterSubGaussianExitTail_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    [∀ level, MeasurableSpace (XiVtx system level)]
    [∀ level, MeasurableSingletonClass (XiVtx system level)] :
    let walkExponent := Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive) /
        Real.log (system.distanceSpectralRadius rulesConnected)
    let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive
    ∃ constant coefficient cutoff : ℝ, 0 < constant ∧ 0 < coefficient ∧ 0 < cutoff ∧
      ∀ᶠ level in atTop, ∀ (start : XiVtx system level) (radius : ℝ) (time : ℝ≥0),
        0 < radius → radius ≤ 1 → 0 < time → (time : ℝ) ≤ cutoff * radius ^ walkExponent →
      ((xiGraphWalkPathLaw system rulesConnected level start)
        {path | graphFloorExitTime (xiOriginalDiameterGraphBall system rulesConnected level start radius)
          (rates level) path ≤ (time : ℝ≥0∞)}).toReal ≤
        constant * Real.exp (-coefficient * (radius ^ walkExponent / (time : ℝ)) ^ (1 / (walkExponent - 1))) := by
  intro walkExponent rates
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceRate := system.distanceSpectralRadius rulesConnected
  let timeRate := realMatrixSpectralRadius (massMatrixR system.toRuleData) *
    system.resistanceSpectralRadius rulesConnected distancePositive
  have distanceGeTwo : 2 ≤ distanceRate :=
    system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive
  have distanceGreaterThanOne : 1 < distanceRate := by linarith
  have distancePositiveRate := zero_lt_one.trans distanceGreaterThanOne
  have squareBound : distanceRate ^ 2 ≤ timeRate :=
    system.distanceSpectralRadius_sq_le_mass_mul_resistance rulesConnected rulesLoopless rulesUnique distancePositive
  have timeGreaterThanDistance : distanceRate < timeRate := by nlinarith
  have walkGreaterThanOne : 1 < walkExponent :=
    (one_lt_div (Real.log_pos distanceGreaterThanOne)).mpr
      (Real.log_lt_log distancePositiveRate timeGreaterThanDistance)
  have exponentPositive : 0 < 1 / (walkExponent - 1) :=
    div_pos zero_lt_one (sub_pos.mpr walkGreaterThanOne)
  obtain ⟨constant, nativeCoefficient, nativeCutoff, constantPositive, nativeCoefficientPositive,
      nativeCutoffPositive, nativeTail⟩ :=
    exists_xiNativeSubGaussianMaximalTail_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  obtain ⟨comparison, comparisonPositive, metricComparison⟩ :=
    exists_xiOriginalDiameter_native_distance_lower system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  let coefficient := nativeCoefficient * (comparison ^ walkExponent) ^ (1 / (walkExponent - 1))
  have coefficientPositive : 0 < coefficient := by dsimp [coefficient]; positivity
  refine ⟨constant, coefficient, nativeCutoff * comparison, constantPositive, coefficientPositive,
    mul_pos nativeCutoffPositive comparisonPositive, ?_⟩
  filter_upwards [metricComparison] with level comparisonBound
  intro start radius time radiusPositive radiusSmall timePositive timeSmall
  have timeRealPositive : 0 < (time : ℝ) := timePositive
  have radiusPowerAtMost : radius ^ walkExponent ≤ radius := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge radiusPositive radiusSmall walkGreaterThanOne.le
  have nativeTimeSmall : (time : ℝ) ≤ nativeCutoff * (comparison * radius) := by
    have multiplied := mul_le_mul_of_nonneg_left radiusPowerAtMost
      (mul_pos nativeCutoffPositive comparisonPositive).le
    exact timeSmall.trans (by convert multiplied using 1 <;> ring)
  have diameterPositive := xiFiniteLevelDiameter_positive system rulesConnected (fun _ => (1 : ℝ)⁻¹)
    (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level
  have inclusion :
      {path | graphFloorExitTime (xiOriginalDiameterGraphBall system rulesConnected level start radius)
        (rates level) path ≤ (time : ℝ≥0∞)} ⊆
      xiNativeMaximalDisplacementEvent system rulesConnected parameters level
        ⌊xiNativeFiniteJumpRate system level
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * (time : ℝ)⌋₊
        start (comparison * radius) := by
    intro path escaped
    obtain ⟨index, bounded, outside⟩ :=
      (graphFloorBallExitTime_le_iff_maximal_graph_distance (XiSimpleGraph system level) start
        (radius * xiFiniteLevelDiameter system rulesConnected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level) (rates level)
        (xiNativeFiniteJumpRateNNReal_positive system rulesConnected distancePositive normalization normalizationPositive level)
        path time).mp escaped
    refine ⟨index, ?_, ?_⟩
    · simpa only [rates, xiNativeFiniteJumpRateNNReal, NNReal.coe_mk, mul_comm] using bounded
    · have ratioLower : radius ≤ ((XiSimpleGraph system level).dist start (path index) : ℝ) /
          xiFiniteLevelDiameter system rulesConnected (fun _ => (1 : ℝ)⁻¹)
            (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level :=
        (le_div_iff₀ diameterPositive).mpr outside
      have multiplied := mul_le_mul_of_nonneg_left ratioLower comparisonPositive.le
      simpa only [dist_comm] using multiplied.trans (comparisonBound start (path index))
  let law := xiGraphWalkPathLaw system rulesConnected level start
  haveI : IsProbabilityMeasure law := by dsimp [law, xiGraphWalkPathLaw]; infer_instance
  have transferred := measureReal_mono (μ := law) inclusion
  have actual := nativeTail level start (comparison * radius) (time : ℝ)
    (mul_pos comparisonPositive radiusPositive) timeRealPositive nativeTimeSmall
  have combined := transferred.trans actual
  have scaledPower : ((comparison * radius) ^ walkExponent / (time : ℝ)) ^ (1 / (walkExponent - 1)) =
      (comparison ^ walkExponent) ^ (1 / (walkExponent - 1)) *
        (radius ^ walkExponent / (time : ℝ)) ^ (1 / (walkExponent - 1)) := by
    rw [Real.mul_rpow comparisonPositive.le radiusPositive.le, mul_div_assoc,
      Real.mul_rpow (Real.rpow_nonneg comparisonPositive.le _)
        (div_nonneg (Real.rpow_nonneg radiusPositive.le _) timeRealPositive.le)]
  convert combined using 1
  congr 2
  rw [scaledPower]
  dsimp only [coefficient]
  ring

end
end EIGS

#print axioms EIGS.exists_xiOriginalDiameterSubGaussianExitTail_of_rules
