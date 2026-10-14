import RequestProject.Section31.EIGSOriginalDiameterGrowth
import RequestProject.Section31.EIGSIncidentStarCompletionMesh
import RequestProject.Section2MetricComparison

/-! Uniform comparison of the actual original graph metric divided by its
own unweighted diameter with the canonical native completion metric.
The constants and eventual lower diameter bound are constructed internally. -/

namespace EIGS
open Filter Topology
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem exists_xiOriginalDiameter_native_distance_lower (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∃ comparison : ℝ, 0 < comparison ∧ ∀ᶠ level in atTop,
      ∀ first second : XiVtx system level,
      comparison * (((XiSimpleGraph system level).dist first second : ℝ) /
        xiFiniteLevelDiameter system rulesConnected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level) ≤
        dist (parameters.vertexEmbedding level first) (parameters.vertexEmbedding level second) := by
  intro parameters
  obtain ⟨lengthLower, lengthUpper, lengthLowerPositive, lengthUpperPositive, metricBounds⟩ :=
    xiScaled_unit_distance_comparable system rulesConnected rulesLoopless
      parameters.lengthsPositive parameters.ratePositive
  obtain ⟨diameterLower, diameterUpper, diameterLowerPositive, diameterUpperPositive, diameterBounds⟩ :=
    xiOriginalDiameter_spectral_growth system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  refine ⟨lengthLower * diameterLower, mul_pos lengthLowerPositive diameterLowerPositive, ?_⟩
  filter_upwards [diameterBounds] with level diameterBound
  intro first second
  have powerPositive := pow_pos parameters.ratePositive level
  have diameterPositive := xiFiniteLevelDiameter_positive system rulesConnected (fun _ => (1 : ℝ)⁻¹)
    (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level
  have graphDistanceNonnegative : 0 ≤ ((XiSimpleGraph system level).dist first second : ℝ) := Nat.cast_nonneg _
  have ratioBound :
      (lengthLower * diameterLower) * (((XiSimpleGraph system level).dist first second : ℝ) /
        xiFiniteLevelDiameter system rulesConnected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level) ≤
        lengthLower * ((XiSimpleGraph system level).dist first second : ℝ) /
          (system.distanceSpectralRadius rulesConnected) ^ level := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ diameterPositive powerPositive).mpr
    have multiplied := mul_le_mul_of_nonneg_left diameterBound.1
      (mul_nonneg lengthLowerPositive.le graphDistanceNonnegative)
    convert multiplied using 1 <;> ring
  have nativeEquality :
      dist (parameters.vertexEmbedding level first) (parameters.vertexEmbedding level second) =
      xiScaledWeightedDistance system parameters.lengths
        (system.distanceSpectralRadius rulesConnected) level first second :=
    xiCompletionEmbedding_dist_eq_scaled_weighted system rulesConnected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) parameters.ratePositive
      parameters.eigenpair level first second
  rw [nativeEquality]
  exact ratioBound.trans (metricBounds level first second).1

end
end EIGS

#print axioms EIGS.exists_xiOriginalDiameter_native_distance_lower
