import RequestProject.Section31.CoarseModulusScaleSequences
import RequestProject.Section31.EIGSCoarseArrivalDistance

/-! The integer threshold used by the numerical windows is eventually
smaller than any prescribed spatial tolerance in the actual completion.
The resulting path conclusion concerns the actual coarse scanner count.
Probability and tightness assertions are not part of this module. -/

namespace IGS.Sec31

open Filter
open scoped Topology
noncomputable section

theorem coarseModulusSpatialThreshold_le {scale distanceRate coefficient : ℝ}
    (scalePositive : 0 < scale) (distancePositive : 0 < distanceRate)
    (coefficientNonnegative : 0 ≤ coefficient) (level : ℕ) :
    coefficient * (coarseModulusCrossings scale distanceRate level + 2 : ℝ) * distanceRate⁻¹ ^ level ≤
      coefficient * scale + 4 * coefficient * distanceRate⁻¹ ^ level := by
  have crossingUpper := (coarseModulusCrossings_bounds scalePositive distancePositive level).2.2
  have upper : (coarseModulusCrossings scale distanceRate level + 2 : ℝ) ≤ scale * distanceRate ^ level + 4 :=
    by linarith
  have scaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right upper (pow_nonneg (inv_nonneg.mpr distancePositive.le) level))
    coefficientNonnegative
  have cancellation : distanceRate ^ level * distanceRate⁻¹ ^ level = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero level distancePositive.ne')]
  calc
    _ = coefficient * ((coarseModulusCrossings scale distanceRate level + 2 : ℝ) * distanceRate⁻¹ ^ level) := by ring
    _ ≤ coefficient * ((scale * distanceRate ^ level + 4) * distanceRate⁻¹ ^ level) := scaled
    _ = _ := by rw [add_mul, mul_assoc, cancellation, mul_one]; ring

theorem coarseModulusSpatialThreshold_eventually_lt {scale distanceRate coefficient tolerance : ℝ}
    (scalePositive : 0 < scale) (rateGeTwo : 2 ≤ distanceRate) (coefficientPositive : 0 < coefficient)
    (limitingThreshold : coefficient * scale < tolerance) :
    ∀ᶠ level : ℕ in atTop,
      coefficient * (coarseModulusCrossings scale distanceRate level + 2 : ℝ) * distanceRate⁻¹ ^ level <
        tolerance := by
  have distancePositive : 0 < distanceRate := by linarith
  have inverseLimit : Tendsto (fun level : ℕ => distanceRate⁻¹ ^ level) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr distancePositive.le)
      ((inv_lt_one₀ distancePositive).mpr (by linarith))
  have upperLimit : Tendsto (fun level : ℕ =>
      coefficient * scale + 4 * coefficient * distanceRate⁻¹ ^ level) atTop (𝓝 (coefficient * scale)) := by
    simpa using (inverseLimit.const_mul (4 * coefficient)).const_add (coefficient * scale)
  filter_upwards [upperLimit.eventually (gt_mem_nhds limitingThreshold)] with level upper
  exact (coarseModulusSpatialThreshold_le scalePositive distancePositive coefficientPositive.le level).trans_lt upper

end
end IGS.Sec31

namespace EIGS

open Filter IGS.Sec31 IGS.Sec31.DiscreteMarkov
open scoped Topology Classical
noncomputable section
variable {K : ℕ}

theorem xiCoarseModulusSpatialThreshold_eventually_lt (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ coarse : ℕ in atTop,
      (coarseModulusCrossings (tolerance / (2 * (3 * xiRuleRadius system parameters.lengths + 1)))
          (system.distanceSpectralRadius rulesConnected) coarse + 2 : ℝ) *
        ((3 * xiRuleRadius system parameters.lengths + 1) *
          (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) < tolerance := by
  have radiusNonnegative := xiRuleRadius_nonnegative system
    (fun colour => (parameters.lengthsPositive colour).le)
  have coefficientPositive : 0 < 3 * xiRuleRadius system parameters.lengths + 1 := by positivity
  have scalePositive : 0 < tolerance / (2 * (3 * xiRuleRadius system parameters.lengths + 1)) :=
    div_pos tolerancePositive (by positivity)
  have limitingThreshold : (3 * xiRuleRadius system parameters.lengths + 1) *
      (tolerance / (2 * (3 * xiRuleRadius system parameters.lengths + 1))) < tolerance := by
    have cancellation : (3 * xiRuleRadius system parameters.lengths + 1) *
        (tolerance / (2 * (3 * xiRuleRadius system parameters.lengths + 1))) = tolerance / 2 := by
      field_simp [coefficientPositive.ne']
    rw [cancellation]
    linarith
  filter_upwards [IGS.Sec31.coarseModulusSpatialThreshold_eventually_lt scalePositive rateGeTwo
    coefficientPositive limitingThreshold] with coarse small
  convert small using 1 <;> ring

theorem xiCoarseModulusLargeDisplacement_forces_count (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ coarse : ℕ in atTop, ∀ steps (path : ℕ → XiVtx system (coarse + steps)) (horizon : ℕ),
      (∀ index, index < horizon →
        (XiSimpleGraph system (coarse + steps)).Adj (path index) (path (index + 1))) →
      (∃ time, time ≤ horizon ∧ tolerance <
        dist (parameters.vertexEmbedding (coarse + steps) (path time))
          (parameters.vertexEmbedding (coarse + steps) (path 0))) →
      coarseModulusCrossings (tolerance / (2 * (3 * xiRuleRadius system parameters.lengths + 1)))
          (system.distanceSpectralRadius rulesConnected) coarse <
        (coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path horizon).2 := by
  filter_upwards [xiCoarseModulusSpatialThreshold_eventually_lt system rulesConnected parameters
    rateGeTwo tolerancePositive] with coarse threshold
  intro steps path horizon adjacency displacement
  obtain ⟨time, before, farther⟩ := displacement
  apply xiCoarseArrivalState_count_gt_of_displacement system rulesConnected parameters rateGeTwo
    coarse steps path horizon _ adjacency
  exact ⟨time, before, threshold.trans farther⟩

theorem xiCanonicalCoarseModulusLargeDisplacement_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∀ᶠ coarse : ℕ in atTop, ∀ steps (path : ℕ → XiVtx system (coarse + steps)) (horizon : ℕ),
      (∀ index, index < horizon →
        (XiSimpleGraph system (coarse + steps)).Adj (path index) (path (index + 1))) →
      (∃ time, time ≤ horizon ∧ tolerance <
        dist (parameters.vertexEmbedding (coarse + steps) (path time))
          (parameters.vertexEmbedding (coarse + steps) (path 0))) →
      coarseModulusCrossings (tolerance / (2 * (3 * xiRuleRadius system parameters.lengths + 1)))
          (system.distanceSpectralRadius rulesConnected) coarse <
        (coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path horizon).2 := by
  intro parameters
  exact xiCoarseModulusLargeDisplacement_forces_count system rulesConnected parameters
    (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    tolerancePositive

end
end EIGS

#print axioms IGS.Sec31.coarseModulusSpatialThreshold_le
#print axioms IGS.Sec31.coarseModulusSpatialThreshold_eventually_lt
#print axioms EIGS.xiCoarseModulusSpatialThreshold_eventually_lt
#print axioms EIGS.xiCoarseModulusLargeDisplacement_forces_count
#print axioms EIGS.xiCanonicalCoarseModulusLargeDisplacement_of_rules
