import RequestProject.Section31.EIGSSpeedWeakConvergence
import RequestProject.Section31.EIGSAddressGeometry
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Weak convergence of the actual endpoint speed measures in the constructed
compact completion. The original normalized vertex-counting identification
is a separate theorem and is not assumed here. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

private theorem probability_integral_sub_le {Domain : Type*} [MeasurableSpace Domain]
    (measure : Measure Domain) [IsProbabilityMeasure measure]
    {first second : Domain → ℝ} (first_integrable : Integrable first measure)
    (second_integrable : Integrable second measure) {bound : ℝ}
    (pointwise_bound : ∀ point, ‖first point - second point‖ ≤ bound) :
    ‖(∫ point, first point ∂measure) - ∫ point, second point ∂measure‖ ≤ bound := by
  rw [← integral_sub first_integrable second_integrable]
  simpa using norm_integral_le_of_norm_le_const
    (μ := measure) (Filter.Eventually.of_forall pointwise_bound)

variable {K : ℕ} (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

include ruleConnected lengthsPositive rateGreaterThanOne eigenpair

theorem xiAddressError_tendsto_zero :
    Tendsto (fun level : ℕ =>
      (xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ level / (1 - rate⁻¹))
      atTop (𝓝 0) := by
  have inverse_less_than_one : rate⁻¹ < 1 :=
    (inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne
  have power_limit := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)) inverse_less_than_one
  simpa only [mul_zero, zero_div] using
    (power_limit.const_mul (xiRuleRadius system lengths * rate⁻¹)).div_const (1 - rate⁻¹)

theorem xiAddressError_add_le (initialLevel offset : ℕ) :
    (xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ (initialLevel + offset) / (1 - rate⁻¹) ≤
      (xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ initialLevel / (1 - rate⁻¹) := by
  have inverse_nonnegative : 0 ≤ rate⁻¹ := inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)
  have inverse_less_than_one : rate⁻¹ < 1 :=
    (inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr inverse_less_than_one.le)
  have coefficient_nonnegative := mul_nonneg
    (xiRuleRadius_nonnegative system (fun colour => (lengthsPositive colour).le)) inverse_nonnegative
  simpa only [pow_add, mul_assoc] using mul_le_of_le_one_right
    (mul_nonneg coefficient_nonnegative (pow_nonneg inverse_nonnegative initialLevel))
    (pow_le_one₀ inverse_nonnegative inverse_less_than_one.le)

theorem xiTailMeasure_integral_tendsto (mass : XiMassParameters system)
    (test : XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair →ᵇ ℝ) :
    Tendsto (fun level => ∫ point, test point ∂
      xiTailMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level)
      atTop (𝓝 (∫ point, test point ∂
        xiLimitMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)) := by
  letI := xiCompletion_compactSpace system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  have test_uniform := CompactSpace.uniformContinuous_of_continuous test.continuous
  have tail_integral : ∀ level,
      (∫ point, test point ∂xiTailMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level) =
      (∫ edge, test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair level edge) ∂mass.uniformEdgeMeasure level) := by
    intro level
    exact integral_map Measurable.of_discrete.aemeasurable test.continuous.measurable.aestronglyMeasurable
  have limit_integral :
      (∫ point, test point ∂xiLimitMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass) =
      (∫ address, test (xiAddressLimit system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair address) ∂mass.addressMeasure) :=
    integral_map (measurable_xiAddressLimit system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair).aemeasurable test.continuous.measurable.aestronglyMeasurable
  simp_rw [tail_integral, limit_integral]
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerance_positive
  obtain ⟨distance_tolerance, distance_tolerance_positive, test_distance_bound⟩ :=
    Metric.uniformContinuous_iff.mp test_uniform (tolerance / 4) (by positivity)
  have small_errors := (xiAddressError_tendsto_zero system ruleConnected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair).eventually (eventually_lt_nhds (by positivity : 0 < distance_tolerance / 3))
  obtain ⟨initialLevel, initialLevel_bound⟩ := eventually_atTop.mp small_errors
  have initial_error_small := initialLevel_bound initialLevel le_rfl
  have coarse_limit := mass.uniformEdgeMeasure_ancestor_test_limit initialLevel
    (fun edge => test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair initialLevel edge))
  obtain ⟨offsetThreshold, coarse_bound⟩ := Metric.tendsto_atTop.mp coarse_limit
    (tolerance / 4) (by positivity)
  refine ⟨initialLevel + offsetThreshold, ?_⟩
  intro level level_bound
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le (by omega : initialLevel ≤ level)
  have offset_bound : offsetThreshold ≤ offset := by omega
  have fine_to_coarse :
      ‖(∫ edge, test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair (initialLevel + offset) edge)
            ∂mass.uniformEdgeMeasure (initialLevel + offset)) -
        (∫ edge, test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair initialLevel (xiEdgeAncestor system initialLevel offset edge))
            ∂mass.uniformEdgeMeasure (initialLevel + offset))‖ ≤ tolerance / 4 := by
    apply probability_integral_sub_le _ Integrable.of_finite Integrable.of_finite
    intro edge
    have geometry_bound := xiFineTail_to_ancestorTail system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass initialLevel offset edge
    have error_comparison := xiAddressError_add_le system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair initialLevel offset
    have close_points : dist
        (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          (initialLevel + offset) edge)
        (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          initialLevel (xiEdgeAncestor system initialLevel offset edge)) < distance_tolerance := by
      linarith
    simpa only [Real.dist_eq, Real.norm_eq_abs] using (test_distance_bound close_points).le
  have coarse_to_limit :
      ‖(∫ address, test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair initialLevel (xiAddressEdge system initialLevel address))
            ∂mass.addressMeasure) -
        (∫ address, test (xiAddressLimit system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair address) ∂mass.addressMeasure)‖ ≤ tolerance / 4 := by
    have coarse_integrable : Integrable
        (fun address => test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair initialLevel (xiAddressEdge system initialLevel address)))
        mass.addressMeasure := by
      exact (Integrable.of_finite (μ := mass.addressMeasure.map (xiAddressEdge system initialLevel))
        (f := fun edge => test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair initialLevel edge))).comp_measurable
            (measurable_xiAddressEdge system initialLevel)
    have limit_integrable := (test.integrable
      (mass.addressMeasure.map (xiAddressLimit system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair))).comp_measurable
          (measurable_xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    apply probability_integral_sub_le _ coarse_integrable limit_integrable
    intro address
    have geometry_bound := xiAddressLimit_error system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair address initialLevel
    have close_points : dist
        (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          initialLevel (xiAddressEdge system initialLevel address))
        (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address) <
          distance_tolerance := by
      change dist (xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair initialLevel address) _ < _
      linarith
    simpa only [Real.dist_eq, Real.norm_eq_abs] using (test_distance_bound close_points).le
  have middle_bound := coarse_bound offset offset_bound
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (∫ edge, test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair (initialLevel + offset) edge)
          ∂mass.uniformEdgeMeasure (initialLevel + offset))
    (∫ edge, test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair initialLevel (xiEdgeAncestor system initialLevel offset edge))
          ∂mass.uniformEdgeMeasure (initialLevel + offset))
    (∫ address, test (xiAddressLimit system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair address) ∂mass.addressMeasure)
  have triangle_coarse := norm_sub_le_norm_sub_add_norm_sub
    (∫ edge, test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair initialLevel (xiEdgeAncestor system initialLevel offset edge))
          ∂mass.uniformEdgeMeasure (initialLevel + offset))
    (∫ address, test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair initialLevel (xiAddressEdge system initialLevel address))
          ∂mass.addressMeasure)
    (∫ address, test (xiAddressLimit system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair address) ∂mass.addressMeasure)
  simp only [Real.dist_eq, Real.norm_eq_abs] at middle_bound triangle triangle_coarse fine_to_coarse coarse_to_limit ⊢
  linarith

theorem xiHeadTail_integral_sub_tendsto_zero (mass : XiMassParameters system)
    (test : XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair →ᵇ ℝ) :
    Tendsto (fun level =>
      (∫ point, test point ∂xiHeadMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level) -
      (∫ point, test point ∂xiTailMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level)) atTop (𝓝 0) := by
  letI := xiCompletion_compactSpace system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  have test_uniform := CompactSpace.uniformContinuous_of_continuous test.continuous
  have head_integral : ∀ level,
      (∫ point, test point ∂xiHeadMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level) =
      (∫ edge, test (xiEdgeHeadPoint system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair level edge) ∂mass.uniformEdgeMeasure level) := by
    intro level
    exact integral_map Measurable.of_discrete.aemeasurable test.continuous.measurable.aestronglyMeasurable
  have tail_integral : ∀ level,
      (∫ point, test point ∂xiTailMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level) =
      (∫ edge, test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair level edge) ∂mass.uniformEdgeMeasure level) := by
    intro level
    exact integral_map Measurable.of_discrete.aemeasurable test.continuous.measurable.aestronglyMeasurable
  simp_rw [head_integral, tail_integral]
  have lengths_bound : ∀ colour, lengths colour ≤ ∑ otherColour, lengths otherColour := by
    intro colour
    exact Finset.single_le_sum (fun otherColour _ => (lengthsPositive otherColour).le)
      (Finset.mem_univ colour)
  have inverse_nonnegative : 0 ≤ rate⁻¹ := inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)
  have inverse_less_than_one : rate⁻¹ < 1 :=
    (inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne
  have edge_length_limit := (tendsto_pow_atTop_nhds_zero_of_lt_one
    inverse_nonnegative inverse_less_than_one).mul_const (∑ colour, lengths colour)
  simp only [zero_mul] at edge_length_limit
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerance_positive
  obtain ⟨distance_tolerance, distance_tolerance_positive, test_distance_bound⟩ :=
    Metric.uniformContinuous_iff.mp test_uniform (tolerance / 2) (by positivity)
  obtain ⟨threshold, threshold_bound⟩ := eventually_atTop.mp
    (edge_length_limit.eventually (eventually_lt_nhds distance_tolerance_positive))
  refine ⟨threshold, ?_⟩
  intro level level_bound
  have integral_bound :
      ‖(∫ edge, test (xiEdgeHeadPoint system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair level edge) ∂mass.uniformEdgeMeasure level) -
        (∫ edge, test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair level edge) ∂mass.uniformEdgeMeasure level)‖ ≤ tolerance / 2 := by
    apply probability_integral_sub_le _ Integrable.of_finite Integrable.of_finite
    intro edge
    have geometry_bound := xiCompletionEdge_distance_le system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level edge
    have colour_bound := mul_le_mul_of_nonneg_left
      (lengths_bound (XiCol system.toRuleData level edge)) (pow_nonneg inverse_nonnegative level)
    have close_points : dist
        (xiEdgeHeadPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge)
        (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge) <
          distance_tolerance := by
      rw [dist_comm]
      exact (geometry_bound.trans colour_bound).trans_lt (threshold_bound level level_bound)
    simpa only [Real.dist_eq, Real.norm_eq_abs] using (test_distance_bound close_points).le
  simpa only [dist_zero_right] using integral_bound.trans_lt (by linarith : tolerance / 2 < tolerance)

theorem xiHeadMeasure_integral_tendsto (mass : XiMassParameters system)
    (test : XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair →ᵇ ℝ) :
    Tendsto (fun level => ∫ point, test point ∂
      xiHeadMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level)
      atTop (𝓝 (∫ point, test point ∂
        xiLimitMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)) := by
  simpa only [sub_add_cancel, zero_add] using
    (xiHeadTail_integral_sub_tendsto_zero system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass test).add
    (xiTailMeasure_integral_tendsto system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass test)

theorem xiSpeedMeasure_integral_tendsto (mass : XiMassParameters system)
    (test : XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair →ᵇ ℝ) :
    Tendsto (fun level => ∫ point, test point ∂
      xiSpeedMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level)
      atTop (𝓝 (∫ point, test point ∂
        xiLimitMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)) := by
  have speed_integral : ∀ level,
      (∫ point, test point ∂xiSpeedMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level) =
      (1 / 2 : ℝ) * (∫ point, test point ∂xiTailMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level) +
      (1 / 2 : ℝ) * (∫ point, test point ∂xiHeadMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level) := by
    intro level
    rw [xiSpeedMeasure, integral_add_measure
      ((test.integrable _).smul_measure (ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)))
      ((test.integrable _).smul_measure (ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)))]
    simp only [integral_smul_measure, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, smul_eq_mul]
  simp_rw [speed_integral]
  convert ((xiTailMeasure_integral_tendsto system ruleConnected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair mass test).const_mul (1 / 2)).add
    ((xiHeadMeasure_integral_tendsto system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass test).const_mul (1 / 2)) using 1 <;> congr 1 <;> ring

noncomputable def xiSpeedProbabilityMeasure (mass : XiMassParameters system) (level : ℕ) :
    ProbabilityMeasure (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  ⟨xiSpeedMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level,
    inferInstance⟩

noncomputable def xiLimitProbabilityMeasure (mass : XiMassParameters system) :
    ProbabilityMeasure (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  ⟨xiLimitMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass,
    inferInstance⟩

theorem xiSpeedProbabilityMeasure_tendsto (mass : XiMassParameters system) :
    Tendsto (xiSpeedProbabilityMeasure system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass) atTop
      (𝓝 (xiLimitProbabilityMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  exact xiSpeedMeasure_integral_tendsto system ruleConnected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair mass test

end
end EIGS


