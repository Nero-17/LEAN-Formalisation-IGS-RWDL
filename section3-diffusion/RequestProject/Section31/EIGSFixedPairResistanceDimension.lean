import RequestProject.Section31.EIGSFixedPairResistanceBounds
import RequestProject.Section31.EIGSActualTerminalResistanceDimension
import RequestProject.Section2UnitMetricLimit

/-! The resistance dimension at every fixed pair of distinct finite-born
vertices, using their actual forward images in the unweighted simple graphs.
Both resistance and graph-distance growth are derived internally. -/

namespace EIGS
noncomputable section
open Filter Topology
open scoped Classical
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiSimpleGraph_fixed_pair_distance_canonical_bounds (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (coarse : ℕ) (source sink : XiVtx system coarse) (distinct : source ≠ sink) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ᶠ steps in atTop,
      lower * (system.distanceSpectralRadius connected) ^ steps ≤
        ((XiSimpleGraph system (coarse + steps)).dist
          (xiForward system coarse steps source) (xiForward system coarse steps sink) : ℝ) ∧
      ((XiSimpleGraph system (coarse + steps)).dist
          (xiForward system coarse steps source) (xiForward system coarse steps sink) : ℝ) ≤
        upper * (system.distanceSpectralRadius connected) ^ steps := by
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  have ratePositive : 0 < system.distanceSpectralRadius connected := zero_lt_one.trans rateGreaterThanOne
  obtain ⟨scale, scalePositive, metricLimit⟩ := xiSimpleGraph_all_coarse_pairs_metric_limit system connected
    loopless unique plantingNonadjacent distancePositive parameters.lengthsPositive ratePositive
    parameters.normalized parameters.eigenpair
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  have weightedPositive : 0 < (XiNetwork system coarse).weightedDistance parameters.lengths source sink :=
    (XiNetwork system coarse).weightedDistance_pos (xiSimpleGraph_connected system connected coarse)
      parameters.lengthsPositive source sink distinct
  have scaledPositive : 0 < xiScaledWeightedDistance system parameters.lengths
      (system.distanceSpectralRadius connected) coarse source sink :=
    mul_pos (pow_pos (inv_pos.mpr ratePositive) coarse) weightedPositive
  let limit := (scale * xiScaledWeightedDistance system parameters.lengths
    (system.distanceSpectralRadius connected) coarse source sink) *
      (system.distanceSpectralRadius connected) ^ coarse
  have limitPositive : 0 < limit := mul_pos (mul_pos scalePositive scaledPositive) (pow_pos ratePositive coarse)
  have stepLimit : Tendsto (fun steps =>
      ((XiSimpleGraph system (coarse + steps)).dist
        (xiForward system coarse steps source) (xiForward system coarse steps sink) : ℝ) /
          (system.distanceSpectralRadius connected) ^ steps) atTop (𝓝 limit) := by
    convert (metricLimit coarse source sink).mul_const ((system.distanceSpectralRadius connected) ^ coarse) using 1
    funext steps
    rw [pow_add]
    field_simp [ratePositive.ne']
  refine ⟨limit / 2, 2 * limit, by positivity, by positivity, ?_⟩
  have lower := stepLimit.eventually (lt_mem_nhds (by linarith : limit / 2 < limit))
  have upper := stepLimit.eventually (gt_mem_nhds (by linarith : limit < 2 * limit))
  filter_upwards [lower, upper] with steps lowerBound upperBound
  have powerPositive := pow_pos ratePositive steps
  exact ⟨((lt_div_iff₀ powerPositive).mp lowerBound).le,
    ((div_lt_iff₀ powerPositive).mp upperBound).le⟩

theorem xiSimpleGraph_fixed_pair_resistance_dimension_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (coarse : ℕ) (source sink : XiVtx system coarse) (distinct : source ≠ sink) :
    Tendsto (fun steps =>
      Real.log (effResToBoundary (XiSimpleGraph system (coarse + steps))
        (Finset.univ.erase (xiForward system coarse steps sink)) (xiForward system coarse steps source)) /
      Real.log ((XiSimpleGraph system (coarse + steps)).dist
        (xiForward system coarse steps source) (xiForward system coarse steps sink) : ℝ)) atTop
      (𝓝 (Real.log (system.resistanceSpectralRadius connected distancePositive) /
        Real.log (system.distanceSpectralRadius connected))) := by
  obtain ⟨resistanceLower, resistanceUpper, resistanceLowerPositive, resistanceUpperPositive, resistanceBounds⟩ :=
    xiSimpleGraph_fixed_pair_resistance_canonical_bounds system connected loopless unique plantingNonadjacent
      distancePositive coarse source sink distinct
  have resistanceLog := logarithmic_geometric_scale_limit
    (system.resistanceSpectralRadius_positive_eigenpair connected distancePositive).1
    resistanceLowerPositive resistanceUpperPositive tendsto_id (Filter.Eventually.of_forall resistanceBounds)
  obtain ⟨distanceLower, distanceUpper, distanceLowerPositive, distanceUpperPositive, distanceBounds⟩ :=
    xiSimpleGraph_fixed_pair_distance_canonical_bounds system connected loopless unique plantingNonadjacent
      distancePositive coarse source sink distinct
  have rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  have distanceLog := logarithmic_geometric_scale_limit (zero_lt_one.trans rateGreaterThanOne)
    distanceLowerPositive distanceUpperPositive tendsto_id distanceBounds
  apply (resistanceLog.div distanceLog (Real.log_pos rateGreaterThanOne).ne').congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with steps positive
  have castNonzero : (steps : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  exact div_div_div_cancel_right₀ castNonzero _ _

theorem xiSimpleGraph_fixed_pair_resistanceDimension_eq (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (coarse : ℕ) (source sink : XiVtx system coarse) (distinct : source ≠ sink) :
    resistanceDimension
      (fun steps => effResToBoundary (XiSimpleGraph system (coarse + steps))
        (Finset.univ.erase (xiForward system coarse steps sink)) (xiForward system coarse steps source))
      (fun steps => ((XiSimpleGraph system (coarse + steps)).dist
        (xiForward system coarse steps source) (xiForward system coarse steps sink) : ℝ)) =
      Real.log (system.resistanceSpectralRadius connected distancePositive) /
        Real.log (system.distanceSpectralRadius connected) :=
  (xiSimpleGraph_fixed_pair_resistance_dimension_limit system connected loopless unique plantingNonadjacent
    distancePositive coarse source sink distinct).limUnder_eq

end
end EIGS

#print axioms EIGS.xiSimpleGraph_fixed_pair_distance_canonical_bounds
#print axioms EIGS.xiSimpleGraph_fixed_pair_resistance_dimension_limit
#print axioms EIGS.xiSimpleGraph_fixed_pair_resistanceDimension_eq
