import RequestProject.Section31.EIGSVertexIntegralMarginals
import RequestProject.Section31.EIGSVertexCellGeometry

/-! Actual uniform vertex probabilities and actual degree speed probabilities
converge to the same independently constructed address pushforward. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal Classical BoundedContinuousFunction

noncomputable section

private theorem finite_probability_integral_sub_le_with_exception {Domain : Type*}
    [Fintype Domain] [MeasurableSpace Domain] [DiscreteMeasurableSpace Domain]
    (measure : Measure Domain) [IsProbabilityMeasure measure]
    (first second : Domain → ℝ) (exception : Domain → Prop) [DecidablePred exception]
    (constant coefficient : ℝ)
    (pointwiseBound : ∀ point, ‖first point - second point‖ ≤
      constant + coefficient * (if exception point then 1 else 0)) :
    ‖(∫ point, first point ∂measure) - ∫ point, second point ∂measure‖ ≤
      constant + coefficient * ∫ point, (if exception point then (1 : ℝ) else 0) ∂measure := by
  rw [← integral_sub Integrable.of_finite Integrable.of_finite]
  calc
    _ ≤ ∫ point, ‖first point - second point‖ ∂measure := norm_integral_le_integral_norm _
    _ ≤ ∫ point, (constant + coefficient * (if exception point then (1 : ℝ) else 0)) ∂measure :=
      integral_mono Integrable.of_finite Integrable.of_finite pointwiseBound
    _ = _ := by
      rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const, integral_const_mul]
      simp

variable {K : ℕ} (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

include plantingNonadjacent distancePositive

theorem xiVertexEmpiricalMeasure_integral_tendsto (mass : XiMassParameters system)
    (test : XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair →ᵇ ℝ) :
    Tendsto (fun level => ∫ point, test point ∂
      xiVertexEmpiricalMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair level)
      atTop (𝓝 (∫ point, test point ∂
        xiLimitMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)) := by
  letI := xiCompletion_compactSpace system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  have testUniform := CompactSpace.uniformContinuous_of_continuous test.continuous
  have finiteIntegral : ∀ level,
      (∫ point, test point ∂xiVertexEmpiricalMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair level) =
      ∫ vertex, test (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex) ∂xiVertexCountingMeasure system level := by
    intro level
    exact integral_map Measurable.of_discrete.aemeasurable test.continuous.measurable.aestronglyMeasurable
  have limitIntegral :
      (∫ point, test point ∂xiLimitMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass) =
      ∫ address, test (xiAddressLimit system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair address) ∂mass.addressMeasure :=
    integral_map (measurable_xiAddressLimit system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair).aemeasurable test.continuous.measurable.aestronglyMeasurable
  simp_rw [finiteIntegral, limitIntegral]
  have powerLimit := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le))
    ((inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne)
  have geometryLimit := (powerLimit.mul_const (∑ colour, lengths colour)).add
    ((xiAddressError_tendsto_zero system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair).const_mul 2)
  simp only [zero_mul, mul_zero, zero_add] at geometryLimit
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerancePositive
  obtain ⟨distanceTolerance, distanceTolerancePositive, testDistanceBound⟩ :=
    Metric.uniformContinuous_iff.mp testUniform (tolerance / 4) (by positivity)
  obtain ⟨coarseLevel, geometrySmall, addressErrorSmall⟩ :=
    ((geometryLimit.eventually (eventually_lt_nhds distanceTolerancePositive)).and
      ((xiAddressError_tendsto_zero system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair).eventually (eventually_lt_nhds distanceTolerancePositive))).exists
  let ancestorTest : Option (XiEdge system.toRuleData coarseLevel) → ℝ :=
    Option.elim' 0 (fun edge => test (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair coarseLevel edge))
  have middleLimit := xiVertexCountingMeasure_ancestor_test_limit system ruleConnected
    plantingNonadjacent distancePositive mass coarseLevel ancestorTest
  have oldLimit := xiVertexCountingMeasure_ancestor_test_limit system ruleConnected
    plantingNonadjacent distancePositive mass coarseLevel
      (fun state => if state = none then (1 : ℝ) else 0)
  simp only [Option.some_ne_none, ↓reduceIte, integral_zero] at oldLimit
  have weightedOldLimit := oldLimit.const_mul ‖test‖
  simp only [mul_zero] at weightedOldLimit
  obtain ⟨offsetThreshold, thresholdBound⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp middleLimit (tolerance / 4) (by positivity)).and
      (weightedOldLimit.eventually (eventually_lt_nhds (by positivity : 0 < tolerance / 4))))
  refine ⟨coarseLevel + offsetThreshold, ?_⟩
  intro level levelBound
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le (by omega : coarseLevel ≤ level)
  have offsetBound : offsetThreshold ≤ offset := by omega
  have fineToCoarse :
      ‖(∫ vertex, test (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarseLevel + offset) vertex)
            ∂xiVertexCountingMeasure system (coarseLevel + offset)) -
        (∫ vertex, ancestorTest (xiVertexAncestorEdge system coarseLevel offset vertex)
          ∂xiVertexCountingMeasure system (coarseLevel + offset))‖ < tolerance / 2 := by
    have pointwiseBound : ∀ vertex : XiVtx system (coarseLevel + offset),
        ‖test (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarseLevel + offset) vertex) -
          ancestorTest (xiVertexAncestorEdge system coarseLevel offset vertex)‖ ≤
          tolerance / 4 + ‖test‖ *
            (if xiVertexAncestorEdge system coarseLevel offset vertex = none then 1 else 0) := by
      intro vertex
      cases ancestryEquality : xiVertexAncestorEdge system coarseLevel offset vertex with
      | none =>
          simp only [ancestorTest, Option.elim'_none, ancestryEquality, ↓reduceIte, sub_zero, mul_one]
          exact (test.norm_coe_le_norm _).trans (by linarith)
      | some ancestor =>
          have geometryBound := xiPrivateVertex_to_ancestorTail system ruleConnected lengths lengthsPositive rate
            rateGreaterThanOne eigenpair mass coarseLevel offset ancestor vertex ancestryEquality
          have testBound := testDistanceBound (geometryBound.trans_lt geometrySmall)
          simpa only [ancestorTest, ancestryEquality, Option.elim'_some, Option.some_ne_none,
            ↓reduceIte, mul_zero, add_zero, Real.dist_eq, Real.norm_eq_abs] using testBound.le
    have integralBound := finite_probability_integral_sub_le_with_exception
      (xiVertexCountingMeasure system (coarseLevel + offset)) _ _
      (fun vertex => xiVertexAncestorEdge system coarseLevel offset vertex = none)
      (tolerance / 4) ‖test‖ pointwiseBound
    have oldSmall := (thresholdBound offset offsetBound).2
    linarith
  have coarseToLimit :
      ‖(∫ address, ancestorTest (some (xiAddressEdge system coarseLevel address)) ∂mass.addressMeasure) -
        (∫ address, test (xiAddressLimit system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair address) ∂mass.addressMeasure)‖ ≤ tolerance / 4 := by
    have coarseIntegrable : Integrable
        (fun address => ancestorTest (some (xiAddressEdge system coarseLevel address))) mass.addressMeasure :=
      (Integrable.of_finite (μ := mass.addressMeasure.map (xiAddressEdge system coarseLevel))
        (f := fun edge => ancestorTest (some edge))).comp_measurable
          (measurable_xiAddressEdge system coarseLevel)
    have limitIntegrable : Integrable
        (fun address => test (xiAddressLimit system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair address)) mass.addressMeasure :=
      (test.integrable
        (mass.addressMeasure.map (xiAddressLimit system ruleConnected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair))).comp_measurable
            (measurable_xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    rw [← integral_sub coarseIntegrable limitIntegrable]
    have pointwiseBound : ∀ address,
        ‖ancestorTest (some (xiAddressEdge system coarseLevel address)) -
          test (xiAddressLimit system ruleConnected lengths lengthsPositive rate
            rateGreaterThanOne eigenpair address)‖ ≤ tolerance / 4 := by
      intro address
      have geometryBound := xiAddressLimit_error system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair address coarseLevel
      have testBound := testDistanceBound (geometryBound.trans_lt addressErrorSmall)
      simpa only [ancestorTest, Option.elim'_some, xiAddressTailApproximation, xiEdgeTailPoint,
        Real.dist_eq, Real.norm_eq_abs] using testBound.le
    simpa using norm_integral_le_of_norm_le_const (μ := mass.addressMeasure)
      (Eventually.of_forall pointwiseBound)
  have middleSmall := (thresholdBound offset offsetBound).1
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (∫ vertex, test (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarseLevel + offset) vertex)
        ∂xiVertexCountingMeasure system (coarseLevel + offset))
    (∫ vertex, ancestorTest (xiVertexAncestorEdge system coarseLevel offset vertex)
      ∂xiVertexCountingMeasure system (coarseLevel + offset))
    (∫ address, test (xiAddressLimit system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair address) ∂mass.addressMeasure)
  have coarseTriangle := norm_sub_le_norm_sub_add_norm_sub
    (∫ vertex, ancestorTest (xiVertexAncestorEdge system coarseLevel offset vertex)
      ∂xiVertexCountingMeasure system (coarseLevel + offset))
    (∫ address, ancestorTest (some (xiAddressEdge system coarseLevel address)) ∂mass.addressMeasure)
    (∫ address, test (xiAddressLimit system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair address) ∂mass.addressMeasure)
  simp only [Real.dist_eq, Real.norm_eq_abs] at middleSmall triangle coarseTriangle fineToCoarse coarseToLimit ⊢
  linarith

def xiVertexProbabilityMeasure (level : ℕ) :
    ProbabilityMeasure (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  ⟨xiVertexEmpiricalMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair level,
    inferInstance⟩

theorem xiVertexProbabilityMeasure_tendsto (mass : XiMassParameters system) :
    Tendsto (xiVertexProbabilityMeasure system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair) atTop
      (𝓝 (xiLimitProbabilityMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  exact xiVertexEmpiricalMeasure_integral_tendsto system ruleConnected plantingNonadjacent distancePositive
    lengths lengthsPositive rate rateGreaterThanOne eigenpair mass test

theorem xiVertex_and_speed_same_limit (mass : XiMassParameters system) :
    Tendsto (xiVertexProbabilityMeasure system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair) atTop
      (𝓝 (xiLimitProbabilityMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass)) ∧
    Tendsto (xiSpeedProbabilityMeasure system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass) atTop
      (𝓝 (xiLimitProbabilityMeasure system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass)) :=
  ⟨xiVertexProbabilityMeasure_tendsto system ruleConnected plantingNonadjacent distancePositive
      lengths lengthsPositive rate rateGreaterThanOne eigenpair mass,
    xiSpeedProbabilityMeasure_tendsto system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass⟩

end
end EIGS

#print axioms EIGS.xiVertexEmpiricalMeasure_integral_tendsto
#print axioms EIGS.xiVertexProbabilityMeasure_tendsto
#print axioms EIGS.xiVertex_and_speed_same_limit
