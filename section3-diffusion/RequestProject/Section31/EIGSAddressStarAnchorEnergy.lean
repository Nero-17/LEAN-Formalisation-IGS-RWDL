import RequestProject.Section31.EIGSAddressIncidentStar
import RequestProject.Section31.EIGSAddressCellAverageEnergy

/-! Actual local anchor estimates for continuous finite-energy functions.
The address-star term is retained locally, so uniform continuity contributes
its modulus squared times the same star mass. The other error is exactly the
mass-resistance scale. Candidate source; not compiled. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

private theorem weighted_anchor_square_le (anchor harmonic target constant weight oscillation : ℝ)
    (weightNonnegative : 0 ≤ weight) (weightBound : weight ≤ 2)
    (harmonicBound : weight ≠ 0 → (harmonic - anchor) ^ 2 ≤ oscillation ^ 2) :
    weight * (anchor - constant) ^ 2 ≤ 6 * oscillation ^ 2 +
      6 * (target - harmonic) ^ 2 + 3 * weight * (target - constant) ^ 2 := by
  by_cases zero : weight = 0
  · simp only [zero, zero_mul, mul_zero, add_zero]
    positivity
  have threeSquares : (anchor - constant) ^ 2 ≤
      3 * ((harmonic - anchor) ^ 2 + (target - harmonic) ^ 2 + (target - constant) ^ 2) := by
    nlinarith [sq_nonneg ((harmonic - anchor) - (target - harmonic)),
      sq_nonneg ((harmonic - anchor) + (target - constant)),
      sq_nonneg ((target - harmonic) + (target - constant))]
  have multiplied := mul_le_mul_of_nonneg_left threeSquares weightNonnegative
  have harmonicWeighted := mul_le_mul_of_nonneg_left (harmonicBound zero) weightNonnegative
  have oscillationWeighted := mul_le_mul_of_nonneg_right weightBound (sq_nonneg oscillation)
  have tailWeighted := mul_le_mul_of_nonneg_right weightBound (sq_nonneg (target - harmonic))
  nlinarith

theorem xiAddressStarWeight_integrable_mul (system : EIGSData K) (mass : XiMassParameters system)
    (level : ℕ) (vertex : XiVtx system level) (values : XiEdgeAddress system → ℝ)
    (valuesIntegrable : Integrable values mass.addressMeasure) :
    Integrable (fun address => xiAddressStarWeight system level vertex address * values address)
      mass.addressMeasure := by
  apply valuesIntegrable.bdd_mul
  · exact ((measurable_of_countable (xiEdgeStarMultiplicity system level vertex)).comp
      (measurable_xiAddressEdge system level)).aestronglyMeasurable
  · exact Eventually.of_forall fun address => by
      rw [Real.norm_eq_abs, abs_of_nonneg (xiEdgeStarMultiplicity_bounds system level vertex _).1]
      exact (xiEdgeStarMultiplicity_bounds system level vertex _).2

theorem exists_xiAddressStar_anchor_energy_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ →
      ∀ level (vertex : XiVtx system level) (anchor : ℝ),
      (∫ address, xiAddressStarWeight system level vertex address ∂mass.addressMeasure) *
          (target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) - anchor) ^ 2 ≤
        constant / (mass.rate * resistanceRate) ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal +
        3 * ∫ address, xiAddressStarWeight system level vertex address *
          (target (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair address) - anchor) ^ 2 ∂mass.addressMeasure := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  obtain ⟨tailConstant, tailPositive, tailBound⟩ := exists_xiContinuousHarmonic_native_tail system
    rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair
  obtain ⟨cellConstant, cellPositive, cellBound⟩ := exists_xiCylinder_endpoint_square_energy_bound system mass
    resistanceRate ratePositive resistanceVector vectorPositive
  refine ⟨6 * (cellConstant + tailConstant ^ 2), by positivity, ?_⟩
  intro target targetFinite level vertex anchor
  obtain ⟨approximation, approximationAgreement, _⟩ := exists_xiContinuousHarmonic_joint_recovery system
    rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
    distancePositive oneColourDistance resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    target targetFinite
  let values : XiVtx system level → ℝ := fun finiteVertex => target (xiCompletionEmbedding system rulesConnected
    lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level finiteVertex)
  let pulledTarget := target ∘ xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let pulledHarmonic := approximation level ∘ xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  have oscillationIntegrable : Integrable (fun address =>
      (values (XiHead system level (xiAddressEdge system level address)) -
        values (XiTail system level (xiAddressEdge system level address))) ^ 2) mass.addressMeasure :=
    (show Integrable (fun edge : XiEdge system.toRuleData level =>
      (values (XiHead system level edge) - values (XiTail system level edge)) ^ 2)
      (mass.addressMeasure.map (xiAddressEdge system level)) from Integrable.of_finite).comp_measurable
        (measurable_xiAddressEdge system level)
  have tailIntegrable : Integrable (fun address => (pulledTarget address - pulledHarmonic address) ^ 2)
      mass.addressMeasure :=
    (xiContinuous_address_integrable system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass (target - approximation level)).2
  have targetIntegrable := xiContinuous_address_integrable system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass (target - ContinuousMap.const _ anchor)
  have localIntegrable := xiAddressStarWeight_integrable_mul system mass level vertex _ targetIntegrable.2
  have weightIntegrable : Integrable (xiAddressStarWeight system level vertex) mass.addressMeasure :=
    (show Integrable (xiEdgeStarMultiplicity system level vertex)
      (mass.addressMeasure.map (xiAddressEdge system level)) from Integrable.of_finite).comp_measurable
        (measurable_xiAddressEdge system level)
  have pointwiseBound (address : XiEdgeAddress system) :
      xiAddressStarWeight system level vertex address * (values vertex - anchor) ^ 2 ≤
        6 * (values (XiHead system level (xiAddressEdge system level address)) -
          values (XiTail system level (xiAddressEdge system level address))) ^ 2 +
        6 * (pulledTarget address - pulledHarmonic address) ^ 2 +
        3 * (xiAddressStarWeight system level vertex address * (pulledTarget address - anchor) ^ 2) := by
    apply weighted_anchor_square_le _ _ _ _ _ _
      (xiEdgeStarMultiplicity_bounds system level vertex _).1
      (xiEdgeStarMultiplicity_bounds system level vertex _).2
    intro supported
    have range := xiContinuousHarmonic_address_endpoint_range system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair level values (approximation level) (approximationAgreement level) address
    by_cases tail : XiTail system level (xiAddressEdge system level address) = vertex
    · simpa only [tail] using square_distance_to_endpoint_le _ _ _ range.1 range.2
    have head : XiHead system level (xiAddressEdge system level address) = vertex := by
      by_contra different
      exact supported (by simp only [xiAddressStarWeight, xiEdgeStarMultiplicity, if_neg tail, if_neg different, zero_add])
    have reversed := square_distance_to_endpoint_le
      (values (XiHead system level (xiAddressEdge system level address)))
      (values (XiTail system level (xiAddressEdge system level address))) (pulledHarmonic address)
      (by simpa only [min_comm] using range.1) (by simpa only [max_comm] using range.2)
    have squareIdentity :
        (values (XiTail system level (xiAddressEdge system level address)) -
          values (XiHead system level (xiAddressEdge system level address))) ^ 2 =
        (values (XiHead system level (xiAddressEdge system level address)) -
          values (XiTail system level (xiAddressEdge system level address))) ^ 2 := by ring
    simpa only [head, squareIdentity] using reversed
  have integralBound := integral_mono (weightIntegrable.mul_const ((values vertex - anchor) ^ 2))
    (((oscillationIntegrable.const_mul 6).add (tailIntegrable.const_mul 6)).add (localIntegrable.const_mul 3)) pointwiseBound
  rw [integral_mul_const, integral_add
    ((oscillationIntegrable.const_mul 6).add (tailIntegrable.const_mul 6)) (localIntegrable.const_mul 3),
    integral_add (oscillationIntegrable.const_mul 6) (tailIntegrable.const_mul 6),
    integral_const_mul, integral_const_mul, integral_const_mul,
    xiAddress_coordinate_integral] at integralBound
  let targetDomain : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
    ⟨target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair,
      (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).mpr targetFinite⟩
  have finiteEnergyBound := finite_energy_le_traceEnergyValue
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive) targetDomain level
  change (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy values ≤
    (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal at finiteEnergyBound
  have endpointBound := (cellBound level values).trans
    (mul_le_mul_of_nonneg_left finiteEnergyBound (by positivity))
  have tailEstimate := tailBound target targetFinite level (approximation level) (approximationAgreement level)
  have tailSquared := pow_le_pow_left₀ (norm_nonneg
    (core.embed (BoundedContinuousFunction.mkOfCompact target) -
      core.embed (BoundedContinuousFunction.mkOfCompact (approximation level)))) tailEstimate 2
  rw [mul_pow, mul_pow, inverse_sqrt_power_square (mass.rate * resistanceRate)
    (mul_pos mass.rate_positive ratePositive).le, Real.sq_sqrt ENNReal.toReal_nonneg] at tailSquared
  have differenceNorm := xiContinuous_L2_norm_sq_address_integral system rulesConnected lengths lengthsPositive
    distanceRate distanceRateGreaterThanOne metricEigenpair mass (target - approximation level)
  change ‖core.embed (BoundedContinuousFunction.mkOfCompact target -
      BoundedContinuousFunction.mkOfCompact (approximation level))‖ ^ 2 =
    (∫ address, (pulledTarget address - pulledHarmonic address) ^ 2 ∂mass.addressMeasure) at differenceNorm
  rw [map_sub] at differenceNorm
  have tailIntegralBound : (∫ address, (pulledTarget address - pulledHarmonic address) ^ 2 ∂mass.addressMeasure) ≤
      tailConstant ^ 2 / (mass.rate * resistanceRate) ^ level *
        (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal := by
    rw [← differenceNorm]
    simpa only [div_eq_mul_inv] using tailSquared
  have upperBound := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left endpointBound (by norm_num : (0 : ℝ) ≤ 6))
      (mul_le_mul_of_nonneg_left tailIntegralBound (by norm_num : (0 : ℝ) ≤ 6)))
    (le_refl (3 * ∫ address, xiAddressStarWeight system level vertex address *
      (pulledTarget address - anchor) ^ 2 ∂mass.addressMeasure))
  exact integralBound.trans (upperBound.trans_eq (by ring))

end
end EIGS

#print axioms EIGS.xiAddressStarWeight_integrable_mul
#print axioms EIGS.exists_xiAddressStar_anchor_energy_bound
