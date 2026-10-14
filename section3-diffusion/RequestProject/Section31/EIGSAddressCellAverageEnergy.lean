import RequestProject.Section31.EIGSAddressHarmonicCellEnergy
import RequestProject.Section31.EIGSL2EnergyDensity

/-! The energy-error half of actual address-cell averaging. Harmonic
projection supplies the L² tail, harmonic endpoint convexity supplies the
coarse-cell constant comparison, and the proved least-square property
selects the actual cell mean. The decay is (mass.rate * resistanceRate)^(-n),
without requiring resistanceRate > 1. -/

namespace IGS.Sec31

 theorem inverse_sqrt_power_square (rate : ℝ) (rateNonnegative : 0 ≤ rate) (level : ℕ) :
    ((Real.sqrt rate)⁻¹ ^ level) ^ 2 = (rate ^ level)⁻¹ := by
  calc
    _ = ((Real.sqrt rate)⁻¹) ^ (2 * level) := by rw [← pow_mul, Nat.mul_comm]
    _ = (rate ^ level)⁻¹ := by rw [pow_mul, inv_pow, Real.sq_sqrt rateNonnegative, inv_pow]

end IGS.Sec31

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiContinuous_L2_norm_sq_address_integral
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair, ℝ)) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair
    ‖(xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair mass).embed
      (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 =
    ∫ address, target (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair address) ^ 2 ∂mass.addressMeasure := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceGreaterThanOne metricEigenpair
  change ‖BoundedContinuousFunction.toLp 2
    (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair mass)
    ℝ (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ point, target point ^ 2 ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair mass := by
      apply integral_congr_ae
      filter_upwards [BoundedContinuousFunction.coeFn_toLp 2
        (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair mass)
        ℝ (BoundedContinuousFunction.mkOfCompact target)] with point equality
      rw [equality]
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      rfl
    _ = _ := integral_map
      (measurable_xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair).aemeasurable
      (target.continuous.measurable.pow_const 2).aestronglyMeasurable

theorem exists_xiAddressCellAverage_energy_error_bound (system : EIGSData K)
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
      ∀ level,
        (∫ address, (target (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair address) -
          xiAddressCellAverage system mass level
            (target ∘ xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair) address) ^ 2 ∂mass.addressMeasure) ≤
        constant / (mass.rate * resistanceRate) ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  have massRatePositive := mass.rate_positive
  have scaleNonnegative : 0 ≤ mass.rate * resistanceRate := (mul_pos mass.rate_positive ratePositive).le
  obtain ⟨tailConstant, tailPositive, tailBound⟩ := exists_xiContinuousHarmonic_native_tail system
    rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair
  obtain ⟨cellConstant, cellPositive, cellBound⟩ := exists_xiCylinder_endpoint_square_energy_bound system mass
    resistanceRate ratePositive resistanceVector vectorPositive
  refine ⟨2 * (tailConstant ^ 2 + cellConstant), by positivity, ?_⟩
  intro target targetFinite level
  obtain ⟨approximation, approximationAgreement, _⟩ := exists_xiContinuousHarmonic_joint_recovery system
    rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
    distancePositive oneColourDistance resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    target targetFinite
  let values : XiVtx system level → ℝ := fun vertex => target (xiCompletionEmbedding system rulesConnected lengths
    lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)
  let pulledTarget : XiEdgeAddress system → ℝ := fun address => target (xiAddressLimit system rulesConnected lengths
    lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair address)
  let pulledHarmonic : XiEdgeAddress system → ℝ := fun address => approximation level (xiAddressLimit system rulesConnected
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair address)
  let anchors : XiEdge system.toRuleData level → ℝ := fun edge => values (XiTail system level edge)
  obtain ⟨targetIntegrable, targetSquareIntegrable⟩ := xiContinuous_address_integrable system rulesConnected lengths
    lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass target
  obtain ⟨harmonicIntegrable, harmonicSquareIntegrable⟩ := xiContinuous_address_integrable system rulesConnected lengths
    lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass (approximation level)
  have differenceSquareIntegrable : Integrable (fun address => (pulledTarget address - pulledHarmonic address) ^ 2)
      mass.addressMeasure := by
    exact (xiContinuous_address_integrable system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass (target - approximation level)).2
  have targetAnchorIntegrable := integrable_square_sub_finite_coordinate mass.addressMeasure (xiAddressEdge system level)
    (measurable_xiAddressEdge system level) pulledTarget targetIntegrable targetSquareIntegrable anchors
  have harmonicAnchorIntegrable := integrable_square_sub_finite_coordinate mass.addressMeasure (xiAddressEdge system level)
    (measurable_xiAddressEdge system level) pulledHarmonic harmonicIntegrable harmonicSquareIntegrable anchors
  have tailEstimate := tailBound target targetFinite level (approximation level) (approximationAgreement level)
  have tailSquared := pow_le_pow_left₀ (norm_nonneg _) tailEstimate 2
  rw [mul_pow, mul_pow, inverse_sqrt_power_square (mass.rate * resistanceRate) scaleNonnegative,
    Real.sq_sqrt ENNReal.toReal_nonneg] at tailSquared
  have differenceNorm := xiContinuous_L2_norm_sq_address_integral system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass (target - approximation level)
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
  have harmonicTailBound := xiContinuousHarmonic_address_tail_square_bound system rulesConnected lengths lengthsPositive
    distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair level values (approximation level) (approximationAgreement level)
  have harmonicIntegralBound :
      (∫ address, (pulledHarmonic address - anchors (xiAddressEdge system level address)) ^ 2 ∂mass.addressMeasure) ≤
      cellConstant / (mass.rate * resistanceRate) ^ level *
        (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal :=
    (harmonicTailBound.trans (cellBound level values)).trans
      (mul_le_mul_of_nonneg_left finiteEnergyBound (by positivity))
  have triangleBound := integral_mono targetAnchorIntegrable
    ((differenceSquareIntegrable.const_mul 2).add (harmonicAnchorIntegrable.const_mul 2))
    (fun address => by
      change (pulledTarget address - anchors (xiAddressEdge system level address)) ^ 2 ≤
        2 * (pulledTarget address - pulledHarmonic address) ^ 2 +
          2 * (pulledHarmonic address - anchors (xiAddressEdge system level address)) ^ 2
      nlinarith [sq_nonneg (pulledTarget address - 2 * pulledHarmonic address + anchors (xiAddressEdge system level address))])
  have triangleIntegral := integral_add (differenceSquareIntegrable.const_mul 2) (harmonicAnchorIntegrable.const_mul 2)
  rw [integral_const_mul, integral_const_mul] at triangleIntegral
  replace triangleBound := triangleBound.trans_eq triangleIntegral
  have meanMinimal := xiAddressCellAverage_minimizes_square_error system mass level pulledTarget
    targetIntegrable targetSquareIntegrable anchors
  calc
    _ ≤ ∫ address, (pulledTarget address - anchors (xiAddressEdge system level address)) ^ 2 ∂mass.addressMeasure := meanMinimal
    _ ≤ 2 * (∫ address, (pulledTarget address - pulledHarmonic address) ^ 2 ∂mass.addressMeasure) +
        2 * (∫ address, (pulledHarmonic address - anchors (xiAddressEdge system level address)) ^ 2 ∂mass.addressMeasure) := triangleBound
    _ ≤ 2 * (tailConstant ^ 2 / (mass.rate * resistanceRate) ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) +
        2 * (cellConstant / (mass.rate * resistanceRate) ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) :=
      add_le_add (mul_le_mul_of_nonneg_left tailIntegralBound (by norm_num))
        (mul_le_mul_of_nonneg_left harmonicIntegralBound (by norm_num))
    _ = _ := by ring

theorem exists_xiAddressCellAverage_energy_error_bound_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      4 ≤ mass.rate * resistanceRate ∧
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (target : C(XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair, ℝ)),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair) ≠ ⊤ →
      ∀ level,
        (∫ address, (target (xiAddressLimit system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            distanceGreaterThanOne parameters.eigenpair address) -
          xiAddressCellAverage system mass level
            (target ∘ xiAddressLimit system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              distanceGreaterThanOne parameters.eigenpair) address) ^ 2 ∂mass.addressMeasure) ≤
        constant / (mass.rate * resistanceRate) ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair)).toReal := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair, _, _⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  dsimp only
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair, ?_, ?_⟩
  · exact xiAnalyticTimeRate_ge_four system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      mass resistanceRate ratePositive resistanceVector vectorPositive (funext renormalizationEigenpair)
  · exact exists_xiAddressCellAverage_energy_error_bound system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair

end
end EIGS

#print axioms IGS.Sec31.inverse_sqrt_power_square
#print axioms EIGS.xiContinuous_L2_norm_sq_address_integral
#print axioms EIGS.exists_xiAddressCellAverage_energy_error_bound
#print axioms EIGS.exists_xiAddressCellAverage_energy_error_bound_of_rules
