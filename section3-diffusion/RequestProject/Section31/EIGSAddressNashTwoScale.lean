import RequestProject.Section31.EIGSAddressCellAverageEnergy

/-! A genuine two-scale Nash inequality for the actual continuous trace-energy
domain and actual limit measure. Both averaging estimates are proved in the
imported native construction; neither is assumed as an analytic hypothesis.
Extension to the completed form and the semigroup differential argument are
subsequent steps toward a heat-kernel bound. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiNash_two_scale_bound (system : EIGSData K)
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
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    ∃ energyConstant : ℝ, 0 < energyConstant ∧ ∃ l1Constant : ℝ, 0 < l1Constant ∧
      ∀ (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ →
      ∀ level,
        ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 ≤
        energyConstant / (mass.rate * resistanceRate) ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal +
        l1Constant * mass.rate ^ level *
          (∫ point, |target point| ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass) ^ 2 := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  obtain ⟨errorConstant, errorPositive, errorBound⟩ := exists_xiAddressCellAverage_energy_error_bound system
    rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive
    distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair
  obtain ⟨meanConstant, meanPositive, meanBound⟩ := exists_xiAddressCellAverage_L1_L2_bound system mass
  refine ⟨2 * errorConstant, by positivity, 2 * meanConstant, by positivity, ?_⟩
  intro target targetFinite level
  let pulledTarget : XiEdgeAddress system → ℝ := target ∘ xiAddressLimit system rulesConnected lengths lengthsPositive
    distanceRate distanceRateGreaterThanOne metricEigenpair
  obtain ⟨targetIntegrable, targetSquareIntegrable⟩ := xiContinuous_address_integrable system rulesConnected lengths
    lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass target
  have errorIntegrable : Integrable (fun address =>
      (pulledTarget address - xiAddressCellAverage system mass level pulledTarget address) ^ 2) mass.addressMeasure :=
    integrable_square_sub_finite_coordinate mass.addressMeasure (xiAddressEdge system level)
      (measurable_xiAddressEdge system level) pulledTarget targetIntegrable targetSquareIntegrable
      (xiAddressCellMean system mass level pulledTarget)
  have meanSquareIntegrable : Integrable (fun address =>
      xiAddressCellAverage system mass level pulledTarget address ^ 2) mass.addressMeasure := by
    have zeroSquareIntegrable : Integrable (fun _ : XiEdgeAddress system => (0 : ℝ) ^ 2) mass.addressMeasure := by
      simpa only [zero_pow (by norm_num : 2 ≠ 0)] using (integrable_const (0 : ℝ) :
        Integrable (fun _ : XiEdgeAddress system => (0 : ℝ)) mass.addressMeasure)
    have shifted := integrable_square_sub_finite_coordinate mass.addressMeasure (xiAddressEdge system level)
      (measurable_xiAddressEdge system level) (fun _ => (0 : ℝ)) (integrable_const 0) zeroSquareIntegrable
      (xiAddressCellMean system mass level pulledTarget)
    simpa only [zero_sub, neg_sq] using shifted
  have triangle := integral_mono targetSquareIntegrable
    ((errorIntegrable.const_mul 2).add (meanSquareIntegrable.const_mul 2)) (fun address => by
      nlinarith [sq_nonneg (pulledTarget address - 2 * xiAddressCellAverage system mass level pulledTarget address)])
  rw [integral_add (errorIntegrable.const_mul 2) (meanSquareIntegrable.const_mul 2),
    integral_const_mul, integral_const_mul] at triangle
  have actualError := errorBound target targetFinite level
  have actualMean := meanBound level pulledTarget targetIntegrable
  have mapped := integral_map
    (measurable_xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair).aemeasurable target.continuous.abs.measurable.aestronglyMeasurable
  change (∫ point, |target point| ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass) =
    (∫ address, |pulledTarget address| ∂mass.addressMeasure) at mapped
  rw [← mapped] at actualMean
  have normIdentity := xiContinuous_L2_norm_sq_address_integral system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass target
  rw [normIdentity]
  calc
    _ ≤ 2 * (∫ address, (pulledTarget address - xiAddressCellAverage system mass level pulledTarget address) ^ 2
          ∂mass.addressMeasure) + 2 * (∫ address, xiAddressCellAverage system mass level pulledTarget address ^ 2
          ∂mass.addressMeasure) := triangle
    _ ≤ 2 * (errorConstant / (mass.rate * resistanceRate) ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) +
        2 * (meanConstant * mass.rate ^ level *
          (∫ point, |target point| ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left actualError (by norm_num))
        (mul_le_mul_of_nonneg_left actualMean (by norm_num))
    _ = _ := by ring

theorem exists_xiNash_two_scale_bound_of_rules (system : EIGSData K)
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
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      4 ≤ mass.rate * resistanceRate ∧
    ∃ energyConstant : ℝ, 0 < energyConstant ∧ ∃ l1Constant : ℝ, 0 < l1Constant ∧
      ∀ (target : C(XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair, ℝ)),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair) ≠ ⊤ →
      ∀ level,
        ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 ≤
        energyConstant / (mass.rate * resistanceRate) ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair)).toReal +
        l1Constant * mass.rate ^ level *
          (∫ point, |target point| ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            distanceGreaterThanOne parameters.eigenpair mass) ^ 2 := by
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
  · exact exists_xiNash_two_scale_bound system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair

end
end EIGS

#print axioms EIGS.exists_xiNash_two_scale_bound
#print axioms EIGS.exists_xiNash_two_scale_bound_of_rules
