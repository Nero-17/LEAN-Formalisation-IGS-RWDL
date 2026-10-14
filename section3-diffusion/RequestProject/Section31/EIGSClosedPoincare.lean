import RequestProject.Section31.EIGSAddressPoincare
import RequestProject.Section31.EIGSL2ClosabilityWithoutPrimitive
import RequestProject.Section31.ProbabilityL2PoincareClosure

/-! Actual closed Poincare inequality and zero-energy constancy. The
level-zero actual address average is the global mean. Its proved core error
passes through the actual pushforward law and the proved probability-L²
variance closure theorem. No irreducibility or positivity target is assumed. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def XiClosedPoincareProperties (system : EIGSData K)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) : Prop :=
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    let measure := xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    ∃ constant : ℝ, 0 < constant ∧
      (∀ target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
        (∫ point, (target.val point - ∫ other, target.val other ∂measure) ^ 2 ∂measure) ≤
          constant * QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target) ∧
      ∀ target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
        QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target = 0 →
          ∀ᵐ point ∂measure, target.val point = ∫ other, target.val other ∂measure

theorem xiClosedPoincareProperties (system : EIGSData K)
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
    XiClosedPoincareProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  let measure := xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  obtain ⟨constant, constantPositive, averageError⟩ :=
    exists_xiAddressCellAverage_energy_error_bound system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair
  have originalBound (values : originalDomain) :
      (∫ point, (values.val point - ∫ other, values.val other ∂measure) ^ 2 ∂measure) ≤
        constant * originalForm values := by
    let representative := (xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values
    have representativeFinite : xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (representative.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ :=
      (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).1 representative.property
    have representativeImage : core.embed (BoundedContinuousFunction.mkOfCompact representative.val) = values.val :=
      congrArg Subtype.val ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).apply_symm_apply values)
    have representativeEnergy :
        (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          (representative.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal = originalForm values := by
      symm
      simpa only [representative, originalForm, LinearEquiv.apply_symm_apply] using
        xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair representative
    have representativeAE : (fun point => values.val point) =ᵐ[
        xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass]
        representative.val := by
      rw [← representativeImage]
      exact BoundedContinuousFunction.coeFn_toLp 2 _ ℝ (BoundedContinuousFunction.mkOfCompact representative.val)
    have meanRepresentative : (∫ point, values.val point ∂measure) = ∫ point, representative.val point ∂measure :=
      integral_congr_ae representativeAE
    have varianceRepresentative :
        (∫ point, (values.val point - ∫ other, values.val other ∂measure) ^ 2 ∂measure) =
        ∫ point, (representative.val point - ∫ other, representative.val other ∂measure) ^ 2 ∂measure := by
      rw [meanRepresentative]
      apply integral_congr_ae
      filter_upwards [representativeAE] with point equality
      rw [equality]
    have addressMeasurable := measurable_xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    have meanMapped := integral_map (μ := mass.addressMeasure) addressMeasurable.aemeasurable
      representative.val.continuous.measurable.aestronglyMeasurable
    change (∫ point, representative.val point ∂measure) =
      ∫ address, representative.val (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair address) ∂mass.addressMeasure at meanMapped
    have varianceMeasurable : Measurable (fun point =>
        (representative.val point - ∫ other, representative.val other ∂measure) ^ 2) :=
      ((representative.val.continuous.sub continuous_const).measurable).pow_const 2
    have varianceMapped := integral_map (μ := mass.addressMeasure) addressMeasurable.aemeasurable
      varianceMeasurable.aestronglyMeasurable
    change (∫ point, (representative.val point - ∫ other, representative.val other ∂measure) ^ 2 ∂measure) =
      (∫ address, (representative.val (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair address) - ∫ other, representative.val other ∂measure) ^ 2
          ∂mass.addressMeasure) at varianceMapped
    rw [meanMapped] at varianceRepresentative varianceMapped
    have comparison := averageError representative.val representativeFinite 0
    simp only [pow_zero, div_one, xiAddressCellAverage_zero] at comparison
    rw [representativeEnergy] at comparison
    exact varianceRepresentative.le.trans (varianceMapped.le.trans comparison)
  dsimp only [XiClosedPoincareProperties]
  refine ⟨constant, constantPositive, ?_, ?_⟩
  · intro target
    exact QuadraticEnergySpace.closedForm_variance_bound measure originalDomain originalForm nonnegative closable
      constant originalBound target
  · intro target zeroEnergy
    exact QuadraticEnergySpace.closedForm_ae_eq_mean_of_variance_bound_and_energy_zero measure originalDomain
      originalForm nonnegative closable constant originalBound target zeroEnergy

theorem exists_xiClosedPoincare_of_rules (system : EIGSData K)
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
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      XiClosedPoincareProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        oneColourDistance parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair, _, _⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  dsimp only
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair, ?_⟩
  exact xiClosedPoincareProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      oneColourDistance parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair

end
end EIGS

#print axioms EIGS.xiClosedPoincareProperties
#print axioms EIGS.exists_xiClosedPoincare_of_rules
