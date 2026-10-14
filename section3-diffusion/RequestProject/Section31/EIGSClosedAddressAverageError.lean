import RequestProject.Section31.EIGSAddressCellAverageEnergy
import RequestProject.Section31.EIGSL2ClosabilityWithoutPrimitive
import RequestProject.Section31.FinitePartitionL2Average
import RequestProject.Section31.QuadraticEnergyFiniteApproximation

/-! Actual finite-address L² averaging of closed-domain elements. The pullback
is an isometry by the already constructed pushforward measure. Closed recovery
extends the proved continuous-core averaging error with its original constants. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def xiAddressL2Embedding (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system) :
    Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass) →ₗᵢ[ℝ] Lp ℝ 2 mass.addressMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair)
    ⟨measurable_xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair, rfl⟩

def xiAddressL2Average (system : EIGSData K) (mass : XiMassParameters system) (level : ℕ) :
    Lp ℝ 2 mass.addressMeasure →L[ℝ] Lp ℝ 2 mass.addressMeasure :=
  finitePartitionL2Average mass.addressMeasure (xiAddressEdge system level)
    (measurable_xiAddressEdge system level) (mass.edgeWeight level)

theorem xiAddressL2Average_compact (system : EIGSData K) (mass : XiMassParameters system) (level : ℕ) :
    IsCompactOperator (xiAddressL2Average system mass level) :=
  finitePartitionL2Average_compact _ _ _ _

theorem exists_xiClosedAddressAverage_error_bound (system : EIGSData K)
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
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair sequence energyCauchy (by simpa using ambientZero.norm)
    let embedding := xiAddressL2Embedding system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative) level,
        ‖embedding target.val - xiAddressL2Average system mass level (embedding target.val)‖ ^ 2 ≤
          constant / (mass.rate * resistanceRate) ^ level *
            QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target := by
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
  let embedding := xiAddressL2Embedding system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  obtain ⟨constant, constantPositive, continuousBound⟩ :=
    exists_xiAddressCellAverage_energy_error_bound system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair
  have originalBound (values : originalDomain) (level : ℕ) :
      ‖embedding values.val - xiAddressL2Average system mass level (embedding values.val)‖ ^ 2 ≤
        constant / (mass.rate * resistanceRate) ^ level * originalForm values := by
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
    let addressMap := xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    have addressMeasurable : Measurable addressMap :=
      measurable_xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair
    have addressPreserving : MeasurePreserving addressMap mass.addressMeasure
        (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass) :=
      ⟨addressMeasurable, rfl⟩
    have pulledAE : (fun address => embedding values.val address) =ᵐ[mass.addressMeasure]
        (fun address => representative.val (addressMap address)) :=
      (Lp.coeFn_compMeasurePreserving values.val addressPreserving).trans
        (ae_eq_comp addressMeasurable.aemeasurable representativeAE)
    have cellIntegralEquality (edge : XiEdge system.toRuleData level) :
        (∫ address in {address | xiAddressEdge system level address = edge}, embedding values.val address ∂mass.addressMeasure) =
        ∫ address in {address | xiAddressEdge system level address = edge}, representative.val (addressMap address) ∂mass.addressMeasure :=
      integral_congr_ae (ae_restrict_of_ae pulledAE)
    have averageAE := finitePartitionL2Average_ae mass.addressMeasure (xiAddressEdge system level)
      (measurable_xiAddressEdge system level) (mass.edgeWeight level) (embedding values.val)
    have residualAE : (fun address =>
        (embedding values.val - xiAddressL2Average system mass level (embedding values.val)) address ^ 2) =ᵐ[mass.addressMeasure]
        (fun address => (representative.val (addressMap address) -
          xiAddressCellAverage system mass level (representative.val ∘ addressMap) address) ^ 2) := by
      filter_upwards [Lp.coeFn_sub (embedding values.val)
        (xiAddressL2Average system mass level (embedding values.val)), pulledAE, averageAE]
        with address subtraction pulled average
      change xiAddressL2Average system mass level (embedding values.val) address = _ at average
      change _ = _ at subtraction
      rw [subtraction]
      change (embedding values.val address - xiAddressL2Average system mass level (embedding values.val) address) ^ 2 = _
      rw [pulled, average, cellIntegralEquality]
      rfl
    rw [L2_norm_sq_eq_integral_square, integral_congr_ae residualAE]
    have bound := continuousBound representative.val representativeFinite level
    rw [representativeEnergy] at bound
    exact bound
  dsimp only
  refine ⟨constant, constantPositive, ?_⟩
  intro target level
  exact QuadraticEnergySpace.closedForm_operator_error_bound originalDomain originalForm nonnegative closable
    embedding.toContinuousLinearMap (xiAddressL2Average system mass level)
    (constant / (mass.rate * resistanceRate) ^ level) (fun values => originalBound values level) target

end
end EIGS

#print axioms EIGS.xiAddressL2Embedding
#print axioms EIGS.xiAddressL2Average_compact
#print axioms EIGS.exists_xiClosedAddressAverage_error_bound
