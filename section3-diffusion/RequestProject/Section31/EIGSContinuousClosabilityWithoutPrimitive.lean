import RequestProject.Section31.EIGSContinuousPointwiseZeroWithoutPrimitive
import RequestProject.Section31.TraceEnergyPointwiseClosability

/-! No primitive degree-matrix assumption is needed.

Closability of the actual continuous finite-energy form. Actual native L²
convergence and bounded energy identify every finite trace; the limit energy
then vanishes for an energy-Cauchy sequence. Closed-domain completion is separate. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction

set_option maxHeartbeats 2400000

variable {K : ℕ}

theorem xiContinuous_energy_closable_without_primitive (system : EIGSData K)
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
    ∀ sequence : ℕ → C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
    (∀ index, xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (sequence index ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤) →
    (∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        ((sequence first - sequence second) ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal < tolerance) →
    Tendsto (fun index => ‖core.embed (BoundedContinuousFunction.mkOfCompact (sequence index))‖) atTop (nhds 0) →
    Tendsto (fun index => (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (sequence index ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) atTop (nhds 0) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  dsimp only
  intro sequence sequenceFinite energyCauchy normZero
  let sequenceDomain : ℕ → xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
    fun index => ⟨sequence index ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair,
      (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).2 (sequenceFinite index)⟩
  have domainCauchy : ∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      traceEnergyValue (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
        (sequenceDomain first - sequenceDomain second) < tolerance := energyCauchy
  obtain ⟨energyBound, _, energiesBounded⟩ := traceEnergyValue_bounded_of_energy_cauchy
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive) sequenceDomain domainCauchy
  have pointwiseZero := xiContinuous_pointwise_zero_of_L2_zero_energy_bounded_without_primitive system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair sequence sequenceFinite energyBound energiesBounded normZero
  exact traceEnergyValue_tendsto_zero_of_energy_cauchy_pointwise
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair) sequenceDomain domainCauchy pointwiseZero

end EIGS

#print axioms EIGS.xiContinuous_energy_closable_without_primitive
