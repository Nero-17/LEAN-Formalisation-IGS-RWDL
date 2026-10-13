import RequestProject.Section31.EIGSContinuousClosabilityWithoutPrimitive
import RequestProject.Section31.EIGSL2QuadraticEnergy

/-! No primitive degree-matrix assumption is needed.

Sequential closability of the actual quadratic form on its native L²
domain. Representatives are recovered through the previously proved injective
continuous-to-L² map; no representative or trace convergence is assumed. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

set_option maxHeartbeats 2400000

variable {K : ℕ}

theorem xiContinuousLpEnergyQuadraticForm_closable_without_primitive (system : EIGSData K)
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
    ∀ sequence : ℕ → xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive,
    (∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair (sequence first - sequence second) < tolerance) →
    Tendsto (fun index => ‖(sequence index).val‖) atTop (nhds 0) →
    Tendsto (fun index => xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair (sequence index)) atTop (nhds 0) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  intro sequence energyCauchy normZero
  let representatives := fun index => (xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm (sequence index)
  have energyIdentity : ∀ values : xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive,
      xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair values =
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values).val ∘
          xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal := by
    intro values
    simpa only [LinearEquiv.apply_symm_apply] using
      xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values)
  have finite : ∀ index, xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      ((representatives index).val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ := by
    intro index
    exact (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).1
      (representatives index).property
  have representativeCauchy : ∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (((representatives first).val - (representatives second).val) ∘
          xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal < tolerance := by
    intro tolerance tolerancePositive
    obtain ⟨threshold, differenceSmall⟩ := energyCauchy tolerance tolerancePositive
    refine ⟨threshold, ?_⟩
    intro first firstAfter second secondAfter
    have comparison := differenceSmall first firstAfter second secondAfter
    rw [energyIdentity] at comparison
    simpa only [map_sub] using comparison
  have representativesNorm : ∀ index,
      ‖(xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass).embed
        (BoundedContinuousFunction.mkOfCompact (representatives index).val)‖ = ‖(sequence index).val‖ := by
    intro index
    have sameClass := congrArg Subtype.val
      ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).apply_symm_apply (sequence index))
    exact congrArg norm sameClass
  have energyZero := xiContinuous_energy_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    (fun index => (representatives index).val) finite representativeCauchy
    (by simpa only [representativesNorm] using normZero)
  simpa only [energyIdentity] using energyZero

end EIGS

#print axioms EIGS.xiContinuousLpEnergyQuadraticForm_closable_without_primitive
