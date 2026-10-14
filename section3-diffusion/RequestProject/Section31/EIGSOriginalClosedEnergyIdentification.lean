import RequestProject.Section31.EIGSOriginalEnergyCompleteness
import RequestProject.Section31.QuadraticEnergyOriginalClosedIdentification

/-! The original continuous energy domain is already closed when the given
actual resistance eigenvalue exceeds one. Harmonic contraction, restriction
bijection, bounded extension and original graph-norm completeness are supplied
internally from original rule assumptions for that very same eigenpair.
This permits identification with the already constructed closed semigroup and
Brownian family without selecting another energy vector or process.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31 MeasureTheory
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiOriginal_closedDomain_eq
    (system : EIGSData K)
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
    (resistanceRate : ℝ) (rateGreaterThanOne : 1 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour) :
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate (zero_lt_one.trans rateGreaterThanOne)
      resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate (zero_lt_one.trans rateGreaterThanOne)
      resistanceVector vectorPositive eigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate (zero_lt_one.trans rateGreaterThanOne)
      resistanceVector vectorPositive eigenpair
    QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative = originalDomain := by
  let ratePositive := zero_lt_one.trans rateGreaterThanOne
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
    distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair profiles profilesPlus profilesMinus profilesMinimal contractionFactor profilesOscillation
  have bijective : Function.Bijective (xiFiniteEnergyRestriction system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) :=
    ⟨xiFiniteEnergyRestriction_injective system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive,
      xiFiniteEnergyRestriction_surjective_of_step_contraction system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate rateGreaterThanOne resistanceVector vectorPositive
        eigenpair contractionFactor factorPositive factorStrict stepContraction⟩
  obtain ⟨extension, agreement⟩ := exists_xiAnchoredEnergy_continuous_linear_extension_of_bijective system rulesConnected
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair (xiVertexEmbedding system 0 true) bijective
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  letI : CompleteSpace (QuadraticEnergySpace originalDomain originalForm nonnegative) :=
    xiOriginalEnergySpace_complete_of_anchored_extension system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive eigenpair bijective extension agreement
  exact QuadraticEnergySpace.closedDomain_eq_original_of_complete originalDomain originalForm nonnegative

end
end EIGS

#print axioms EIGS.xiOriginal_closedDomain_eq
