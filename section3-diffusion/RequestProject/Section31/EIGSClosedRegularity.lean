import RequestProject.Section31.EIGSL2ClosabilityWithoutPrimitive
import RequestProject.Section31.EIGSHarmonicDensity
import RequestProject.Section31.EIGSHarmonicL2Density
import RequestProject.Section31.QuadraticEnergyCoreDensity

/-! The actual continuous finite-energy core is uniformly dense in C(X)
and dense in the constructed closed energy-plus-L2 norm. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31

set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiClosedLpEnergy_regular_core (system : EIGSData K)
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
    (∀ (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)) (tolerance : ℝ), 0 < tolerance →
      ∃ approximation : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive,
        ∀ point, |approximation.val point - target point| < tolerance) ∧
    (∀ target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
      ∃ sequence : ℕ → originalDomain,
        Tendsto (fun index => QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable
          (⟨(sequence index).val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (sequence index)⟩ - target) +
            ‖(sequence index).val - target.val‖ ^ 2) atTop (nhds 0)) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
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
  dsimp only
  constructor
  · intro target tolerance tolerancePositive
    obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
        profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
      distancePositive oneColourDistance resistanceVector vectorPositive
    have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair profiles profilesPlus profilesMinus profilesMinimal contractionFactor profilesOscillation
    obtain ⟨level, values, extension, extensionValues, approximationBound⟩ :=
      exists_xiHarmonic_uniform_approximation_of_step_contraction system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        contractionFactor factorPositive factorStrict stepContraction target
        (CompactSpace.uniformContinuous_of_continuous target.continuous) tolerance tolerancePositive
    have extensionEnergy := xiContinuousHarmonic_extended_energy system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair level values extension extensionValues
    have extensionFinite : extension ∈ xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive := by
      apply (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).2
      exact ne_of_eq_of_ne extensionEnergy ENNReal.ofReal_ne_top
    exact ⟨⟨extension, extensionFinite⟩, approximationBound⟩
  · intro target
    exact QuadraticEnergySpace.exists_original_closed_energy_approximation originalDomain originalForm nonnegative closable target

end EIGS

#print axioms EIGS.xiClosedLpEnergy_regular_core
