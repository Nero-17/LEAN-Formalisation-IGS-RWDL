import RequestProject.Section31.EIGSFixedNormalizationRecovery
import RequestProject.Section31.QuadraticEnergyExtended
import Mathlib.Topology.Order.LiminfLimsup

/-! The Mosco upper-bound condition on the whole actual limit L2 space.
The same true resistance normalization is used on every original graph level;
infinite-energy targets are handled by the genuine extended closed energy. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped ENNReal

set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiClosedExtendedEnergy_mosco_recovery (system : EIGSData K)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
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
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∀ target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass),
      ∃ sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level),
        core.Strong sequence target ∧
        Filter.limsup (fun level => ENNReal.ofReal
          (xiNativeScaledUnitEnergy system mass resistanceRate normalization level (sequence level))) atTop ≤
            QuadraticEnergySpace.closedExtendedEnergy originalDomain originalForm nonnegative closable target := by
  classical
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
  dsimp only
  intro target
  by_cases membership : target ∈ QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative
  · obtain ⟨sequence, stateConvergence, energyConvergence⟩ :=
      exists_xiClosed_native_joint_recovery_fixed_normalization_without_primitive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive normalizedConvergence ⟨target, membership⟩
    refine ⟨sequence, stateConvergence, ?_⟩
    have extendedConvergence := ENNReal.continuous_ofReal.continuousAt.tendsto.comp energyConvergence
    rw [QuadraticEnergySpace.closedExtendedEnergy_of_mem originalDomain originalForm nonnegative closable target membership]
    exact extendedConvergence.limsup_eq.le
  · obtain ⟨sequence, stateConvergence⟩ := core.exists_strong_recovery target
    refine ⟨sequence, stateConvergence, ?_⟩
    rw [QuadraticEnergySpace.closedExtendedEnergy_of_not_mem originalDomain originalForm nonnegative closable target membership]
    exact le_top

end EIGS

#print axioms EIGS.xiClosedExtendedEnergy_mosco_recovery
