import RequestProject.Section31.EIGSL2ClosabilityWithoutPrimitive
import RequestProject.Section31.EIGSL2EnergyContraction
import RequestProject.Section31.QuadraticEnergyClosureContraction

/-! Normal contractions preserve the entire constructed native closed
energy domain and decrease its actual closed quadratic energy. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction

set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiClosedLpEnergy_normal_contraction (system : EIGSData K)
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
    (contraction : ℝ → ℝ) (contractionLipschitz : LipschitzWith 1 contraction)
    (contractionZero : contraction 0 = 0) :
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
    ∀ target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
      ∃ membership : contractionLipschitz.compLp contractionZero target.val ∈
          QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
        QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable
          ⟨contractionLipschitz.compLp contractionZero target.val, membership⟩ ≤
          QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target := by
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
  have coreContraction : ∀ original : originalDomain, ∃ contracted : originalDomain,
      contracted.val = contractionLipschitz.compLp contractionZero original.val ∧
        originalForm contracted ≤ originalForm original := by
    intro original
    obtain ⟨contracted, contractedAE, energyBound⟩ := xiContinuousLpEnergy_normal_contraction
      system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair contraction
      (fun first second => by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        contractionLipschitz.dist_le_mul first second) original
    refine ⟨contracted, ?_, energyBound⟩
    apply Lp.ext
    exact contractedAE.trans (contractionLipschitz.coeFn_compLp contractionZero original.val).symm
  dsimp only
  intro target
  exact QuadraticEnergySpace.closedForm_continuous_core_contraction originalDomain originalForm nonnegative closable
    (contractionLipschitz.compLp contractionZero) (contractionLipschitz.continuous_compLp contractionZero)
    coreContraction target

end EIGS

#print axioms EIGS.xiClosedLpEnergy_normal_contraction
