import RequestProject.Section31.EIGSClosedNashTwoScale
import RequestProject.Section31.NashTwoScaleOptimization
import RequestProject.Section31.EIGSVertexMassLimits

/-! Exact logarithmic epsilon optimization of the actual closed-domain Nash
inequality. The model supplies mass growth and q = mass.rate * resistanceRate > 1.
No lower bound on the resistance factor alone is required. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def XiClosedNashEpsilonProperties (system : EIGSData K)
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
    ∃ energyConstant : ℝ, 0 < energyConstant ∧ ∃ l1Constant : ℝ, 0 < l1Constant ∧
      ∀ (target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative)
        (tolerance : ℝ), 0 < tolerance → tolerance ≤ energyConstant →
        ‖target.val‖ ^ 2 ≤ tolerance *
          QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target +
        l1Constant * ((mass.rate * resistanceRate) * energyConstant / tolerance) ^
          (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) *
          (∫ point, |target.val point| ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass) ^ 2


theorem xiClosedNashEpsilonProperties (system : EIGSData K)
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
    XiClosedNashEpsilonProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
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
  obtain ⟨energyConstant, energyPositive, l1Constant, l1Positive, closedBound⟩ :=
    xiClosedNashTwoScaleProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have timeRateGreaterThanOne : 1 < mass.rate * resistanceRate :=
    xiAnalyticTimeRate_gt_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      mass resistanceRate ratePositive resistanceVector vectorPositive (funext renormalizationEigenpair)
  have massRateAtLeastOne : 1 ≤ mass.rate :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (mass.rate_ge_two system rulesConnected plantingNonadjacent)
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    (mass.rate * resistanceRate) mass.rate timeRateGreaterThanOne massRateAtLeastOne
  dsimp only [XiClosedNashEpsilonProperties]
  refine ⟨energyConstant, energyPositive, l1Constant, l1Positive, ?_⟩
  intro target tolerance tolerancePositive toleranceAtMost
  exact geometric_two_scale_epsilon_bound (mass.rate * resistanceRate) mass.rate
    (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) energyConstant l1Constant
    (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target)
    ((∫ point, |target.val point| ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass) ^ 2)
    (‖target.val‖ ^ 2) tolerance timeRateGreaterThanOne exponentNonnegative growthIdentity
    energyPositive l1Positive.le
    (QuadraticEnergySpace.closedForm_nonnegative originalDomain originalForm nonnegative closable target)
    (sq_nonneg _) (closedBound target) tolerancePositive toleranceAtMost


theorem exists_xiClosedNash_epsilon_bound_of_rules (system : EIGSData K)
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
      4 ≤ mass.rate * resistanceRate ∧
      XiClosedNashEpsilonProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
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
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair, ?_, ?_⟩
  · exact xiAnalyticTimeRate_ge_four system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      mass resistanceRate ratePositive resistanceVector vectorPositive (funext renormalizationEigenpair)
  · exact xiClosedNashEpsilonProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      oneColourDistance parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair

end
end EIGS

#print axioms EIGS.xiClosedNashEpsilonProperties
#print axioms EIGS.exists_xiClosedNash_epsilon_bound_of_rules


