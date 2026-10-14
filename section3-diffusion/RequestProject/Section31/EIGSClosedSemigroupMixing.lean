import RequestProject.Section31.EIGSClosedPoincare
import RequestProject.Section31.EIGSClosedSemigroupAnalyticBounds
import RequestProject.Section31.ProbabilityL2SemigroupMixing

/-! The actual closed L² semigroup converges to the invariant mean along
integer times. Poincaré, smoothing, and preservation of the native constant
one are supplied by the proved model. This is not a positivity-improvement
or strict-positive heat-kernel assertion. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction NNReal
set_option maxHeartbeats 3000000
variable {K : ℕ}

def XiClosedSemigroupMixingProperties (system : EIGSData K)
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
    let measure := xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 measure)),
      ∃ constant : ℝ, 0 < constant ∧
        (∀ (time : ℝ≥0), 0 < time → ∀ forcing : Lp ℝ 2 measure,
          ‖probabilityL2MeanZeroProjection measure
            (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
              originalDense time forcing)‖ ^ 2 ≤ constant * (‖forcing‖ ^ 2 / (2 * (time : ℝ)))) ∧
        ∀ forcing : Lp ℝ 2 measure,
          Tendsto (fun index : ℕ => QuadraticEnergySpace.closedSemigroup originalDomain originalForm
            nonnegative closable originalDense (index + 1) forcing) atTop
            (𝓝 ((∫ point, forcing point ∂measure) • Lp.const 2 measure (1 : ℝ)))


theorem xiClosedSemigroupMixingProperties_of_dense_core (system : EIGSData K)
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
    (originalDense : Dense (xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)))) :
    XiClosedSemigroupMixingProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
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
  have poincare := xiClosedPoincareProperties system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair
  dsimp only [XiClosedPoincareProperties] at poincare
  obtain ⟨constant, constantPositive, varianceBound, zeroEnergyConstant⟩ := poincare
  dsimp only [XiClosedSemigroupMixingProperties]
  refine ⟨originalDense, constant, constantPositive, ?_, ?_⟩
  · intro time timePositive forcing
    exact QuadraticEnergySpace.closedSemigroup_mean_zero_projection_bound
      (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)
      originalDomain originalForm nonnegative closable originalDense constant constantPositive.le
      varianceBound time timePositive forcing
  · intro forcing
    exact QuadraticEnergySpace.closedSemigroup_tendsto_mean
      (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)
      originalDomain originalForm nonnegative closable originalDense constant constantPositive.le varianceBound
      (xiContinuousLpEnergyConstant system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive 1)
      (xiContinuousLpEnergyConstant_energy system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair 1)
      (xiContinuousLpEnergyConstant_ae system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive 1) forcing


theorem exists_xiClosedSemigroupMixing_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (connected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      XiClosedSemigroupMixingProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
        parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  classical
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system connected distancePositive
  letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (connected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system connected loopless unique plantingNonadjacent distancePositive
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair, ?_⟩
  exact xiClosedSemigroupMixingProperties_of_dense_core system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense

end EIGS

#print axioms EIGS.xiClosedSemigroupMixingProperties_of_dense_core
#print axioms EIGS.exists_xiClosedSemigroupMixing_of_rules


