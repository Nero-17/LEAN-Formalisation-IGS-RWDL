import RequestProject.Section31.EIGSClosedAddressAverageError
import RequestProject.Section31.EIGSAnalyticTimeScale

/-! Actual bounded closed-energy balls are compact in limit L². The actual
address pullback is an isometry; finite address averages are compact operators
and approximate uniformly on these balls. No cell-boundary or resistanceRate>1
premise is added. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def XiClosedEnergyCompactnessProperties (system : EIGSData K)
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
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair sequence energyCauchy (by simpa using ambientZero.norm)
    ∀ normBound energyBound : ℝ, 0 ≤ energyBound →
      IsCompact (QuadraticEnergySpace.closedEnergyBoundedBall originalDomain originalForm nonnegative closable
        normBound energyBound)

theorem xiClosedEnergyBoundedBall_isCompact (system : EIGSData K)
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
    ∀ normBound energyBound : ℝ, 0 ≤ energyBound →
      IsCompact (QuadraticEnergySpace.closedEnergyBoundedBall originalDomain originalForm nonnegative closable
        normBound energyBound) := by
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
  obtain ⟨constant, constantPositive, closedErrorBound⟩ :=
    exists_xiClosedAddressAverage_error_bound system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  dsimp only
  intro normBound energyBound energyNonnegative
  let boundedSet := QuadraticEnergySpace.closedEnergyBoundedBall originalDomain originalForm nonnegative closable
    normBound energyBound
  have timeRateGreaterOne : 1 < mass.rate * resistanceRate :=
    xiAnalyticTimeRate_gt_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      mass resistanceRate ratePositive resistanceVector vectorPositive (funext renormalizationEigenpair)
  have timeRatePositive : 0 < mass.rate * resistanceRate := zero_lt_one.trans timeRateGreaterOne
  let errors : ℕ → ℝ := fun level => Real.sqrt (constant * energyBound / (mass.rate * resistanceRate) ^ level)
  have coefficientsTendsto : Tendsto
      (fun level : ℕ => constant * energyBound / (mass.rate * resistanceRate) ^ level) atTop (nhds 0) := by
    have inverseLimit := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr timeRatePositive.le)
      ((inv_lt_one₀ timeRatePositive).mpr timeRateGreaterOne)
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using inverseLimit.const_mul (constant * energyBound)
  have errorsTendsto : Tendsto errors atTop (nhds 0) := by
    simpa only [Real.sqrt_zero] using coefficientsTendsto.sqrt
  have errorBound (level : ℕ) (values : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair mass)) (membership : values ∈ boundedSet) :
      ‖embedding values - xiAddressL2Average system mass level (embedding values)‖ ≤ errors level := by
    obtain ⟨_, lifted, liftedEquality, energyBounded⟩ := membership
    have estimate := closedErrorBound lifted level
    rw [liftedEquality] at estimate
    have squareBound :
        ‖embedding values - xiAddressL2Average system mass level (embedding values)‖ ^ 2 ≤
          constant * energyBound / (mass.rate * resistanceRate) ^ level := by
      apply estimate.trans
      have coefficientNonnegative : 0 ≤ constant / (mass.rate * resistanceRate) ^ level := by positivity
      convert mul_le_mul_of_nonneg_left energyBounded coefficientNonnegative using 1 <;> ring
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr squareBound
  have totalBounded : TotallyBounded boundedSet :=
    totallyBounded_of_compact_approximations embedding (xiAddressL2Average system mass)
      (xiAddressL2Average_compact system mass) boundedSet normBound
      (fun values membership => membership.1) errors errorsTendsto errorBound
  exact totalBounded.isCompact_of_isClosed
    (QuadraticEnergySpace.closedEnergyBoundedBall_isClosed originalDomain originalForm nonnegative closable
      normBound energyBound energyNonnegative)

theorem exists_xiClosedEnergyCompactness_of_rules (system : EIGSData K)
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
      XiClosedEnergyCompactnessProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
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
  exact xiClosedEnergyBoundedBall_isCompact system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      oneColourDistance parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair

end
end EIGS

#print axioms EIGS.xiClosedEnergyBoundedBall_isCompact
#print axioms EIGS.exists_xiClosedEnergyCompactness_of_rules
