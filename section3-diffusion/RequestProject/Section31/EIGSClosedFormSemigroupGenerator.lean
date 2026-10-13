import RequestProject.Section31.EIGSRegularStronglyLocalDirichlet
import RequestProject.Section31.QuadraticEnergySemigroupGenerator

/-! The same original-rule closed form and canonical Yosida semigroup,
with exact identification of its infinitesimal-generator graph. Metric, mass,
resistance eigenpair, density and closability are constructed from the adopted
five combinatorial conditions. This file does not construct a Hunt process. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped NNReal

set_option maxHeartbeats 3000000

variable {K : ℕ}

def XiClosedSemigroupGeneratorProperties (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily connected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) : Prop :=
    letI := xiCompletion_compactSpace system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let originalDomain := xiContinuousEnergyLpDomain system connected lengths lengthsPositive
        distanceRate distanceRateGreaterThanOne metricEigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive
        distanceRate distanceRateGreaterThanOne metricEigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system connected lengths lengthsPositive
        distanceRate distanceRateGreaterThanOne metricEigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system connected loopless unique plantingNonadjacent
          distancePositive oneColourDistance lengths lengthsPositive
          distanceRate distanceRateGreaterThanOne metricEigenpair mass
          resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass))),
        ∃ semigroup : ℝ≥0 → Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass) →L[ℝ] Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass),
          semigroup = QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense ∧
          (∀ time values, Tendsto (fun index =>
            QuadraticEnergySpace.closedSemigroupApproximation originalDomain originalForm nonnegative closable originalDense
              index time values) atTop (nhds (semigroup time values))) ∧
          (∀ time, ‖semigroup time‖ ≤ 1) ∧
          semigroup 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)) ∧
          (∀ firstTime secondTime, semigroup (firstTime + secondTime) =
            (semigroup firstTime).comp (semigroup secondTime)) ∧
          Continuous (fun point : (Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)) × ℝ≥0 => semigroup point.2 point.1) ∧
          (∀ values, Continuous (fun time => semigroup time values)) ∧
          (∀ values derivative,
            HasDerivWithinAt (fun time : ℝ => semigroup time.toNNReal values)
              derivative (Set.Ici 0) 0 ↔
            ∃ domainValues : QuadraticEnergySpace.generatorDomain originalDomain originalForm nonnegative closable,
              (domainValues : Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate
                distanceRateGreaterThanOne metricEigenpair mass)) = values ∧
              -(QuadraticEnergySpace.closedGenerator originalDomain originalForm nonnegative closable
                originalDense domainValues) = derivative)

theorem xiClosedSemigroupGeneratorProperties_of_dense_core (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily connected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (originalDense : Dense (xiContinuousEnergyLpDomain system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive :
        Set (Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)))) :
    XiClosedSemigroupGeneratorProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  classical
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let originalDomain := xiContinuousEnergyLpDomain system connected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system connected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system connected loopless unique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only [XiClosedSemigroupGeneratorProperties]
  refine ⟨originalDense,
    QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense,
    rfl,
    QuadraticEnergySpace.closedSemigroup_approximation_limit originalDomain originalForm nonnegative closable originalDense,
    QuadraticEnergySpace.closedSemigroup_norm originalDomain originalForm nonnegative closable originalDense,
    QuadraticEnergySpace.closedSemigroup_zero originalDomain originalForm nonnegative closable originalDense,
    QuadraticEnergySpace.closedSemigroup_add originalDomain originalForm nonnegative closable originalDense,
    QuadraticEnergySpace.closedSemigroup_joint_continuous originalDomain originalForm nonnegative closable originalDense, ?_, ?_⟩
  · intro values
    have pairedContinuous : Continuous (fun time : ℝ≥0 => (values, time)) :=
      continuous_const.prodMk continuous_id
    have jointContinuous := QuadraticEnergySpace.closedSemigroup_joint_continuous
      originalDomain originalForm nonnegative closable originalDense
    simpa only [Function.comp_def] using jointContinuous.comp pairedContinuous
  · intro values derivative
    exact QuadraticEnergySpace.closedSemigroup_generator_graph originalDomain originalForm
      nonnegative closable originalDense values derivative

theorem exists_xiClosedFormSemigroupGenerator_of_rules (system : EIGSData K)
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
      XiRegularStronglyLocalDirichletProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
        parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair ∧
      XiClosedSemigroupGeneratorProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
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
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair, ?_, ?_⟩
  · exact xiRegularStronglyLocalDirichletProperties_of_dense_core system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense
  · exact xiClosedSemigroupGeneratorProperties_of_dense_core system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense

end EIGS

#print axioms EIGS.xiClosedSemigroupGeneratorProperties_of_dense_core
#print axioms EIGS.exists_xiClosedFormSemigroupGenerator_of_rules
