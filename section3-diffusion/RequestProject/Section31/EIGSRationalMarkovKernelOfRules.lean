import RequestProject.Section31.EIGSMarkovSemigroupKernelOfRules
import RequestProject.Section31.CountableTimeMarkovKernel
import Mathlib.Data.NNRat.Lemmas

/-! A genuine rational-time Markov kernel semigroup constructed from the
corrected original rules. A common stable full-measure set is constructed
internally, and its complement is made absorbing. Thus the rational-time
zero and addition identities hold at every point. Representation of the
original L2 semigroup and invariance of its measure are preserved. This is
not an all-real-time Hunt or continuous-path construction. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction NNReal NNRat ProbabilityTheory
set_option maxHeartbeats 3000000
variable {K : ℕ}

def XiRationalMarkovKernelProperties (system : EIGSData K)
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
    ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass))),
      let semigroup := QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense
      ∀ defaultPoint : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair,
      ∃ transition : ℚ≥0 → ProbabilityTheory.Kernel (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair),
        (∀ time, ProbabilityTheory.IsMarkovKernel (transition time)) ∧
        (∀ (time : ℚ≥0) (values : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
          ∀ᵐ point ∂(xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass),
            ∫ location, values location ∂(transition time point) =
              semigroup (time : ℝ≥0) (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
                distanceRateGreaterThanOne metricEigenpair mass values) point) ∧
        (∀ time, (transition time).Invariant
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass)) ∧
        transition 0 = ProbabilityTheory.Kernel.id ∧
        (∀ firstTime secondTime : ℚ≥0,
          transition secondTime ∘ₖ transition firstTime = transition (firstTime + secondTime))


theorem xiRationalMarkovKernelProperties_of_dense_core (system : EIGSData K)
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
    XiRationalMarkovKernelProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
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
  have kernelProperties := xiMarkovSemigroupKernelProperties_of_dense_core system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair originalDense
  dsimp only [XiMarkovSemigroupKernelProperties] at kernelProperties
  obtain ⟨density, kernelForDefault⟩ := kernelProperties
  let nativeMeasure := xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  let tests := CountableMarkov.rationalTests (X := XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
  dsimp only [XiRationalMarkovKernelProperties]
  refine ⟨density, ?_⟩
  intro defaultPoint
  obtain ⟨transition, markov, representation, invariant, addLaw⟩ := kernelForDefault defaultPoint
  letI : ProbabilityTheory.IsMarkovKernel (transition 0) := markov 0
  have zeroLaw : ∀ᵐ point ∂nativeMeasure, transition 0 point = ProbabilityTheory.Kernel.id point := by
    apply CountableMarkov.ae_kernel_eq_id_of_identity_representation nativeMeasure (transition 0)
      tests CountableMarkov.rationalTests_dense
    intro values
    simpa only [QuadraticEnergySpace.closedSemigroup_zero, ContinuousLinearMap.id_apply]
      using representation 0 values
  let rationalTransition := fun time : ℚ≥0 => transition (time : ℝ≥0)
  letI : Countable ℚ≥0 := NNRat.coe_injective.countable
  have rationalZero : ∀ᵐ point ∂nativeMeasure,
      rationalTransition 0 point = ProbabilityTheory.Kernel.id point := by
    simpa only [rationalTransition, NNRat.cast_zero] using zeroLaw
  have rationalAdd : ∀ firstTime secondTime : ℚ≥0, ∀ᵐ point ∂nativeMeasure,
      (rationalTransition secondTime ∘ₖ rationalTransition firstTime) point =
        rationalTransition (firstTime + secondTime) point := by
    intro firstTime secondTime
    simpa only [rationalTransition, NNRat.cast_add] using
      addLaw (firstTime : ℝ≥0) (secondTime : ℝ≥0)
  obtain ⟨modified, modifiedMarkov, modifiedInvariant, sameAE, modifiedZero, modifiedAdd⟩ :=
    CountableMarkov.exists_countable_time_markov_modification nativeMeasure rationalTransition
      (fun time => markov (time : ℝ≥0)) (fun time => invariant (time : ℝ≥0)) rationalZero rationalAdd
  refine ⟨modified, modifiedMarkov, ?_, modifiedInvariant, modifiedZero, modifiedAdd⟩
  intro time values
  filter_upwards [sameAE time, representation (time : ℝ≥0) values]
    with point modifiedIdentity originalIdentity
  rw [modifiedIdentity]
  exact originalIdentity



theorem exists_xiRationalMarkovKernel_of_rules (system : EIGSData K)
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
      XiRationalMarkovKernelProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
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
  exact xiRationalMarkovKernelProperties_of_dense_core system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense

end EIGS

#print axioms EIGS.xiRationalMarkovKernelProperties_of_dense_core
#print axioms EIGS.exists_xiRationalMarkovKernel_of_rules
