import RequestProject.Section31.EIGSRationalMarkovKernelOfRules
import RequestProject.Section31.FullDiscreteMarkovSubsampling

/-! Actual fixed-step probability path laws for the original-rule rational
Markov family, with full joint-law consistency under natural subsampling and
all dyadic refinements. No projective consistency is assumed. This does not
yet construct a law on the union of the dyadic time grids or Hunt paths. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory NNRat
set_option maxHeartbeats 3000000

variable {X : Type*} [MeasurableSpace X]

noncomputable def rationalSkeletonLaw (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (step : ℚ≥0) (initial : Measure X) :
    Measure (ℕ → X) := by
  letI : IsMarkovKernel (family step) := markov step
  exact pathLaw (family step) initial

def dyadicStep (level : ℕ) : ℚ≥0 := (1 / 2 : ℚ≥0) ^ level

theorem dyadic_refinement_step (level refinement : ℕ) :
    (2 ^ refinement : ℕ) • dyadicStep (level + refinement) = dyadicStep level := by
  rw [nsmul_eq_mul]
  simp only [dyadicStep, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  calc
    (2 : ℚ≥0) ^ refinement * ((1 / 2 : ℚ≥0) ^ level * (1 / 2 : ℚ≥0) ^ refinement) =
        (1 / 2 : ℚ≥0) ^ level * ((2 : ℚ≥0) * (1 / 2 : ℚ≥0)) ^ refinement := by
      rw [mul_pow]
      ring
    _ = (1 / 2 : ℚ≥0) ^ level := by norm_num

theorem rationalSkeletonLaw_subsample (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time))
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (step : ℚ≥0) (initial : Measure X) [IsProbabilityMeasure initial] (stride : ℕ) :
    (rationalSkeletonLaw family markov step initial).map (sampleEvery stride) =
      rationalSkeletonLaw family markov (stride • step) initial := by
  letI : IsMarkovKernel (family step) := markov step
  letI : IsMarkovKernel (family (stride • step)) := markov (stride • step)
  change (pathLaw (family step) initial).map (sampleEvery stride) = pathLaw (family (stride • step)) initial
  simpa only [kernel_pow_fixed_step family zeroLaw addLaw step stride] using
    (pathLaw_sampleEvery (family step) initial stride)

theorem rationalSkeletonLaw_dyadic (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time))
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (level refinement : ℕ) (initial : Measure X) [IsProbabilityMeasure initial] :
    (rationalSkeletonLaw family markov (dyadicStep (level + refinement)) initial).map
        (sampleEvery (2 ^ refinement)) =
      rationalSkeletonLaw family markov (dyadicStep level) initial := by
  rw [rationalSkeletonLaw_subsample family markov zeroLaw addLaw, dyadic_refinement_step]

def RationalSkeletonProperties (measure : Measure X) (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) : Prop :=
  (∀ step initial, IsProbabilityMeasure initial →
    IsProbabilityMeasure (rationalSkeletonLaw family markov step initial)) ∧
  (∀ step initial index,
    (rationalSkeletonLaw family markov step initial).map (fun path => path index) =
      family (index • step) ∘ₘ initial) ∧
  (∀ step point index,
    (rationalSkeletonLaw family markov step (Measure.dirac point)).map (fun path => path index) =
      family (index • step) point) ∧
  (∀ step initial stride, IsProbabilityMeasure initial →
    (rationalSkeletonLaw family markov step initial).map (sampleEvery stride) =
      rationalSkeletonLaw family markov (stride • step) initial) ∧
  (∀ level refinement initial, IsProbabilityMeasure initial →
    (rationalSkeletonLaw family markov (dyadicStep (level + refinement)) initial).map
        (sampleEvery (2 ^ refinement)) =
      rationalSkeletonLaw family markov (dyadicStep level) initial) ∧
  (∀ step index,
    (rationalSkeletonLaw family markov step measure).map (fun path => path index) = measure)

theorem rationalSkeletonProperties_of_family (measure : Measure X) (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time))
    (invariant : ∀ time, (family time).Invariant measure)
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime)) :
    RationalSkeletonProperties measure family markov := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro step initial probability
    letI : IsProbabilityMeasure initial := probability
    letI : IsMarkovKernel (family step) := markov step
    change IsProbabilityMeasure (pathLaw (family step) initial)
    infer_instance
  · intro step initial index
    letI : IsMarkovKernel (family step) := markov step
    change (pathLaw (family step) initial).map (fun path => path index) = _
    rw [pathLaw_coordinate_iterates, kernel_pow_fixed_step family zeroLaw addLaw step index]
  · intro step point index
    letI : IsMarkovKernel (family step) := markov step
    change (pathLaw (family step) (Measure.dirac point)).map (fun path => path index) = _
    rw [pathLaw_coordinate_dirac, kernel_pow_fixed_step family zeroLaw addLaw step index]
  · intro step initial stride probability
    letI : IsProbabilityMeasure initial := probability
    exact rationalSkeletonLaw_subsample family markov zeroLaw addLaw step initial stride
  · intro level refinement initial probability
    letI : IsProbabilityMeasure initial := probability
    exact rationalSkeletonLaw_dyadic family markov zeroLaw addLaw level refinement initial
  · intro step index
    letI : IsMarkovKernel (family step) := markov step
    exact pathLaw_coordinate_stationary (family step) measure (invariant step) index

end IGS.Sec31.DiscreteMarkov

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction NNReal NNRat ProbabilityTheory
set_option maxHeartbeats 3000000
variable {K : ℕ}

def XiRationalMarkovPathLawProperties (system : EIGSData K)
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
        ∃ markov : ∀ time, ProbabilityTheory.IsMarkovKernel (transition time),
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
          transition secondTime ∘ₖ transition firstTime = transition (firstTime + secondTime)) ∧
        DiscreteMarkov.RationalSkeletonProperties
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass) transition markov


theorem xiRationalMarkovPathLawProperties_of_dense_core (system : EIGSData K)
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
    XiRationalMarkovPathLawProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  have kernelProperties := xiRationalMarkovKernelProperties_of_dense_core system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair originalDense
  dsimp only [XiRationalMarkovKernelProperties] at kernelProperties
  obtain ⟨density, kernelForDefault⟩ := kernelProperties
  dsimp only [XiRationalMarkovPathLawProperties]
  refine ⟨density, ?_⟩
  intro defaultPoint
  obtain ⟨transition, markov, representation, invariant, zeroLaw, addLaw⟩ := kernelForDefault defaultPoint
  refine ⟨transition, markov, representation, invariant, zeroLaw, addLaw, ?_⟩
  exact DiscreteMarkov.rationalSkeletonProperties_of_family
    (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass) transition markov invariant zeroLaw addLaw


theorem exists_xiRationalMarkovPathLaw_of_rules (system : EIGSData K)
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
      XiRationalMarkovPathLawProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
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
  exact xiRationalMarkovPathLawProperties_of_dense_core system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense

end EIGS

#print axioms EIGS.xiRationalMarkovPathLawProperties_of_dense_core
#print axioms EIGS.exists_xiRationalMarkovPathLaw_of_rules

#print axioms IGS.Sec31.DiscreteMarkov.dyadic_refinement_step
#print axioms IGS.Sec31.DiscreteMarkov.rationalSkeletonLaw_subsample
#print axioms IGS.Sec31.DiscreteMarkov.rationalSkeletonLaw_dyadic
#print axioms IGS.Sec31.DiscreteMarkov.rationalSkeletonProperties_of_family
