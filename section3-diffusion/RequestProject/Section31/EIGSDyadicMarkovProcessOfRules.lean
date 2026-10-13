import RequestProject.Section31.DyadicMarkovPathLaw

/-! The actual dyadic total probability process for the original five rules,
with complete enumerated finite-prefix laws and every fixed-time marginal.
The same native quadratic form, density and rational kernel family supply
all inputs internally; no consistency or process-existence premise is added.
Real-time path regularity and Hunt properties remain separate. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory NNRat
set_option maxHeartbeats 3000000

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]

theorem dyadicPathLaw_coordinate (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (initial : Measure X)
    [IsProbabilityMeasure initial] (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (time : DyadicTime) :
    (dyadicPathLaw family markov initial).map (fun path => path time) = family time.val ∘ₘ initial := by
  let count := dyadicEnumeration.symm time
  let lastIndex : Finset.Iic count := ⟨count, Finset.mem_Iic.mpr le_rfl⟩
  have measurable : Measurable
      (fun path : DyadicTime → X => fun index : Finset.Iic count =>
        path (dyadicEnumeration index.val)) := by
    apply measurable_pi_lambda
    intro index
    exact measurable_pi_apply _
  have timeIdentity :
      prefixGridIndex
          (fun index => dyadicTimeLevel (dyadicEnumeration index))
          (fun index => dyadicTimeIndex (dyadicEnumeration index)) count lastIndex •
        dyadicStep (prefixGridLevel
          (fun index => dyadicTimeLevel (dyadicEnumeration index)) count) = time.val := by
    rw [prefixGridIndex_time, ← dyadicTime_representation]
    change (dyadicEnumeration (dyadicEnumeration.symm time)).val = time.val
    rw [Equiv.apply_symm_apply]
  calc
    (dyadicPathLaw family markov initial).map (fun path => path time) =
        ((dyadicPathLaw family markov initial).map
          (fun path (index : Finset.Iic count) => path (dyadicEnumeration index.val))).map
            (fun history => history lastIndex) := by
      rw [Measure.map_map (measurable_pi_apply _) measurable]
      congr 1
      funext path
      change path time = path (dyadicEnumeration (dyadicEnumeration.symm time))
      rw [Equiv.apply_symm_apply]
    _ = (dyadicPrefixLaws family markov initial
        (fun index => dyadicTimeLevel (dyadicEnumeration index))
        (fun index => dyadicTimeIndex (dyadicEnumeration index)) count).map
          (fun history => history lastIndex) := by
      rw [dyadicPathLaw_enumerated_prefix family markov initial zeroLaw addLaw]
    _ = family time.val ∘ₘ initial := by
      unfold dyadicPrefixLaws
      rw [Measure.map_map (measurable_pi_apply _) (dyadicPrefix_measurable _ _ _)]
      letI : IsMarkovKernel (family (dyadicStep (prefixGridLevel
        (fun index => dyadicTimeLevel (dyadicEnumeration index)) count))) := markov _
      change (pathLaw (family (dyadicStep (prefixGridLevel
        (fun index => dyadicTimeLevel (dyadicEnumeration index)) count))) initial).map
          (fun path => path (prefixGridIndex
            (fun index => dyadicTimeLevel (dyadicEnumeration index))
            (fun index => dyadicTimeIndex (dyadicEnumeration index)) count lastIndex)) = _
      rw [pathLaw_coordinate_iterates, kernel_pow_fixed_step family zeroLaw addLaw, timeIdentity]

def DyadicProcessProperties (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) : Prop :=
  ∀ (initial : Measure X) (probability : IsProbabilityMeasure initial),
    letI : IsProbabilityMeasure initial := probability
    ∃ law : Measure (DyadicTime → X), IsProbabilityMeasure law ∧
      (∀ count, law.map (fun path (index : Finset.Iic count) => path (dyadicEnumeration index.val)) =
        dyadicPrefixLaws family markov initial
          (fun index => dyadicTimeLevel (dyadicEnumeration index))
          (fun index => dyadicTimeIndex (dyadicEnumeration index)) count) ∧
      ∀ time : DyadicTime, law.map (fun path => path time) = family time.val ∘ₘ initial

theorem dyadicProcessProperties_of_family (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime)) :
    DyadicProcessProperties family markov := by
  intro initial probability
  letI : IsProbabilityMeasure initial := probability
  exact ⟨dyadicPathLaw family markov initial, inferInstance,
    dyadicPathLaw_enumerated_prefix family markov initial zeroLaw addLaw,
    dyadicPathLaw_coordinate family markov initial zeroLaw addLaw⟩

end IGS.Sec31.DiscreteMarkov


namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction NNReal NNRat ProbabilityTheory
set_option maxHeartbeats 3000000
variable {K : ℕ}

def XiDyadicMarkovProcessProperties (system : EIGSData K)
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
      letI : Nonempty (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) := ⟨defaultPoint⟩
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
            distanceRateGreaterThanOne metricEigenpair mass) transition markov ∧
        DiscreteMarkov.DyadicProcessProperties transition markov


theorem xiDyadicMarkovProcessProperties_of_dense_core (system : EIGSData K)
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
    XiDyadicMarkovProcessProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
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
  dsimp only [XiDyadicMarkovProcessProperties]
  refine ⟨density, ?_⟩
  intro defaultPoint
  obtain ⟨transition, markov, representation, invariant, zeroLaw, addLaw⟩ := kernelForDefault defaultPoint
  letI : Nonempty (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) := ⟨defaultPoint⟩
  refine ⟨transition, markov, representation, invariant, zeroLaw, addLaw, ?_, ?_⟩
  · exact DiscreteMarkov.rationalSkeletonProperties_of_family
      (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass) transition markov invariant zeroLaw addLaw
  · exact DiscreteMarkov.dyadicProcessProperties_of_family transition markov zeroLaw addLaw


theorem exists_xiDyadicMarkovProcess_of_rules (system : EIGSData K)
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
      XiDyadicMarkovProcessProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
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
  exact xiDyadicMarkovProcessProperties_of_dense_core system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense

end EIGS

#print axioms EIGS.xiDyadicMarkovProcessProperties_of_dense_core
#print axioms EIGS.exists_xiDyadicMarkovProcess_of_rules


#print axioms IGS.Sec31.DiscreteMarkov.dyadicPathLaw_coordinate
#print axioms IGS.Sec31.DiscreteMarkov.dyadicProcessProperties_of_family
