import RequestProject.Section31.EIGSStationaryFinitePrefixWeakLimit
import RequestProject.Section31.EIGSDyadicMarkovProcessOfRules

/-! Genuine finite-dimensional weak limits at arbitrary finitely many dyadic
times. The native and limit laws are the actual constructed dyadic path laws.
A common fine-grid prefix and its continuous coordinate projection connect
them to the already-proved stationary fixed-step finite-prefix weak limit. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter Topology
open scoped BigOperators ProbabilityTheory NNRat BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 4000000

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]

/-- Stationary finite-prefix laws depend on the actual L2 operator, even
when two representing kernels differ on exceptional starting points. -/
theorem finitePrefixProbability_eq_of_same_operator (measure : ProbabilityMeasure Space)
    (operator : Lp ℝ 2 (measure : Measure Space) →L[ℝ] Lp ℝ 2 (measure : Measure Space))
    (first second : Kernel Space Space) [IsMarkovKernel first] [IsMarkovKernel second]
    (firstInvariant : first.Invariant (measure : Measure Space))
    (secondInvariant : second.Invariant (measure : Measure Space))
    (firstRepresentation : ∀ values : C(Space, ℝ), ∀ᵐ point ∂(measure : Measure Space),
      (∫ target, values target ∂first point) = operator (ContinuousMap.toLp 2 (measure : Measure Space) ℝ values) point)
    (secondRepresentation : ∀ values : C(Space, ℝ), ∀ᵐ point ∂(measure : Measure Space),
      (∫ target, values target ∂second point) = operator (ContinuousMap.toLp 2 (measure : Measure Space) ℝ values) point)
    (count : ℕ) : finitePrefixProbability first measure count = finitePrefixProbability second measure count := by
  have convergence : Tendsto (fun _ : ℕ => finitePrefixProbability first measure count) atTop
      (nhds (finitePrefixProbability second measure count)) := by
    apply FiniteProductWeak.weak_tendsto_of_product_integrals
    intro tests
    have integralEquality :
        (∫ history : Finset.Iic count → Space, ∏ index, tests index (history index)
          ∂(finitePrefixProbability first measure count : Measure _)) =
        ∫ history : Finset.Iic count → Space, ∏ index, tests index (history index)
          ∂(finitePrefixProbability second measure count : Measure _) := by
      rw [FixedStepPrefixWeak.finitePrefixProbability_integral_product,
        FixedStepPrefixWeak.finitePrefixProbability_integral_product,
        continuous_pathLaw_prefix_integral_operator measure first firstInvariant operator firstRepresentation,
        continuous_pathLaw_prefix_integral_operator measure second secondInvariant operator secondRepresentation]
    simpa only [integralEquality] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        ∫ history : Finset.Iic count → Space, ∏ index, tests index (history index)
          ∂(finitePrefixProbability second measure count : Measure _)) atTop (nhds _))
  exact tendsto_nhds_unique tendsto_const_nhds convergence

variable {Coordinates : Type*} [Fintype Coordinates]

def finiteDyadicEnumerationBound (times : Coordinates → DyadicTime) : ℕ :=
  Finset.univ.sup (fun coordinate => dyadicEnumeration.symm (times coordinate))

def finiteDyadicEnumerationIndex (times : Coordinates → DyadicTime) (coordinate : Coordinates) :
    Finset.Iic (finiteDyadicEnumerationBound times) :=
  ⟨dyadicEnumeration.symm (times coordinate), Finset.mem_Iic.mpr
    (Finset.le_sup (f := fun index => dyadicEnumeration.symm (times index)) (Finset.mem_univ coordinate))⟩

def finiteDyadicGridLevel (times : Coordinates → DyadicTime) : ℕ :=
  prefixGridLevel (fun index => dyadicTimeLevel (dyadicEnumeration index)) (finiteDyadicEnumerationBound times)

def finiteDyadicGridIndex (times : Coordinates → DyadicTime) (coordinate : Coordinates) : ℕ :=
  prefixGridIndex (fun index => dyadicTimeLevel (dyadicEnumeration index))
    (fun index => dyadicTimeIndex (dyadicEnumeration index))
    (finiteDyadicEnumerationBound times) (finiteDyadicEnumerationIndex times coordinate)

def finiteDyadicGridBound (times : Coordinates → DyadicTime) : ℕ :=
  Finset.univ.sup (finiteDyadicGridIndex times)

def finiteDyadicPrefixProjection {X : Type*} (times : Coordinates → DyadicTime)
    (history : Finset.Iic (finiteDyadicGridBound times) → X) : Coordinates → X :=
  fun coordinate => history ⟨finiteDyadicGridIndex times coordinate,
    Finset.mem_Iic.mpr (Finset.le_sup (f := finiteDyadicGridIndex times) (Finset.mem_univ coordinate))⟩

theorem finiteDyadicPrefixProjection_measurable {X : Type*} [MeasurableSpace X]
    (times : Coordinates → DyadicTime) : Measurable (finiteDyadicPrefixProjection (X := X) times) := by
  apply measurable_pi_lambda
  intro coordinate
  exact measurable_pi_apply _

theorem finiteDyadicPrefixProjection_continuous {X : Type*} [TopologicalSpace X]
    (times : Coordinates → DyadicTime) : Continuous (finiteDyadicPrefixProjection (X := X) times) := by
  apply continuous_pi
  intro coordinate
  exact continuous_apply _

theorem finiteDyadicGridIndex_time (times : Coordinates → DyadicTime) (coordinate : Coordinates) :
    finiteDyadicGridIndex times coordinate • dyadicStep (finiteDyadicGridLevel times) = (times coordinate).val := by
  rw [finiteDyadicGridIndex, finiteDyadicGridLevel, prefixGridIndex_time, ← dyadicTime_representation]
  change (dyadicEnumeration (dyadicEnumeration.symm (times coordinate))).val = (times coordinate).val
  rw [Equiv.apply_symm_apply]

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]

def dyadicFiniteProbability (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (initial : ProbabilityMeasure X)
    (times : Coordinates → DyadicTime) : ProbabilityMeasure (Coordinates → X) := by
  let law : ProbabilityMeasure (DyadicTime → X) :=
    ⟨dyadicPathLaw family markov (initial : Measure X), inferInstance⟩
  exact ProbabilityMeasure.map law
    (show Measurable (fun path : DyadicTime → X => fun coordinate => path (times coordinate)) from
      measurable_pi_lambda _ (fun coordinate => measurable_pi_apply (times coordinate))).aemeasurable

def fineGridPrefixProbability (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (initial : ProbabilityMeasure X)
    (times : Coordinates → DyadicTime) : ProbabilityMeasure (Finset.Iic (finiteDyadicGridBound times) → X) := by
  letI : IsMarkovKernel (family (dyadicStep (finiteDyadicGridLevel times))) := markov _
  exact finitePrefixProbability (family (dyadicStep (finiteDyadicGridLevel times))) initial (finiteDyadicGridBound times)

/-- These are finite marginals of the actual constructed dyadic path law.
The common grid is obtained from its proved complete enumerated prefixes. -/
theorem dyadicFiniteProbability_eq_gridProjection (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (initial : ProbabilityMeasure X)
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime, family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (times : Coordinates → DyadicTime) :
    dyadicFiniteProbability family markov initial times =
      (fineGridPrefixProbability family markov initial times).map
        (finiteDyadicPrefixProjection_measurable times).aemeasurable := by
  letI : IsMarkovKernel (family (dyadicStep (finiteDyadicGridLevel times))) := markov _
  let count := finiteDyadicEnumerationBound times
  let selectEnumeration : (Finset.Iic count → X) → Coordinates → X :=
    fun history coordinate => history (finiteDyadicEnumerationIndex times coordinate)
  have selectMeasurable : Measurable selectEnumeration := by
    apply measurable_pi_lambda
    intro coordinate
    exact measurable_pi_apply _
  have enumeratedMeasurable : Measurable
      (fun path : DyadicTime → X => fun index : Finset.Iic count => path (dyadicEnumeration index.val)) := by
    apply measurable_pi_lambda
    intro index
    exact measurable_pi_apply _
  have factor : (fun path : DyadicTime → X => fun coordinate => path (times coordinate)) =
      selectEnumeration ∘ (fun path : DyadicTime → X => fun index : Finset.Iic count =>
        path (dyadicEnumeration index.val)) := by
    funext path coordinate
    simp only [Function.comp_apply, selectEnumeration, finiteDyadicEnumerationIndex, Equiv.apply_symm_apply]
  apply Subtype.ext
  change (dyadicPathLaw family markov (initial : Measure X)).map
    (fun path : DyadicTime → X => fun coordinate => path (times coordinate)) =
    ((pathLaw (family (dyadicStep (finiteDyadicGridLevel times))) (initial : Measure X)).map
      (frestrictLe (finiteDyadicGridBound times))).map (finiteDyadicPrefixProjection times)
  rw [factor, ← Measure.map_map selectMeasurable enumeratedMeasurable,
    dyadicPathLaw_enumerated_prefix family markov (initial : Measure X) zeroLaw addLaw count]
  unfold dyadicPrefixLaws
  rw [Measure.map_map selectMeasurable (dyadicPrefix_measurable _ _ _),
    Measure.map_map (finiteDyadicPrefixProjection_measurable times)
      (measurable_frestrictLe (finiteDyadicGridBound times))]
  rfl

def mappedDyadicFiniteProbability (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (initial : ProbabilityMeasure X)
    (embedding : X → Space) (measurable : Measurable embedding)
    (times : Coordinates → DyadicTime) : ProbabilityMeasure (Coordinates → Space) :=
  (dyadicFiniteProbability family markov initial times).map
    (show Measurable (fun points : Coordinates → X => fun coordinate => embedding (points coordinate)) from
      measurable_pi_lambda _ (fun coordinate => measurable.comp (measurable_pi_apply coordinate))).aemeasurable

def fineGridMappedPrefixProbability (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (initial : ProbabilityMeasure X)
    (embedding : X → Space) (measurable : Measurable embedding)
    (times : Coordinates → DyadicTime) : ProbabilityMeasure (Finset.Iic (finiteDyadicGridBound times) → Space) := by
  letI : IsMarkovKernel (family (dyadicStep (finiteDyadicGridLevel times))) := markov _
  exact FixedStepPrefixWeak.mappedProbability (family (dyadicStep (finiteDyadicGridLevel times)))
    initial embedding measurable (finiteDyadicGridBound times)

omit [MetricSpace Space] [CompactSpace Space] [BorelSpace Space] in
theorem mappedDyadicFiniteProbability_eq_gridProjection (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (initial : ProbabilityMeasure X)
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime, family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (embedding : X → Space) (measurable : Measurable embedding)
    (times : Coordinates → DyadicTime) :
    mappedDyadicFiniteProbability family markov initial embedding measurable times =
      (fineGridMappedPrefixProbability family markov initial embedding measurable times).map
        (finiteDyadicPrefixProjection_measurable times).aemeasurable := by
  letI : IsMarkovKernel (family (dyadicStep (finiteDyadicGridLevel times))) := markov _
  apply Subtype.ext
  change (dyadicFiniteProbability family markov initial times : Measure (Coordinates → X)).map
      (fun points : Coordinates → X => fun coordinate => embedding (points coordinate)) =
    (fineGridMappedPrefixProbability family markov initial embedding measurable times :
      Measure (Finset.Iic (finiteDyadicGridBound times) → Space)).map (finiteDyadicPrefixProjection times)
  have gridMeasureIdentity :
      (dyadicFiniteProbability family markov initial times : Measure (Coordinates → X)) =
      (fineGridPrefixProbability family markov initial times :
        Measure (Finset.Iic (finiteDyadicGridBound times) → X)).map (finiteDyadicPrefixProjection times) :=
    congrArg (fun probability : ProbabilityMeasure (Coordinates → X) =>
      (probability : Measure (Coordinates → X)))
      (dyadicFiniteProbability_eq_gridProjection family markov initial zeroLaw addLaw times)
  rw [gridMeasureIdentity]
  change (((pathLaw (family (dyadicStep (finiteDyadicGridLevel times))) (initial : Measure X)).map
    (frestrictLe (finiteDyadicGridBound times))).map (finiteDyadicPrefixProjection times)).map
      (fun points : Coordinates → X => fun coordinate => embedding (points coordinate)) =
    (((pathLaw (family (dyadicStep (finiteDyadicGridLevel times))) (initial : Measure X)).map
      (frestrictLe (finiteDyadicGridBound times))).map
        (fun history : Finset.Iic (finiteDyadicGridBound times) → X =>
          fun index => embedding (history index))).map (finiteDyadicPrefixProjection times)
  rw [Measure.map_map
    (show Measurable (fun points : Coordinates → X => fun coordinate => embedding (points coordinate)) from
      measurable_pi_lambda _ (fun coordinate => measurable.comp (measurable_pi_apply coordinate)))
    (finiteDyadicPrefixProjection_measurable times),
    Measure.map_map (finiteDyadicPrefixProjection_measurable times)
      (show Measurable (fun history : Finset.Iic (finiteDyadicGridBound times) → X =>
        fun index => embedding (history index)) from
          measurable_pi_lambda _ (fun index => measurable.comp (measurable_pi_apply index)))]
  rfl

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31 Filter Topology
open scoped BigOperators NNReal NNRat ProbabilityTheory BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) (resistanceRate normalization : ℝ)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)

def xiNativeRationalFiniteKernel (time : ℚ≥0) : Kernel (XiVtx system level) (XiVtx system level) :=
  xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization rulesLoopless rulesUnique
    plantingNonadjacent rateNonnegative normalizationNonnegative (time : ℝ≥0)

instance xiNativeRationalFiniteKernel_isMarkov (time : ℚ≥0) :
    IsMarkovKernel (xiNativeRationalFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time) := by
  unfold xiNativeRationalFiniteKernel
  infer_instance

theorem xiNativeRationalFiniteKernel_zero :
    xiNativeRationalFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative 0 = Kernel.id := by
  simpa only [xiNativeRationalFiniteKernel, NNRat.cast_zero] using
    xiNativeFiniteKernel_zero system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative

theorem xiNativeRationalFiniteKernel_add (firstTime secondTime : ℚ≥0) :
    xiNativeRationalFiniteKernel system rulesConnected mass level resistanceRate normalization
        rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative secondTime ∘ₖ
      xiNativeRationalFiniteKernel system rulesConnected mass level resistanceRate normalization
        rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative firstTime =
    xiNativeRationalFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative (firstTime + secondTime) := by
  simpa only [xiNativeRationalFiniteKernel, NNRat.cast_add] using
    (xiNativeFiniteKernel_add system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative
      (firstTime : ℝ≥0) (secondTime : ℝ≥0)).symm

variable {Coordinates : Type*} [Fintype Coordinates]

def xiNativeDyadicStationaryFiniteProbability
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (times : Coordinates → DiscreteMarkov.DyadicTime) :
    ProbabilityMeasure (Coordinates → XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) := by
  letI : Nonempty (XiVtx system level) := nonempty_of_isProbabilityMeasure (xiVertexSpeedMeasure system mass level)
  exact DiscreteMarkov.mappedDyadicFiniteProbability
    (xiNativeRationalFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative)
    (fun time => xiNativeRationalFiniteKernel_isMarkov system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time)
    (xiNativeSpeedProbabilityMeasure system mass level)
    (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level)
    (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair level) times

theorem xiNativeDyadicStationaryFiniteProbability_eq_gridPrefix
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (times : Coordinates → DiscreteMarkov.DyadicTime) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    xiNativeDyadicStationaryFiniteProbability system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair times =
      (xiNativeStationaryPrefixProbability system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate normalization
        rateNonnegative normalizationNonnegative level
        (DiscreteMarkov.dyadicStep (DiscreteMarkov.finiteDyadicGridLevel times) : ℝ≥0)
        (DiscreteMarkov.finiteDyadicGridBound times)).map
          (DiscreteMarkov.finiteDyadicPrefixProjection_continuous times).measurable.aemeasurable := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  letI : Nonempty (XiVtx system level) := nonempty_of_isProbabilityMeasure (xiVertexSpeedMeasure system mass level)
  exact DiscreteMarkov.mappedDyadicFiniteProbability_eq_gridProjection
    (xiNativeRationalFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative)
    (fun time => xiNativeRationalFiniteKernel_isMarkov system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time)
    (xiNativeSpeedProbabilityMeasure system mass level)
    (xiNativeRationalFiniteKernel_zero system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative)
    (xiNativeRationalFiniteKernel_add system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative)
    (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level)
    (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair level) times


def XiNativeDyadicFiniteLawWeakProperties (system : EIGSData K)
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
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
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
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ defaultPoint : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair,
      letI : Nonempty (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) := ⟨defaultPoint⟩
      ∃ transition : ℚ≥0 → Kernel
          (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
          (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair),
      ∃ markov : ∀ time, IsMarkovKernel (transition time),
        (∀ (time : ℚ≥0) (values : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
          ∀ᵐ point ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass,
            (∫ location, values location ∂transition time point) =
              QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense (time : ℝ≥0)
                (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
                  distanceRateGreaterThanOne metricEigenpair mass values) point) ∧
        (∀ time, (transition time).Invariant
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass)) ∧
        transition 0 = Kernel.id ∧
        (∀ firstTime secondTime : ℚ≥0,
          transition secondTime ∘ₖ transition firstTime = transition (firstTime + secondTime)) ∧
        DiscreteMarkov.DyadicProcessProperties transition markov ∧
        ∀ (dimension : ℕ) (times : Fin dimension → DiscreteMarkov.DyadicTime),
        Tendsto (fun level => xiNativeDyadicStationaryFiniteProbability system rulesConnected mass level
          resistanceRate normalization rulesLoopless rulesUnique plantingNonadjacent ratePositive.le normalizationPositive.le
          lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair times) atTop
          (nhds (DiscreteMarkov.dyadicFiniteProbability transition markov
            (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass) times))

theorem xiNativeDyadicFiniteLaw_weak_limit (system : EIGSData K)
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
    XiNativeDyadicFiniteLawWeakProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair normalization normalizationPositive := by
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
  have previous := xiNativeStationaryFixedStepPrefix_weak_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive normalizedConvergence
  dsimp only [XiNativeStationaryFixedStepPrefixWeakProperties] at previous
  dsimp only [XiNativeDyadicFiniteLawWeakProperties]
  intro originalDense defaultPoint
  letI : Nonempty (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) := ⟨defaultPoint⟩
  obtain ⟨comparison, comparisonMarkov, comparisonRepresentation, comparisonInvariant, prefixConvergence⟩ :=
    previous originalDense defaultPoint
  have processProperties := xiDyadicMarkovProcessProperties_of_dense_core system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair originalDense
  dsimp only [XiDyadicMarkovProcessProperties] at processProperties
  obtain ⟨processDensity, processForDefault⟩ := processProperties
  obtain ⟨transition, markov, representation, invariant, zeroLaw, addLaw, skeleton, dyadic⟩ :=
    processForDefault defaultPoint
  refine ⟨transition, markov, representation, invariant, zeroLaw, addLaw, dyadic, ?_⟩
  intro dimension times
  let rationalStep := DiscreteMarkov.dyadicStep (DiscreteMarkov.finiteDyadicGridLevel times)
  let step : ℝ≥0 := rationalStep
  let count := DiscreteMarkov.finiteDyadicGridBound times
  letI : IsMarkovKernel (comparison step) := comparisonMarkov step
  letI : IsMarkovKernel (transition rationalStep) := markov rationalStep
  have prefixSame :
      DiscreteMarkov.finitePrefixProbability (comparison step)
        (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass) count =
      DiscreteMarkov.fineGridPrefixProbability transition markov
        (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass) times := by
    change DiscreteMarkov.finitePrefixProbability (comparison step)
        (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass) count =
      DiscreteMarkov.finitePrefixProbability (transition rationalStep)
        (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass) count
    apply DiscreteMarkov.finitePrefixProbability_eq_of_same_operator
      (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)
      (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense step)
      (comparison step) (transition rationalStep) (comparisonInvariant step) (invariant rationalStep) _ _ count
    · intro values
      simpa only [xiContinuousL2Map] using comparisonRepresentation step values
    · intro values
      simpa only [xiContinuousL2Map] using representation rationalStep values
  have gridConvergence := prefixConvergence step count
  rw [prefixSame] at gridConvergence
  have projectedConvergence := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    _ _ gridConvergence (DiscreteMarkov.finiteDyadicPrefixProjection_continuous times)
  have nativeIdentity (level : ℕ) := xiNativeDyadicStationaryFiniteProbability_eq_gridPrefix system rulesConnected
    mass level resistanceRate normalization rulesLoopless rulesUnique plantingNonadjacent ratePositive.le normalizationPositive.le
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair times
  have targetIdentity := DiscreteMarkov.dyadicFiniteProbability_eq_gridProjection transition markov
    (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass) zeroLaw addLaw times
  change Tendsto (fun level => (xiNativeStationaryPrefixProbability system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate normalization ratePositive.le normalizationPositive.le level
      (DiscreteMarkov.dyadicStep (DiscreteMarkov.finiteDyadicGridLevel times) : ℝ≥0)
      (DiscreteMarkov.finiteDyadicGridBound times)).map
        (DiscreteMarkov.finiteDyadicPrefixProjection_continuous times).measurable.aemeasurable) atTop
      (nhds ((DiscreteMarkov.fineGridPrefixProbability transition markov
        (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass) times).map
          (DiscreteMarkov.finiteDyadicPrefixProjection_continuous times).measurable.aemeasurable))
      at projectedConvergence
  simpa only [← nativeIdentity, ← targetIdentity] using projectedConvergence

theorem exists_xiNativeDyadicFiniteLawWeak_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      ∃ _originalDense : Dense ((xiContinuousEnergyLpDomain system rulesConnected
        parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        distanceRateGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive) :
        Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
      XiNativeDyadicFiniteLawWeakProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, originalDense, ?_⟩
  exact xiNativeDyadicFiniteLaw_weak_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence




end
end EIGS

#print axioms IGS.Sec31.DiscreteMarkov.finitePrefixProbability_eq_of_same_operator
#print axioms IGS.Sec31.DiscreteMarkov.finiteDyadicGridIndex_time
#print axioms IGS.Sec31.DiscreteMarkov.dyadicFiniteProbability_eq_gridProjection
#print axioms IGS.Sec31.DiscreteMarkov.mappedDyadicFiniteProbability_eq_gridProjection
#print axioms EIGS.xiNativeRationalFiniteKernel_zero
#print axioms EIGS.xiNativeRationalFiniteKernel_add
#print axioms EIGS.xiNativeDyadicStationaryFiniteProbability
#print axioms EIGS.xiNativeDyadicStationaryFiniteProbability_eq_gridPrefix
#print axioms EIGS.XiNativeDyadicFiniteLawWeakProperties
#print axioms EIGS.xiNativeDyadicFiniteLaw_weak_limit
#print axioms EIGS.exists_xiNativeDyadicFiniteLawWeak_of_rules
