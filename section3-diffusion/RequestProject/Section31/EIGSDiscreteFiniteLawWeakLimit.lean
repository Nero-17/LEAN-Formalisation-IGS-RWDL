import RequestProject.Section31.EIGSDiscreteFiniteObservations
import RequestProject.Section31.EIGSDyadicFiniteLawWeakLimit

/-! Weak finite-dimensional limits for the original integer-time graph walk.
Complete grids start at zero. Continuous coordinate projections cover any
finite list of dyadic observation times, including positive first times,
repetitions and arbitrary order. An unobserved zero coordinate has test one;
the literal prepend-one product identity is proved below. The limit is the actual constructed dyadic
path law. No weak convergence on a path space is asserted. -/

namespace IGS.Sec31.DiscreteObservationWeak

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ProbabilityTheory BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 4000000

variable {X Space : Type*} [MeasurableSpace X] [MetricSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]

def scheduledMappedProbability (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (embedding : X → Space) (measurable : Measurable embedding)
    (schedule : ℕ → ℕ) (count : ℕ) : ProbabilityMeasure (Finset.Iic count → Space) := by
  let observed : (ℕ → X) → Finset.Iic count → Space :=
    fun path index => embedding (path (schedule index.val))
  have observedMeasurable : Measurable observed :=
    measurable_pi_lambda _ (fun index => measurable.comp (measurable_pi_apply _))
  exact ⟨(DiscreteMarkov.pathLaw kernel (initial : Measure X)).map observed,
    Measure.isProbabilityMeasure_map observedMeasurable.aemeasurable⟩

theorem scheduledMappedProbability_integral_product
    (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (embedding : X → Space) (measurable : Measurable embedding)
    (schedule : ℕ → ℕ) (count : ℕ) (tests : Finset.Iic count → Space →ᵇ ℝ) :
    (∫ history : Finset.Iic count → Space, ∏ index, tests index (history index)
      ∂(scheduledMappedProbability kernel initial embedding measurable schedule count : Measure _)) =
      ∫ path, (∏ index : Fin count, FixedStepPrefixWeak.extendTests count tests index.val
        (embedding (path (schedule index.val)))) *
        tests ⟨count, Finset.mem_Iic.mpr le_rfl⟩ (embedding (path (schedule count)))
        ∂DiscreteMarkov.pathLaw kernel (initial : Measure X) := by
  have productMeasurable : Measurable (fun history : Finset.Iic count → Space =>
      ∏ index, tests index (history index)) := by
    apply Finset.measurable_prod
    intro index _
    exact (tests index).continuous.measurable.comp (measurable_pi_apply index)
  change (∫ history : Finset.Iic count → Space, ∏ index, tests index (history index)
    ∂(DiscreteMarkov.pathLaw kernel (initial : Measure X)).map
      (fun path index => embedding (path (schedule index.val)))) = _
  rw [integral_map (show Measurable (fun path : ℕ → X => fun index : Finset.Iic count =>
    embedding (path (schedule index.val))) from
      measurable_pi_lambda _ (fun index => measurable.comp (measurable_pi_apply _))).aemeasurable
    productMeasurable.aestronglyMeasurable]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro path
  exact FixedStepPrefixWeak.path_coordinateProduct_eq_prefix count embedding tests
    (fun index => path (schedule index))

/-- Deleting an auxiliary initial coordinate is continuous. -/
def dropInitialCoordinate (count : ℕ) (history : Fin (count + 1) → Space) : Fin count → Space :=
  fun index => history index.succ

theorem dropInitialCoordinate_continuous (count : ℕ) :
    Continuous (dropInitialCoordinate (Space := Space) count) := by
  apply continuous_pi
  intro index
  exact continuous_apply index.succ

/-- The auxiliary zero-time observation has the literal constant-one test. -/
theorem prepend_one_product (count : ℕ) (tests : Fin count → Space →ᵇ ℝ)
    (history : Fin (count + 1) → Space) :
    (∏ index : Fin (count + 1),
      (Fin.cases (motive := fun _ : Fin (count + 1) => Space →ᵇ ℝ)
        (1 : Space →ᵇ ℝ) tests index) (history index)) =
      ∏ index : Fin count, tests index (dropInitialCoordinate count history index) := by
  rw [Fin.prod_univ_succ]
  simp [dropInitialCoordinate]

theorem constant_backwardProduct_eq_prefix
    {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    (operator : Hilbert →L[ℝ] Hilbert) (multiplication : ℕ → Hilbert →L[ℝ] Hilbert)
    (count : ℕ) (terminal : Hilbert) :
    FiniteObservations.backwardProduct (fun _ : ℕ => operator) multiplication
      ((List.range count).map (fun index => (index, index))) terminal =
      DiscreteMarkov.operatorBackwardPrefix operator multiplication count terminal := by
  induction count generalizing terminal with
  | zero => rfl
  | succ count induction =>
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        DiscreteMarkov.backwardProduct_append, FiniteObservations.backwardProduct,
        DiscreteMarkov.operatorBackwardPrefix]
      exact induction _

end
end IGS.Sec31.DiscreteObservationWeak

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31 Filter Topology
open scoped BigOperators NNReal NNRat ENNReal Classical BoundedContinuousFunction ProbabilityTheory

noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

def xiNativeDiscreteStationaryPrefixProbability (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system) (resistanceRate normalization : ℝ)
    (_rateNonnegative : 0 ≤ resistanceRate) (_normalizationNonnegative : 0 ≤ normalization)
    (level : ℕ) (step : ℝ≥0) (count : ℕ) :
    ProbabilityMeasure (Finset.Iic count → XiMetricCompletion system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :=
  DiscreteObservationWeak.scheduledMappedProbability
    (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
    (xiNativeSpeedProbabilityMeasure system mass level)
    (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level)
    (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair level)
    (fun index => Nat.floor (((index : ℝ) * (step : ℝ)) *
      xiNativeFiniteJumpRate system level resistanceRate normalization)) count

def XiNativeDiscreteFixedStepPrefixWeakProperties (system : EIGSData K)
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
      ∀ _defaultPoint : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair,
      ∃ transition : ℝ≥0 → Kernel
          (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
          (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair),
      ∃ markov : ∀ time, IsMarkovKernel (transition time),
        (∀ (time : ℝ≥0) (values : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
          ∀ᵐ point ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass,
            (∫ location, values location ∂transition time point) =
              QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
                (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
                  distanceRateGreaterThanOne metricEigenpair mass values) point) ∧
        (∀ time, (transition time).Invariant
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass)) ∧
        ∀ (step : ℝ≥0) (count : ℕ),
        Tendsto (fun level => xiNativeDiscreteStationaryPrefixProbability system rulesConnected
          rulesLoopless rulesUnique plantingNonadjacent lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass resistanceRate normalization
          ratePositive.le normalizationPositive.le level step count) atTop
          (nhds (DiscreteMarkov.finitePrefixProbability (transition step)
            (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass) count))

theorem xiNativeDiscreteFixedStepPrefix_weak_limit (system : EIGSData K)
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
    XiNativeDiscreteFixedStepPrefixWeakProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair normalization normalizationPositive := by
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
  have previous := xiNativeStationaryFixedStepObservations_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive normalizedConvergence
  dsimp only [XiNativeStationaryFixedStepObservationProperties] at previous
  dsimp only [XiNativeDiscreteFixedStepPrefixWeakProperties]
  intro originalDense defaultPoint
  obtain ⟨transition, markov, representation, invariant, _poissonProductConvergence⟩ :=
    previous originalDense defaultPoint
  refine ⟨transition, markov, representation, invariant, ?_⟩
  intro step count
  letI : IsMarkovKernel (transition step) := markov step
  apply FiniteProductWeak.weak_tendsto_of_product_integrals
  intro tests
  let extended := FixedStepPrefixWeak.extendTests count tests
  let terminal := tests ⟨count, Finset.mem_Iic.mpr le_rfl⟩
  have convergence := xiNativeDiscreteFiniteObservations_expectation_limit system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive normalizedConvergence originalDense
    (fun index => (index : ℝ≥0) * step)
    (fun first second ordered => mul_le_mul_of_nonneg_right (by exact_mod_cast ordered) (zero_le step))
    (by simp) extended count terminal
  have gridGap (index : ℕ) : ((index + 1 : ℕ) : ℝ≥0) * step - (index : ℝ≥0) * step = step := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_tsub_cancel_left]
  simp only [gridGap, DiscreteObservationWeak.constant_backwardProduct_eq_prefix] at convergence
  have targetEquality :
      (∫ history : Finset.Iic count → XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair,
        ∏ index, tests index (history index)
          ∂(DiscreteMarkov.finitePrefixProbability (transition step)
            (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass) count : Measure _)) =
      inner ℝ (core.embed 1) (DiscreteMarkov.operatorBackwardPrefix
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense step)
        (fun index => boundedContinuousLimitMultiplication
          (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass) (extended index)) count (core.embed terminal)) := by
    rw [FixedStepPrefixWeak.finitePrefixProbability_integral_product]
    have continuousRepresentation : ∀ values : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
        ∀ᵐ point ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass,
        (∫ target, values target ∂transition step point) =
          QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense step
            (ContinuousMap.toLp 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass) ℝ values) point := by
      intro values
      simpa only [xiContinuousL2Map] using representation step values
    rw [DiscreteMarkov.continuous_pathLaw_prefix_integral_operator
      (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass) (transition step) (invariant step)
      (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense step)
      continuousRepresentation extended count terminal]
    change (∫ point, DiscreteMarkov.operatorBackwardPrefix
      (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense step)
      (fun index => boundedContinuousLimitMultiplication
        (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass) (extended index)) count (core.embed terminal) point
      ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass) = _
    apply DiscreteMarkov.integral_eq_inner_one
      (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)
    change (BoundedContinuousFunction.toLp 2
      (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass) ℝ (1 : _ →ᵇ ℝ) : _ → ℝ) =ᵐ[_] fun _ => 1
    simpa only [BoundedContinuousFunction.coe_one, Pi.one_apply] using
      BoundedContinuousFunction.coeFn_toLp (𝕜 := ℝ) 2
        (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass) (1 : _ →ᵇ ℝ)
  rw [targetEquality]
  simpa only [xiNativeDiscreteStationaryPrefixProbability,
    DiscreteObservationWeak.scheduledMappedProbability_integral_product,
    xiNativeSpeedProbabilityMeasure, xiLimitProbabilityMeasure, NNReal.coe_mul, NNReal.coe_natCast,
    extended, terminal] using convergence

variable {Coordinates : Type*} [Fintype Coordinates]

def xiNativeDiscreteDyadicFiniteProbability (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) (resistanceRate normalization : ℝ)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (_rateNonnegative : 0 ≤ resistanceRate) (_normalizationNonnegative : 0 ≤ normalization)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (times : Coordinates → DiscreteMarkov.DyadicTime) :
    ProbabilityMeasure (Coordinates → XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) := by
  let law : ProbabilityMeasure (ℕ → XiVtx system level) :=
    ⟨DiscreteMarkov.pathLaw
      (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
      (xiVertexSpeedMeasure system mass level), inferInstance⟩
  exact ProbabilityMeasure.map law
    (show Measurable (fun path : ℕ → XiVtx system level => fun coordinate =>
      xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level
        (path (Nat.floor (((times coordinate).val : ℝ) *
          xiNativeFiniteJumpRate system level resistanceRate normalization)))) from
      measurable_pi_lambda _ (fun coordinate =>
        (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair level).comp (measurable_pi_apply _))).aemeasurable

theorem xiNativeDiscreteDyadicFiniteProbability_eq_gridPrefix (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) (resistanceRate normalization : ℝ)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (times : Coordinates → DiscreteMarkov.DyadicTime) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    xiNativeDiscreteDyadicFiniteProbability system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair times =
      (xiNativeDiscreteStationaryPrefixProbability system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate normalization
        rateNonnegative normalizationNonnegative level
        (DiscreteMarkov.dyadicStep (DiscreteMarkov.finiteDyadicGridLevel times) : ℝ≥0)
        (DiscreteMarkov.finiteDyadicGridBound times)).map
          (DiscreteMarkov.finiteDyadicPrefixProjection_continuous times).measurable.aemeasurable := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  apply Subtype.ext
  change (DiscreteMarkov.pathLaw
      (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
      (xiVertexSpeedMeasure system mass level)).map
      (fun path : ℕ → XiVtx system level => fun coordinate =>
        xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level
          (path (Nat.floor (((times coordinate).val : ℝ) *
            xiNativeFiniteJumpRate system level resistanceRate normalization)))) =
    ((DiscreteMarkov.pathLaw
      (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
      (xiVertexSpeedMeasure system mass level)).map
      (fun path : ℕ → XiVtx system level => fun index : Finset.Iic (DiscreteMarkov.finiteDyadicGridBound times) =>
        xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level
          (path (Nat.floor (((index.val : ℝ) *
            (DiscreteMarkov.dyadicStep (DiscreteMarkov.finiteDyadicGridLevel times) : ℝ)) *
            xiNativeFiniteJumpRate system level resistanceRate normalization))))).map
      (DiscreteMarkov.finiteDyadicPrefixProjection times)
  rw [Measure.map_map (DiscreteMarkov.finiteDyadicPrefixProjection_measurable times)
    (show Measurable (fun path : ℕ → XiVtx system level =>
      fun index : Finset.Iic (DiscreteMarkov.finiteDyadicGridBound times) =>
        xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level
          (path (Nat.floor (((index.val : ℝ) *
            (DiscreteMarkov.dyadicStep (DiscreteMarkov.finiteDyadicGridLevel times) : ℝ)) *
            xiNativeFiniteJumpRate system level resistanceRate normalization)))) from
      measurable_pi_lambda _ (fun index =>
        (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair level).comp (measurable_pi_apply _)))]
  congr 1
  funext path coordinate
  have gridTime : (DiscreteMarkov.finiteDyadicGridIndex times coordinate : ℝ) *
      (DiscreteMarkov.dyadicStep (DiscreteMarkov.finiteDyadicGridLevel times) : ℝ) =
      ((times coordinate).val : ℝ) := by
    have identity := DiscreteMarkov.finiteDyadicGridIndex_time times coordinate
    rw [nsmul_eq_mul] at identity
    exact_mod_cast identity
  change _ = xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level
    (path (Nat.floor (((DiscreteMarkov.finiteDyadicGridIndex times coordinate : ℝ) *
      (DiscreteMarkov.dyadicStep (DiscreteMarkov.finiteDyadicGridLevel times) : ℝ)) *
      xiNativeFiniteJumpRate system level resistanceRate normalization)))
  rw [gridTime]

def XiNativeDiscreteDyadicFiniteLawWeakProperties (system : EIGSData K)
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
        Tendsto (fun level => xiNativeDiscreteDyadicFiniteProbability system rulesConnected mass level
          resistanceRate normalization rulesLoopless rulesUnique plantingNonadjacent ratePositive.le normalizationPositive.le
          lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair times) atTop
          (nhds (DiscreteMarkov.dyadicFiniteProbability transition markov
            (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass) times))

theorem xiNativeDiscreteDyadicFiniteLaw_weak_limit (system : EIGSData K)
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
    XiNativeDiscreteDyadicFiniteLawWeakProperties system rulesConnected rulesLoopless rulesUnique
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
  have previous := xiNativeDiscreteFixedStepPrefix_weak_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive normalizedConvergence
  dsimp only [XiNativeDiscreteFixedStepPrefixWeakProperties] at previous
  dsimp only [XiNativeDiscreteDyadicFiniteLawWeakProperties]
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
  have nativeIdentity (level : ℕ) := xiNativeDiscreteDyadicFiniteProbability_eq_gridPrefix system rulesConnected
    mass level resistanceRate normalization rulesLoopless rulesUnique plantingNonadjacent ratePositive.le normalizationPositive.le
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair times
  have targetIdentity := DiscreteMarkov.dyadicFiniteProbability_eq_gridProjection transition markov
    (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass) zeroLaw addLaw times
  change Tendsto (fun level => (xiNativeDiscreteStationaryPrefixProbability system rulesConnected rulesLoopless rulesUnique
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

theorem exists_xiNativeDiscreteDyadicFiniteLawWeak_of_rules (system : EIGSData K)
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
      XiNativeDiscreteDyadicFiniteLawWeakProperties system rulesConnected rulesLoopless rulesUnique
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
  exact xiNativeDiscreteDyadicFiniteLaw_weak_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence




end
end EIGS

#print axioms IGS.Sec31.DiscreteObservationWeak.scheduledMappedProbability_integral_product
#print axioms IGS.Sec31.DiscreteObservationWeak.prepend_one_product

#print axioms EIGS.xiNativeDiscreteFixedStepPrefix_weak_limit
#print axioms EIGS.xiNativeDiscreteDyadicFiniteProbability_eq_gridPrefix

#print axioms EIGS.xiNativeDiscreteDyadicFiniteLaw_weak_limit
#print axioms EIGS.exists_xiNativeDiscreteDyadicFiniteLawWeak_of_rules
#print axioms IGS.Sec31.DiscreteObservationWeak.constant_backwardProduct_eq_prefix
#print axioms EIGS.xiNativeDiscreteDyadicFiniteProbability
