import RequestProject.Section31.EIGSFiniteHorizonMovingStartFullConvergenceOfRules
import RequestProject.Section31.ContinuousKernelBackwardObservations
import RequestProject.Section31.EIGSContinuousSemigroupMarkovOfRules

/-! A weak limit of the actual moving-start floor-clock paths has the
specified finite observation integrals of the same continuous semigroup.
For its Riesz kernels these are genuine nested kernel integrals. -/

namespace EIGS

open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal UniformConvergence BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiFiniteHorizonMovingStartLimit_ordered_product_integrals (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (parameters : XiPathMetricData system rulesConnected) [CompactSpace parameters.LimitSpace]
    [MeasurableSpace parameters.LimitSpace] [BorelSpace parameters.LimitSpace]
    (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ))
    (absoluteUniform : ∀ (first second : ℝ) (firstNonnegative : 0 ≤ first) (ordered : first ≤ second)
      (function : C(parameters.LimitSpace, ℝ)),
      Tendsto (fun level => ‖(xiNativeSupTransition system rulesConnected level ^
        (Nat.floor (second * xiNativeFiniteJumpRate system level resistanceRate normalization) -
          Nat.floor (first * xiNativeFiniteJumpRate system level resistanceRate normalization)))
        (fun vertex => function (parameters.vertexEmbedding level vertex)) -
        (fun vertex => semigroup ⟨second - first, sub_nonneg.mpr ordered⟩ function
          (parameters.vertexEmbedding level vertex))‖) atTop (𝓝 0))
    (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (rateIdentity : ∀ level, (rates level : ℝ) =
      xiNativeFiniteJumpRate system level resistanceRate normalization)
    (starts : ∀ level, XiVtx system level) (start : parameters.LimitSpace)
    (startsConverge : Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start))
    (limit : ProbabilityMeasure (FiniteSupportPathSpace
      (finiteHorizonStepPaths horizon rates parameters.vertexEmbedding)))
    (weakConvergence : Tendsto (fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding
      (fun level => xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
      (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))) level)
        atTop (𝓝 limit))
    (times : ℕ → ℝ≥0) (timesMonotone : Monotone times) (startsAtZero : times 0 = 0)
    (tests : ℕ → C(parameters.LimitSpace, ℝ)) (count : ℕ)
    (terminal : C(parameters.LimitSpace, ℝ)) (timesInHorizon : times count ≤ horizon) :
    (∫ path,
      (∏ index : Fin count, tests index.val (UniformFun.toFun path.val
        ⟨(times index.val : ℝ), (times index.val).property,
          by exact_mod_cast (timesMonotone (Nat.le_of_lt index.isLt)).trans timesInHorizon⟩)) *
      terminal (UniformFun.toFun path.val
        ⟨(times count : ℝ), (times count).property, by exact_mod_cast timesInHorizon⟩)
        ∂(limit : Measure _)) =
      BanachBackwardObservations.backwardProduct
        (fun index : ℕ => semigroup (times (index + 1) - times index))
        (fun index : ℕ => ContinuousLinearMap.mul ℝ C(parameters.LimitSpace, ℝ) (tests index))
        ((List.range count).map (fun index => (index, index))) terminal start := by
  let paths := finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
  let observedTimes (index : Fin count) : Set.Icc (0 : ℝ) (horizon : ℝ) :=
    ⟨(times index.val : ℝ), (times index.val).property,
      by exact_mod_cast (timesMonotone (Nat.le_of_lt index.isLt)).trans timesInHorizon⟩
  let terminalTime : Set.Icc (0 : ℝ) (horizon : ℝ) :=
    ⟨(times count : ℝ), (times count).property, by exact_mod_cast timesInHorizon⟩
  let observedTests (index : Fin count) : FiniteSupportPathSpace paths →ᵇ ℝ :=
    (BoundedContinuousFunction.mkOfCompact (tests index.val)).compContinuous
      ⟨fun path => UniformFun.toFun path.val (observedTimes index),
        finiteSupportPathSpace_continuous_eval paths (observedTimes index)⟩
  let terminalTest : FiniteSupportPathSpace paths →ᵇ ℝ :=
    (BoundedContinuousFunction.mkOfCompact terminal).compContinuous
      ⟨fun path => UniformFun.toFun path.val terminalTime,
        finiteSupportPathSpace_continuous_eval paths terminalTime⟩
  let productFunction : FiniteSupportPathSpace paths →ᵇ ℝ :=
    (∏ index : Fin count, observedTests index) * terminalTest
  have productValue (path : FiniteSupportPathSpace paths) :
      productFunction path =
        (∏ index : Fin count, tests index.val (UniformFun.toFun path.val (observedTimes index))) *
          terminal (UniformFun.toFun path.val terminalTime) := by
    simp only [productFunction, BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.prod_apply,
      observedTests, terminalTest, BoundedContinuousFunction.compContinuous_apply,
      BoundedContinuousFunction.mkOfCompact_apply]
  have weakProducts := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp weakConvergence productFunction
  have nativeProducts := xiNativeSup_moving_start_product_limit system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent parameters resistanceRate normalization rateNonnegative normalizationNonnegative
    semigroup absoluteUniform times timesMonotone startsAtZero tests count terminal starts start startsConverge
  have integralIdentity (level : ℕ) :
      (∫ path, productFunction path ∂(finiteHorizonStepLaw horizon rates parameters.vertexEmbedding
        (fun level => xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))) level :
          Measure (FiniteSupportPathSpace paths))) =
      ∫ path,
        (∏ index : Fin count, tests index.val (parameters.vertexEmbedding level
          (path (Nat.floor ((times index.val : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))))) *
        terminal (parameters.vertexEmbedding level (path (Nat.floor ((times count : ℝ) *
          xiNativeFiniteJumpRate system level resistanceRate normalization)))) ∂pathLaw
          (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
          (Measure.dirac (starts level)) := by
    rw [finiteHorizonStepLaw_eq_map]
    rw [integral_map (finiteHorizonStepMap_measurable horizon rates parameters.vertexEmbedding level).aemeasurable
      productFunction.continuous.measurable.aestronglyMeasurable]
    apply integral_congr_ae
    refine Eventually.of_forall fun path => ?_
    rw [productValue]
    simp only [finiteHorizonStepMap_apply, observedTimes, terminalTime, rateIdentity]
  simp_rw [integralIdentity] at weakProducts
  have identification := tendsto_nhds_unique weakProducts nativeProducts
  simpa only [productValue, observedTimes, terminalTime] using identification

def XiFiniteHorizonMovingStartKernelIdentificationProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  ∃ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
    (∀ time, ‖semigroup time‖ ≤ 1) ∧
    semigroup 0 = ContinuousLinearMap.id ℝ C(parameters.LimitSpace, ℝ) ∧
    (∀ firstTime secondTime, semigroup (firstTime + secondTime) =
      (semigroup firstTime).comp (semigroup secondTime)) ∧
    Continuous (fun point : C(parameters.LimitSpace, ℝ) × ℝ≥0 => semigroup point.2 point.1) ∧
    (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
      Tendsto (fun level => ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
        (fun vertex => function (parameters.vertexEmbedding level vertex)) -
        (fun vertex => semigroup time function (parameters.vertexEmbedding level vertex))‖) atTop (𝓝 0)) ∧
    ∃ positive : ∀ time (function : C(parameters.LimitSpace, ℝ)),
      (∀ point, 0 ≤ function point) → ∀ point, 0 ≤ semigroup time function point,
    ∃ preservesOne : ∀ time, semigroup time 1 = 1,
      ∀ (horizon : ℝ≥0) (starts : ∀ level, XiVtx system level) (start : parameters.LimitSpace),
        Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
        let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
          normalization normalizationPositive
        let paths := finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
        let laws := fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding
          (fun level => xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
          (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))) level
        ∃ limit : ProbabilityMeasure (FiniteSupportPathSpace paths),
          Tendsto laws atTop (𝓝 limit) ∧
          (∀ᵐ path ∂(limit : Measure (FiniteSupportPathSpace paths)), Continuous (UniformFun.toFun path.val)) ∧
          ∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times), times 0 = 0 →
            ∀ (tests : ℕ → C(parameters.LimitSpace, ℝ)) (count : ℕ) (terminal : C(parameters.LimitSpace, ℝ))
              (timesInHorizon : times count ≤ horizon),
              (∫ path,
                (∏ index : Fin count, tests index.val (UniformFun.toFun path.val
                  ⟨(times index.val : ℝ), (times index.val).property,
                    by exact_mod_cast (timesMonotone (Nat.le_of_lt index.isLt)).trans timesInHorizon⟩)) *
                terminal (UniformFun.toFun path.val
                  ⟨(times count : ℝ), (times count).property, by exact_mod_cast timesInHorizon⟩)
                    ∂(limit : Measure (FiniteSupportPathSpace paths))) =
                ContinuousMarkov.kernelBackwardProduct
                  (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
                  ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start

theorem xiFiniteHorizonMovingStartKernelIdentificationProperties_of_movingProducts (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (movingProperties : XiNativeSupMovingStartProductProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive) :
    XiFiniteHorizonMovingStartKernelIdentificationProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  have arbitraryProperties := xiNativeSupArbitraryProductProperties_of_movingStartProducts system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive movingProperties
  have fullProperties := xiFiniteHorizonMovingStartFullConvergenceProperties_of_arbitraryProducts system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive arbitraryProperties
  dsimp only [XiNativeSupMovingStartProductProperties] at movingProperties
  obtain ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit,
    semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, semigroupIntertwining,
    canonicalLimit, supLimit, floorLimit, absoluteUniform, orderedProducts⟩ := movingProperties
  have continuousProperties : XiContinuousSemigroupProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair := by
    dsimp only [XiContinuousSemigroupProperties]
    exact ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd,
      semigroupContinuous, semigroupIntertwining⟩
  have markovProperties := xiContinuousSemigroupMarkovProperties_of_continuousSemigroup system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair continuousProperties
  dsimp only [XiContinuousSemigroupMarkovProperties] at markovProperties
  obtain ⟨markovDense, markovSemigroup, _, _, _, _, markovIntertwining,
    positive, preservesConstants, _, _, _⟩ := markovProperties
  have semigroupEquality : markovSemigroup = semigroup := by
    funext time
    apply ContinuousLinearMap.ext
    intro function
    apply xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    exact (markovIntertwining time function).trans (semigroupIntertwining time function).symm
  subst markovSemigroup
  have preservesOne (time : ℝ≥0) : semigroup time 1 = 1 := by
    simpa using preservesConstants time 1
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext renormalizationEigenpair)
  dsimp only [XiFiniteHorizonMovingStartKernelIdentificationProperties]
  refine ⟨semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, ?_⟩
  intro horizon starts start startsConverge
  dsimp only [XiFiniteHorizonMovingStartFullConvergenceProperties] at fullProperties
  obtain ⟨limit, weakConvergence, continuousLimit⟩ := fullProperties horizon starts start startsConverge
  refine ⟨limit, weakConvergence, continuousLimit, ?_⟩
  intro times timesMonotone startsAtZero tests count terminal timesInHorizon
  have orderedIdentification := xiFiniteHorizonMovingStartLimit_ordered_product_integrals system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent parameters resistanceRate normalization ratePositive.le
    normalizationPositive.le semigroup absoluteUniform horizon
    (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive)
    (by intro level; change xiNativeFiniteJumpRate system level _ normalization = _; rw [rateEquality])
    starts start startsConverge limit weakConvergence times timesMonotone startsAtZero tests count terminal timesInHorizon
  exact orderedIdentification.trans
    (congrFun (ContinuousMarkov.kernelBackwardProduct_indexed_eq_semigroupBackwardProduct semigroup positive
      preservesOne (fun index => times (index + 1) - times index) tests count terminal) start).symm

theorem exists_xiFiniteHorizonMovingStartKernelIdentification_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      XiFiniteHorizonMovingStartKernelIdentificationProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, movingProperties⟩ :=
    exists_xiNativeSupMovingStartProducts_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence,
    xiFiniteHorizonMovingStartKernelIdentificationProperties_of_movingProducts system rulesConnected
      rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair normalization normalizationPositive movingProperties⟩

end
end EIGS

#print axioms EIGS.xiFiniteHorizonMovingStartLimit_ordered_product_integrals
#print axioms EIGS.xiFiniteHorizonMovingStartKernelIdentificationProperties_of_movingProducts
#print axioms EIGS.exists_xiFiniteHorizonMovingStartKernelIdentification_of_rules
