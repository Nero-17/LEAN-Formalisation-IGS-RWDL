import RequestProject.Section31.EIGSNativeSupFiniteObservations
import RequestProject.Section31.EIGSNativeSupDiscreteConvergence
import RequestProject.Section31.AffineContractionTruncation

/-! Moving-start convergence for finite products of continuous observations.
The true Dirac path-law integral is identified with its Banach backward
recursion, whose supremum convergence follows from the same actual absolute
floor-clock operators. The final rule consumer supplies that convergence.
Repeated times are allowed. This file does not yet assert convergence of
arbitrary continuous finite-dimensional tests or probability laws. -/

namespace EIGS

open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiNativeSup_moving_start_product_limit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (parameters : XiPathMetricData system rulesConnected) [CompactSpace parameters.LimitSpace]
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
    (times : ℕ → ℝ≥0) (timesMonotone : Monotone times) (startsAtZero : times 0 = 0)
    (tests : ℕ → C(parameters.LimitSpace, ℝ)) (count : ℕ)
    (terminal : C(parameters.LimitSpace, ℝ)) (starts : ∀ level, XiVtx system level)
    (start : parameters.LimitSpace)
    (startsConverge : Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start)) :
    Tendsto (fun level => ∫ path,
      (∏ index : Fin count, tests index.val (parameters.vertexEmbedding level
        (path (Nat.floor ((times index.val : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))))) *
      terminal (parameters.vertexEmbedding level (path (Nat.floor ((times count : ℝ) *
        xiNativeFiniteJumpRate system level resistanceRate normalization)))) ∂pathLaw
          (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
          (Measure.dirac (starts level))) atTop
      (𝓝 (BanachBackwardObservations.backwardProduct
        (fun index : ℕ => semigroup (times (index + 1) - times index))
        (fun index : ℕ => ContinuousLinearMap.mul ℝ C(parameters.LimitSpace, ℝ) (tests index))
        ((List.range count).map (fun index => (index, index))) terminal start)) := by
  let restriction := xiContinuousVertexRestriction system rulesConnected parameters
  let levelEvolution (level index : ℕ) := xiNativeSupTransition system rulesConnected level ^
    (Nat.floor ((times (index + 1) : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization) -
      Nat.floor ((times index : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))
  let evolution (index : ℕ) := semigroup (times (index + 1) - times index)
  let levelMultiplication (level index : ℕ) :=
    ContinuousLinearMap.mul ℝ (XiVtx system level → ℝ) (restriction level (tests index))
  let multiplication (index : ℕ) :=
    ContinuousLinearMap.mul ℝ C(parameters.LimitSpace, ℝ) (tests index)
  let observations := (List.range count).map (fun index => (index, index))
  have evolutionBound (level index : ℕ) : ‖levelEvolution level index‖ ≤ (1 : ℝ) := by
    apply (continuousLinearMap_norm_pow_le _ _).trans
    simpa only [one_pow] using pow_le_pow_left₀
      (norm_nonneg (xiNativeSupTransition system rulesConnected level))
      (xiNativeSupTransition_norm_le_one system rulesConnected level) _
  have multiplicationBound (level index : ℕ) : ‖levelMultiplication level index‖ ≤ ‖tests index‖ := by
    apply (ContinuousLinearMap.opNorm_mul_apply_le ℝ _ _).trans
    simpa only [one_mul] using
      (restriction level).le_of_opNorm_le
        (xiContinuousVertexRestriction_norm_le_one system rulesConnected parameters level) (tests index)
  have evolutionConverges (index : ℕ) (function : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun level => ‖levelEvolution level index (restriction level function) -
        restriction level (evolution index function)‖) atTop (𝓝 0) := by
    have ordered : times index ≤ times (index + 1) := timesMonotone (Nat.le_succ index)
    have realOrdered : (times index : ℝ) ≤ (times (index + 1) : ℝ) := by exact_mod_cast ordered
    have gapIdentity : (⟨(times (index + 1) : ℝ) - times index,
        sub_nonneg.mpr realOrdered⟩ : ℝ≥0) = times (index + 1) - times index := by
      apply Subtype.ext
      exact (NNReal.coe_sub ordered).symm
    change Tendsto (fun level => ‖(xiNativeSupTransition system rulesConnected level ^
      (Nat.floor ((times (index + 1) : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization) -
        Nat.floor ((times index : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization)))
      (fun vertex => function (parameters.vertexEmbedding level vertex)) -
      (fun vertex => semigroup (times (index + 1) - times index) function
        (parameters.vertexEmbedding level vertex))‖) atTop (𝓝 0)
    simpa only [gapIdentity] using absoluteUniform (times index) (times (index + 1))
      (times index).property realOrdered function
  have multiplicationIdentity (level index : ℕ) (function : C(parameters.LimitSpace, ℝ)) :
      levelMultiplication level index (restriction level function) =
        restriction level (multiplication index function) := by
    ext vertex
    rfl
  have multiplicationConverges (index : ℕ) (function : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun level => ‖levelMultiplication level index (restriction level function) -
        restriction level (multiplication index function)‖) atTop (𝓝 0) := by
    simp_rw [multiplicationIdentity, sub_self, norm_zero]
    exact tendsto_const_nhds
  have terminalConverges : Tendsto (fun level => ‖restriction level terminal - restriction level terminal‖)
      atTop (𝓝 (0 : ℝ)) := by simp only [sub_self, norm_zero]; exact tendsto_const_nhds
  have uniform := BanachBackwardObservations.backwardProduct_uniform_limit restriction levelEvolution evolution
    levelMultiplication multiplication (fun _ => (1 : ℝ)) (fun index => ‖tests index‖)
    evolutionBound multiplicationBound evolutionConverges multiplicationConverges observations
    (fun level => restriction level terminal) terminal terminalConverges
  have movingLimit := BanachBackwardObservations.moving_start_evaluation_limit parameters.vertexEmbedding
    (fun level => BanachBackwardObservations.backwardProduct (levelEvolution level)
      (levelMultiplication level) observations (restriction level terminal))
    (BanachBackwardObservations.backwardProduct evolution multiplication observations terminal)
    uniform starts start startsConverge
  convert movingLimit using 1
  funext level
  exact xiNativeSup_absolute_floor_pathLaw_integral_backwardProduct system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent level resistanceRate normalization rateNonnegative normalizationNonnegative
    times timesMonotone startsAtZero (fun index vertex => tests index (parameters.vertexEmbedding level vertex))
    count (fun vertex => terminal (parameters.vertexEmbedding level vertex)) (starts level)

def XiNativeSupMovingStartProductProperties (system : EIGSData K)
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
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∃ resolvers : (step : ℝ) → 0 < step → step ≤ 1 →
      C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
    (∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1),
      let closedOperator := QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
        originalDense step stepPositive stepAtMostOne
      ‖resolvers step stepPositive stepAtMostOne‖ ≤ 1 ∧
        ∀ function : C(parameters.LimitSpace, ℝ),
          core.embed (BoundedContinuousFunction.mkOfCompact (resolvers step stepPositive stepAtMostOne function)) =
            closedOperator (core.embed (BoundedContinuousFunction.mkOfCompact function)) ∧
          Tendsto (fun level => ‖fun vertex : XiVtx system level =>
            xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
              mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive
              (core.restrict level (BoundedContinuousFunction.mkOfCompact function)) vertex -
            resolvers step stepPositive stepAtMostOne function (parameters.vertexEmbedding level vertex)‖)
            atTop (nhds 0)) ∧
    (∀ (function : C(parameters.LimitSpace, ℝ)) (error : ℝ), 0 < error →
      ∃ thresholdStep : ℝ, 0 < thresholdStep ∧
        ∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1),
          step < thresholdStep → ‖resolvers step stepPositive stepAtMostOne function - function‖ < error) ∧
    (∀ function : C(parameters.LimitSpace, ℝ),
      Tendsto (fun step : {step : ℝ // 0 < step ∧ step ≤ 1} =>
        resolvers step.1 step.2.1 step.2.2 function)
        (comap (fun step : {step : ℝ // 0 < step ∧ step ≤ 1} => step.1) (nhds (0 : ℝ)))
        (nhds function)) ∧
    ∃ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
      (∀ time, ‖semigroup time‖ ≤ 1) ∧
      semigroup 0 = ContinuousLinearMap.id ℝ C(parameters.LimitSpace, ℝ) ∧
      (∀ firstTime secondTime, semigroup (firstTime + secondTime) =
        (semigroup firstTime).comp (semigroup secondTime)) ∧
      Continuous (fun point : C(parameters.LimitSpace, ℝ) × ℝ≥0 => semigroup point.2 point.1) ∧
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
          (semigroup time function) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
          (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function)) ∧
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        Tendsto (fun index => BanachResolventYosidaGeneration.operators
          (fun index => resolvers (QuadraticEnergySpace.canonicalYosidaStep index)
            (QuadraticEnergySpace.canonicalYosidaStep_positive index)
            (QuadraticEnergySpace.canonicalYosidaStep_le_one index))
          QuadraticEnergySpace.canonicalYosidaStep index time function)
          atTop (𝓝 (semigroup time function))) ∧
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        Tendsto (fun level => ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
          (fun vertex => function (parameters.vertexEmbedding level vertex)) -
          (fun vertex => semigroup time function (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0)) ∧
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        Tendsto (fun level => ‖(xiNativeSupTransition system rulesConnected level ^
          Nat.floor ((time : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))
          (fun vertex => function (parameters.vertexEmbedding level vertex)) -
          (fun vertex => semigroup time function (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0)) ∧
      (∀ (first second : ℝ) (firstNonnegative : 0 ≤ first) (ordered : first ≤ second)
        (function : C(parameters.LimitSpace, ℝ)),
        Tendsto (fun level => ‖(xiNativeSupTransition system rulesConnected level ^
          (Nat.floor (second * xiNativeFiniteJumpRate system level resistanceRate normalization) -
            Nat.floor (first * xiNativeFiniteJumpRate system level resistanceRate normalization)))
          (fun vertex => function (parameters.vertexEmbedding level vertex)) -
          (fun vertex => semigroup ⟨second - first, sub_nonneg.mpr ordered⟩ function
            (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0)) ∧
      ∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times) (startsAtZero : times 0 = 0)
        (tests : ℕ → C(parameters.LimitSpace, ℝ)) (count : ℕ)
        (terminal : C(parameters.LimitSpace, ℝ)) (starts : ∀ level, XiVtx system level)
        (start : parameters.LimitSpace)
        (startsConverge : Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start)),
        Tendsto (fun level => ∫ path,
          (∏ index : Fin count, tests index.val (parameters.vertexEmbedding level
            (path (Nat.floor ((times index.val : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))))) *
          terminal (parameters.vertexEmbedding level (path (Nat.floor ((times count : ℝ) *
            xiNativeFiniteJumpRate system level resistanceRate normalization)))) ∂pathLaw
              (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
              (Measure.dirac (starts level))) atTop
          (𝓝 (BanachBackwardObservations.backwardProduct
            (fun index : ℕ => semigroup (times (index + 1) - times index))
            (fun index : ℕ => ContinuousLinearMap.mul ℝ C(parameters.LimitSpace, ℝ) (tests index))
            ((List.range count).map (fun index => (index, index))) terminal start))

theorem xiNativeSupMovingStartProductProperties_of_discreteConvergence (system : EIGSData K)
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
    (discreteProperties : XiNativeSupDiscreteConvergenceProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive) :
    XiNativeSupMovingStartProductProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only [XiNativeSupDiscreteConvergenceProperties, XiNativeSupMovingStartProductProperties]
    at discreteProperties ⊢
  obtain ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit,
    semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, semigroupIntertwining,
    canonicalLimit, supLimit, floorLimit, absoluteUniform⟩ := discreteProperties
  refine ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit,
    semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, semigroupIntertwining,
    canonicalLimit, supLimit, floorLimit, absoluteUniform, ?_⟩
  intro times timesMonotone startsAtZero tests count terminal starts start startsConverge
  exact xiNativeSup_moving_start_product_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent parameters resistanceRate normalization ratePositive.le normalizationPositive.le
    semigroup absoluteUniform times timesMonotone startsAtZero tests count terminal starts start startsConverge

theorem exists_xiNativeSupMovingStartProducts_of_rules (system : EIGSData K)
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
      XiNativeSupMovingStartProductProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, discreteProperties⟩ :=
    exists_xiNativeSupDiscreteConvergence_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiNativeSupMovingStartProductProperties_of_discreteConvergence system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive discreteProperties


end
end EIGS

#print axioms EIGS.xiNativeSup_moving_start_product_limit
#print axioms EIGS.xiNativeSupMovingStartProductProperties_of_discreteConvergence
#print axioms EIGS.exists_xiNativeSupMovingStartProducts_of_rules
