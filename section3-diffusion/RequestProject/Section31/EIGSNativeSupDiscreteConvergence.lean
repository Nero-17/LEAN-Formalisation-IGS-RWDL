import RequestProject.Section31.EIGSNativeSupSemigroupConvergence
import RequestProject.Section31.EIGSNativeSupDePoissonization
import RequestProject.Section31.PoissonizedAbsoluteClockLimit

/-! All-starting-vertex supremum convergence for the actual discrete walk.
Both a single floor clock and differences of absolute floor clocks converge
to the same continuous semigroup. The original-rule consumer retains the
coherent native resolvents and the actual closed L² identification. -/

namespace IGS.Sec31

open Filter Topology

 theorem restriction_limit_of_resolvent_smoothing
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    {LevelSpace : ℕ → Type*} [∀ level, NormedAddCommGroup (LevelSpace level)]
    [∀ level, NormedSpace ℝ (LevelSpace level)]
    (restriction : ∀ level, Space →L[ℝ] LevelSpace level)
    (restrictionBound : ∀ level, ‖restriction level‖ ≤ 1)
    (resolvers : ℕ → Space →L[ℝ] Space)
    (finiteResolvers : ∀ index level, LevelSpace level →L[ℝ] LevelSpace level)
    (resolverConvergence : ∀ index values,
      Tendsto (fun level => ‖finiteResolvers index level (restriction level values) -
        restriction level (resolvers index values)‖) atTop (nhds 0))
    (nearIdentity : ∀ values, Tendsto (fun index => resolvers index values) atTop (nhds values))
    (steps : ℕ → ℝ) (coefficient : ℕ → ℝ)
    (coefficientLimit : Tendsto coefficient atTop (nhds 0))
    (discrete continuous : ∀ level, LevelSpace level →L[ℝ] LevelSpace level)
    (values target : Space)
    (comparison : ∀ index level,
      ‖discrete level (restriction level values) - continuous level (restriction level values)‖ ≤
        2 * ‖restriction level values - finiteResolvers index level (restriction level values)‖ +
          coefficient level * (2 * ‖values‖ / steps index))
    (continuousLimit : Tendsto (fun level => ‖continuous level (restriction level values) -
      restriction level target‖) atTop (nhds 0)) :
    Tendsto (fun level => ‖discrete level (restriction level values) - restriction level target‖)
      atTop (nhds 0) := by
  have initialLimit : Tendsto (fun index => 2 * ‖values - resolvers index values‖) atTop (nhds 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (((tendsto_const_nhds (x := values)).sub (nearIdentity values)).norm.const_mul 2)
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  obtain ⟨index, initialSmall⟩ := (initialLimit.eventually_lt_const (half_pos tolerancePositive)).exists
  have varyingLimit : Tendsto (fun level =>
      2 * ‖finiteResolvers index level (restriction level values) - restriction level (resolvers index values)‖ +
      coefficient level * (2 * ‖values‖ / steps index) +
      ‖continuous level (restriction level values) - restriction level target‖) atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul, zero_add, add_zero] using
      (((resolverConvergence index values).const_mul 2).add
        (coefficientLimit.mul_const (2 * ‖values‖ / steps index))).add continuousLimit
  filter_upwards [varyingLimit.eventually_lt_const (half_pos tolerancePositive)] with level varyingSmall
  have restrictionDistance : ‖restriction level values - restriction level (resolvers index values)‖ ≤
      ‖values - resolvers index values‖ := by
    rw [← map_sub]
    simpa only [one_mul] using
      (restriction level).le_of_opNorm_le (restrictionBound level) (values - resolvers index values)
  have smoothingTriangle := dist_triangle (restriction level values) (restriction level (resolvers index values))
    (finiteResolvers index level (restriction level values))
  have finalTriangle := dist_triangle (discrete level (restriction level values))
    (continuous level (restriction level values)) (restriction level target)
  simp only [dist_eq_norm] at smoothingTriangle finalTriangle
  rw [norm_sub_rev (restriction level (resolvers index values))
    (finiteResolvers index level (restriction level values))] at smoothingTriangle
  have finiteComparison := comparison index level
  have totalSmall : ‖discrete level (restriction level values) - restriction level target‖ < tolerance := by
    linarith
  simpa only [dist_zero_right, norm_norm] using totalSmall

end IGS.Sec31

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiNativeSupTransition_absolute_floor_uniform_limit
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (parameters : XiPathMetricData system rulesConnected) [CompactSpace parameters.LimitSpace]
    (mass : XiMassParameters system) (resistanceRate normalization : ℝ)
    (ratePositive : 0 < resistanceRate) (normalizationPositive : 0 < normalization)
    (resolvers : ℕ → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ))
    (uniformConvergence : ∀ index (function : C(parameters.LimitSpace, ℝ)),
      Tendsto (fun level => ‖fun vertex : XiVtx system level =>
        xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le
          (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
          (xiFiniteSpeedL2 system mass level (fun vertex => function (parameters.vertexEmbedding level vertex))) vertex -
        resolvers index function (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0))
    (nearIdentity : ∀ function, Tendsto (fun index => resolvers index function) atTop (nhds function))
    (semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ))
    (semigroupLimit : ∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
      Tendsto (fun level => ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
        (fun vertex => function (parameters.vertexEmbedding level vertex)) -
        (fun vertex => semigroup time function (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0))
    (jumpRateLimit : Tendsto (fun level => xiNativeFiniteJumpRate system level resistanceRate normalization) atTop atTop)
    (first second : ℝ) (firstNonnegative : 0 ≤ first) (ordered : first ≤ second)
    (function : C(parameters.LimitSpace, ℝ)) :
    Tendsto (fun level => ‖(xiNativeSupTransition system rulesConnected level ^
      (Nat.floor (second * xiNativeFiniteJumpRate system level resistanceRate normalization) -
        Nat.floor (first * xiNativeFiniteJumpRate system level resistanceRate normalization)))
      (fun vertex => function (parameters.vertexEmbedding level vertex)) -
      (fun vertex => semigroup ⟨second - first, sub_nonneg.mpr ordered⟩ function
        (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0) := by
  let restriction := xiContinuousVertexRestriction system rulesConnected parameters
  let finiteResolvers (index level : ℕ) :=
    xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le
      (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
  let coefficient (level : ℕ) :=
    (Real.sqrt (Nat.floor ((second - first) * xiNativeFiniteJumpRate system level resistanceRate normalization)) + 2) /
      xiNativeFiniteJumpRate system level resistanceRate normalization
  have restrictionBound (level : ℕ) : ‖restriction level‖ ≤ 1 :=
    xiContinuousVertexRestriction_norm_le_one system rulesConnected parameters level
  have finiteUniform (index : ℕ) (argument : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun level => ‖finiteResolvers index level (restriction level argument) -
        restriction level (resolvers index argument)‖) atTop (nhds 0) := by
    change Tendsto (fun level => ‖fun vertex : XiVtx system level =>
      xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le
        (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
        (xiFiniteSpeedL2 system mass level (fun vertex => argument (parameters.vertexEmbedding level vertex))) vertex -
      resolvers index argument (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0)
    exact uniformConvergence index argument
  have coefficientLimit : Tendsto coefficient atTop (nhds 0) :=
    PoissonizedWalk.absolute_clock_coefficient_tendsto_zero
      (fun level => xiNativeFiniteJumpRate system level resistanceRate normalization)
      jumpRateLimit first second ordered
  apply restriction_limit_of_resolvent_smoothing restriction restrictionBound resolvers finiteResolvers
    finiteUniform nearIdentity QuadraticEnergySpace.canonicalYosidaStep coefficient coefficientLimit
    (fun level => xiNativeSupTransition system rulesConnected level ^
      (Nat.floor (second * xiNativeFiniteJumpRate system level resistanceRate normalization) -
        Nat.floor (first * xiNativeFiniteJumpRate system level resistanceRate normalization)))
    (fun level => xiNativeSupSemigroup system rulesConnected level resistanceRate normalization (second - first))
    function (semigroup ⟨second - first, sub_nonneg.mpr ordered⟩ function) ?_
    (semigroupLimit ⟨second - first, sub_nonneg.mpr ordered⟩ function)
  intro index level
  have nativeComparison := xiNativeSupTransition_absolute_floor_error_after_smoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent mass level resistanceRate normalization ratePositive normalizationPositive
    (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
    first second firstNonnegative ordered (restriction level function)
  have inputBound : ‖restriction level function‖ ≤ ‖function‖ := by
    simpa only [one_mul] using (restriction level).le_of_opNorm_le (restrictionBound level) function
  have coefficientNonnegative : 0 ≤ coefficient level := by
    have jumpPositive := xiNativeFiniteJumpRate_positive system mass level resistanceRate normalization
      ratePositive normalizationPositive
    dsimp only [coefficient]
    positivity
  have scaledInput : coefficient level *
      (2 * ‖restriction level function‖ / QuadraticEnergySpace.canonicalYosidaStep index) ≤
      coefficient level * (2 * ‖function‖ / QuadraticEnergySpace.canonicalYosidaStep index) := by
    apply mul_le_mul_of_nonneg_left _ coefficientNonnegative
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left inputBound (by norm_num))
      (QuadraticEnergySpace.canonicalYosidaStep_positive index).le
  exact nativeComparison.trans (add_le_add le_rfl scaledInput)

def XiNativeSupDiscreteConvergenceProperties (system : EIGSData K)
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
            (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0))

theorem xiNativeSupDiscreteConvergenceProperties_of_supSemigroup (system : EIGSData K)
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
    (supProperties : XiNativeSupSemigroupConvergenceProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive) :
    XiNativeSupDiscreteConvergenceProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
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
  dsimp only [XiNativeSupSemigroupConvergenceProperties, XiNativeSupDiscreteConvergenceProperties]
    at supProperties ⊢
  obtain ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit,
    semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, semigroupIntertwining,
    canonicalLimit, supLimit⟩ := supProperties
  let canonicalResolvers : ℕ → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ) := fun index =>
    resolvers (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index) (QuadraticEnergySpace.canonicalYosidaStep_le_one index)
  have uniformConvergence (index : ℕ) (function : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun level => ‖fun vertex : XiVtx system level =>
        xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le
          (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
          (xiFiniteSpeedL2 system mass level (fun vertex => function (parameters.vertexEmbedding level vertex))) vertex -
        canonicalResolvers index function (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0) := by
    have uniform := ((resolverProperties (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index) (QuadraticEnergySpace.canonicalYosidaStep_le_one index)).2 function).2
    simpa only [core, xiSpeedL2Core_restrict_eq_finiteSpeedL2] using uniform
  have nearIdentity (function : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun index => canonicalResolvers index function) atTop (nhds function) := by
    apply Metric.tendsto_nhds.mpr
    intro error errorPositive
    obtain ⟨threshold, thresholdPositive, afterThreshold⟩ := approximateIdentity function error errorPositive
    filter_upwards [QuadraticEnergySpace.canonicalYosidaStep_tendsto.eventually_lt_const thresholdPositive]
      with index smallStep
    simpa only [dist_eq_norm] using afterThreshold _ _ _ smallStep
  have jumpRateLimit := xiNativeFiniteJumpRate_tendsto_atTop system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass distancePositive resistanceRate normalization ratePositive normalizationPositive
    resistanceVector vectorPositive (funext renormalizationEigenpair)
  have absoluteUniform (first second : ℝ) (firstNonnegative : 0 ≤ first) (ordered : first ≤ second)
      (function : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun level => ‖(xiNativeSupTransition system rulesConnected level ^
        (Nat.floor (second * xiNativeFiniteJumpRate system level resistanceRate normalization) -
          Nat.floor (first * xiNativeFiniteJumpRate system level resistanceRate normalization)))
        (fun vertex => function (parameters.vertexEmbedding level vertex)) -
        (fun vertex => semigroup ⟨second - first, sub_nonneg.mpr ordered⟩ function
          (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0) :=
    xiNativeSupTransition_absolute_floor_uniform_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      parameters mass resistanceRate normalization ratePositive normalizationPositive canonicalResolvers uniformConvergence
      nearIdentity semigroup supLimit jumpRateLimit first second firstNonnegative ordered function
  refine ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit,
    semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, semigroupIntertwining,
    canonicalLimit, supLimit, ?_, absoluteUniform⟩
  intro time function
  simpa only [zero_mul, Nat.floor_zero, Nat.sub_zero, sub_zero] using
    absoluteUniform 0 time (by norm_num) time.coe_nonneg function

theorem exists_xiNativeSupDiscreteConvergence_of_rules (system : EIGSData K)
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
      XiNativeSupDiscreteConvergenceProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, supProperties⟩ :=
    exists_xiNativeSupSemigroupConvergence_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiNativeSupDiscreteConvergenceProperties_of_supSemigroup system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive supProperties



end
end EIGS

#print axioms IGS.Sec31.restriction_limit_of_resolvent_smoothing
#print axioms EIGS.xiNativeSupTransition_absolute_floor_uniform_limit
#print axioms EIGS.xiNativeSupDiscreteConvergenceProperties_of_supSemigroup
#print axioms EIGS.exists_xiNativeSupDiscreteConvergence_of_rules
