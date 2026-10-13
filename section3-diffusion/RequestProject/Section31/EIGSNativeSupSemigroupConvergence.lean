import RequestProject.Section31.EIGSNativeSupYosidaConvergence
import RequestProject.Section31.EIGSNativeSupSemigroupComparison
import RequestProject.Section31.EIGSContinuousSemigroupYosidaOfRules

/-! Supremum-norm convergence of the actual native finite exponentials.
First choose a fixed resolvent smoothing, then a fixed canonical Yosida
approximation, and finally let the finite level tend to infinity. The
original-rule consumer supplies the coherent resolvent family and its
proved canonical Yosida limit, including the actual closed L² identification. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiNativeSupSemigroup_uniform_limit
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (parameters : XiPathMetricData system rulesConnected) [CompactSpace parameters.LimitSpace]
    (mass : XiMassParameters system) (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (resolvers : ℕ → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ))
    (resolverNorm : ∀ index, ‖resolvers index‖ ≤ 1)
    (uniformConvergence : ∀ index (function : C(parameters.LimitSpace, ℝ)),
      Tendsto (fun level => ‖fun vertex : XiVtx system level =>
        xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative
          (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
          (xiFiniteSpeedL2 system mass level (fun vertex => function (parameters.vertexEmbedding level vertex))) vertex -
        resolvers index function (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0))
    (nearIdentity : ∀ function, Tendsto (fun index => resolvers index function) atTop (nhds function))
    (semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ))
    (canonicalLimit : ∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
      Tendsto (fun index => BoundedYosida.semigroup (resolvers index)
        (QuadraticEnergySpace.canonicalYosidaStep index) time function) atTop (nhds (semigroup time function)))
    (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)) :
    Tendsto (fun level => ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
      (fun vertex => function (parameters.vertexEmbedding level vertex)) -
      (fun vertex => semigroup time function (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0) := by
  let restriction := xiContinuousVertexRestriction system rulesConnected parameters
  let finiteResolvents (index level : ℕ) :=
    xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative
      (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
  have restrictionBound (level : ℕ) : ‖restriction level‖ ≤ 1 :=
    xiContinuousVertexRestriction_norm_le_one system rulesConnected parameters level
  have finiteNorm (index level : ℕ) : ‖finiteResolvents index level‖ ≤ 1 :=
    xiNativeSupResolvent_norm_le_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative
      (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
  have finiteUniform (index : ℕ) (argument : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun level => ‖finiteResolvents index level (restriction level argument) -
        restriction level (resolvers index argument)‖) atTop (nhds 0) := by
    change Tendsto (fun level => ‖fun vertex : XiVtx system level =>
      xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative
        (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
        (xiFiniteSpeedL2 system mass level (fun vertex => argument (parameters.vertexEmbedding level vertex))) vertex -
      resolvers index argument (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0)
    exact uniformConvergence index argument
  have smoothingLimit (argument : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun index => ‖argument - resolvers index argument‖) atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds (x := argument)).sub (nearIdentity argument)).norm
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  have initialErrorLimit : Tendsto (fun index => 2 * ‖function - resolvers index function‖)
      atTop (nhds 0) := by
    simpa only [mul_zero] using (smoothingLimit function).const_mul 2
  obtain ⟨smoothingIndex, smoothingSmall⟩ :=
    (initialErrorLimit.eventually_lt_const (by positivity : 0 < tolerance / 8)).exists
  let smoothed (level : ℕ) := finiteResolvents smoothingIndex level (restriction level function)
  let smoothedTarget := resolvers smoothingIndex function
  let generatorValues (level : ℕ) :=
    (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)⁻¹ • (restriction level function - smoothed level)
  let generatorTarget := (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)⁻¹ • (function - smoothedTarget)
  have generatorUniform : Tendsto (fun level => ‖generatorValues level - restriction level generatorTarget‖)
      atTop (nhds 0) := by
    have identity (level : ℕ) : generatorValues level - restriction level generatorTarget =
        (-(QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)⁻¹) •
          (smoothed level - restriction level smoothedTarget) := by
      simp only [generatorValues, generatorTarget, map_smul, map_sub, smul_sub, neg_smul]
      module
    simp_rw [identity, norm_smul, Real.norm_eq_abs]
    simpa only [mul_zero] using (finiteUniform smoothingIndex function).const_mul
      |-(QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)⁻¹|
  have generatorErrorLimit : Tendsto (fun index => (time : ℝ) *
      ‖generatorTarget - resolvers index generatorTarget‖) atTop (nhds 0) := by
    simpa only [mul_zero] using (smoothingLimit generatorTarget).const_mul (time : ℝ)
  have targetErrorLimit : Tendsto (fun index => ‖BoundedYosida.semigroup (resolvers index)
      (QuadraticEnergySpace.canonicalYosidaStep index) time function - semigroup time function‖)
      atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using ((canonicalLimit time function).sub_const (semigroup time function)).norm
  obtain ⟨yosidaIndex, generatorSmall, targetSmall⟩ :=
    ((generatorErrorLimit.eventually_lt_const (by positivity : 0 < tolerance / 8)).and
      (targetErrorLimit.eventually_lt_const (by positivity : 0 < tolerance / 8))).exists
  have generatorResolverUniform :
      Tendsto (fun level => ‖finiteResolvents yosidaIndex level (generatorValues level) -
        restriction level (resolvers yosidaIndex generatorTarget)‖) atTop (nhds 0) :=
    VaryingBanachOperatorApproximation.varying_apply restriction (finiteResolvents yosidaIndex)
      (resolvers yosidaIndex) 1 (finiteNorm yosidaIndex) (finiteUniform yosidaIndex)
      generatorValues generatorTarget generatorUniform
  have yosidaUniform := VaryingBanachOperatorApproximation.yosida_exponential_apply restriction restrictionBound
    (finiteResolvents yosidaIndex) (resolvers yosidaIndex) (finiteNorm yosidaIndex) (resolverNorm yosidaIndex)
    (finiteUniform yosidaIndex) (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex)
    (QuadraticEnergySpace.canonicalYosidaStep_positive yosidaIndex) time function
  have varyingErrorLimit : Tendsto (fun level =>
      2 * ‖smoothed level - restriction level smoothedTarget‖ +
      (time : ℝ) * (‖generatorValues level - restriction level generatorTarget‖ +
        ‖finiteResolvents yosidaIndex level (generatorValues level) -
          restriction level (resolvers yosidaIndex generatorTarget)‖) +
      ‖BoundedYosida.semigroup (finiteResolvents yosidaIndex level)
        (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex) time (restriction level function) -
        restriction level (BoundedYosida.semigroup (resolvers yosidaIndex)
          (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex) time function)‖)
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_add, add_zero] using
      (((finiteUniform smoothingIndex function).const_mul 2).add
        ((generatorUniform.add generatorResolverUniform).const_mul (time : ℝ))).add yosidaUniform
  filter_upwards [varyingErrorLimit.eventually_lt_const (half_pos tolerancePositive)] with level varyingSmall
  have restrictionDistance (first second : C(parameters.LimitSpace, ℝ)) :
      ‖restriction level first - restriction level second‖ ≤ ‖first - second‖ := by
    rw [← map_sub]
    simpa only [one_mul] using (restriction level).le_of_opNorm_le (restrictionBound level) (first - second)
  have inputBound : ‖restriction level function - smoothed level‖ ≤
      ‖function - smoothedTarget‖ + ‖smoothed level - restriction level smoothedTarget‖ := by
    have triangle := dist_triangle (restriction level function) (restriction level smoothedTarget) (smoothed level)
    simp only [dist_eq_norm, norm_sub_rev (restriction level smoothedTarget) (smoothed level)] at triangle
    exact triangle.trans (add_le_add (restrictionDistance function smoothedTarget) le_rfl)
  have generatorBound : ‖generatorValues level - finiteResolvents yosidaIndex level (generatorValues level)‖ ≤
      ‖generatorValues level - restriction level generatorTarget‖ +
      ‖generatorTarget - resolvers yosidaIndex generatorTarget‖ +
      ‖finiteResolvents yosidaIndex level (generatorValues level) -
        restriction level (resolvers yosidaIndex generatorTarget)‖ := by
    have firstTriangle := dist_triangle (generatorValues level) (restriction level generatorTarget)
      (finiteResolvents yosidaIndex level (generatorValues level))
    have secondTriangle := dist_triangle (restriction level generatorTarget)
      (restriction level (resolvers yosidaIndex generatorTarget))
      (finiteResolvents yosidaIndex level (generatorValues level))
    simp only [dist_eq_norm] at firstTriangle secondTriangle
    have middleBound := restrictionDistance generatorTarget (resolvers yosidaIndex generatorTarget)
    rw [norm_sub_rev (restriction level (resolvers yosidaIndex generatorTarget))
      (finiteResolvents yosidaIndex level (generatorValues level))] at secondTriangle
    linarith
  have finiteComparison := xiNativeSupSemigroup_yosida_error_after_smoothing system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent mass level resistanceRate normalization rateNonnegative normalizationNonnegative
    (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex) (QuadraticEnergySpace.canonicalYosidaStep_positive yosidaIndex)
    (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex) (QuadraticEnergySpace.canonicalYosidaStep_positive smoothingIndex)
    time time.coe_nonneg (restriction level function)
  change ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time (restriction level function) -
      BoundedYosida.semigroup (finiteResolvents yosidaIndex level)
        (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex) time (restriction level function)‖ ≤
      2 * ‖restriction level function - smoothed level‖ +
        (time : ℝ) * ‖generatorValues level - finiteResolvents yosidaIndex level (generatorValues level)‖ at finiteComparison
  have firstTriangle := dist_triangle
    (xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time (restriction level function))
    (BoundedYosida.semigroup (finiteResolvents yosidaIndex level)
      (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex) time (restriction level function))
    (restriction level (semigroup time function))
  have secondTriangle := dist_triangle
    (BoundedYosida.semigroup (finiteResolvents yosidaIndex level)
      (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex) time (restriction level function))
    (restriction level (BoundedYosida.semigroup (resolvers yosidaIndex)
      (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex) time function))
    (restriction level (semigroup time function))
  simp only [dist_eq_norm] at firstTriangle secondTriangle
  have targetBound := restrictionDistance
    (BoundedYosida.semigroup (resolvers yosidaIndex) (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex) time function)
    (semigroup time function)
  have scaledGenerator := mul_le_mul_of_nonneg_left generatorBound time.coe_nonneg
  have totalSmall : ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
      (restriction level function) - restriction level (semigroup time function)‖ < tolerance := by
    change 2 * ‖function - smoothedTarget‖ < tolerance / 8 at smoothingSmall
    linarith
  simpa only [dist_zero_right, norm_norm] using totalSmall

def XiNativeSupSemigroupConvergenceProperties (system : EIGSData K)
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
      ∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        Tendsto (fun level => ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
          (fun vertex => function (parameters.vertexEmbedding level vertex)) -
          (fun vertex => semigroup time function (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0)

theorem xiNativeSupSemigroupConvergenceProperties_of_yosida (system : EIGSData K)
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
    (yosidaProperties : XiContinuousSemigroupYosidaProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive) :
    XiNativeSupSemigroupConvergenceProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
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
  dsimp only [XiContinuousSemigroupYosidaProperties, XiNativeSupSemigroupConvergenceProperties]
    at yosidaProperties ⊢
  obtain ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit,
    semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, semigroupIntertwining,
    canonicalLimit⟩ := yosidaProperties
  refine ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit,
    semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, semigroupIntertwining,
    canonicalLimit, ?_⟩
  let canonicalResolvers : ℕ → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ) := fun index =>
    resolvers (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index) (QuadraticEnergySpace.canonicalYosidaStep_le_one index)
  have resolverNorm (index : ℕ) : ‖canonicalResolvers index‖ ≤ 1 := (resolverProperties _ _ _).1
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
  have canonicalLimit' (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun index => BoundedYosida.semigroup (canonicalResolvers index)
        (QuadraticEnergySpace.canonicalYosidaStep index) time function) atTop (nhds (semigroup time function)) := by
    exact canonicalLimit time function
  intro time function
  exact xiNativeSupSemigroup_uniform_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    parameters mass resistanceRate normalization ratePositive.le normalizationPositive.le canonicalResolvers
    resolverNorm uniformConvergence nearIdentity semigroup canonicalLimit' time function

theorem exists_xiNativeSupSemigroupConvergence_of_rules (system : EIGSData K)
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
      XiNativeSupSemigroupConvergenceProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, yosidaProperties⟩ :=
    exists_xiContinuousSemigroupYosida_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiNativeSupSemigroupConvergenceProperties_of_yosida system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive yosidaProperties


end
end EIGS

#print axioms EIGS.xiNativeSupSemigroup_uniform_limit
#print axioms EIGS.xiNativeSupSemigroupConvergenceProperties_of_yosida
#print axioms EIGS.exists_xiNativeSupSemigroupConvergence_of_rules
