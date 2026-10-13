import RequestProject.Section31.EIGSNativeSemigroupComparison
import RequestProject.Section31.QuadraticEnergySemigroup

/-! Genuine varying-Hilbert Strong convergence of the actual finite
random-walk exponentials to the actual closed-form semigroup. Resolvent
smoothing and the proved vectorwise exponential comparison discharge the
finite-process approximation; no Trotter theorem is assumed. -/

namespace IGS.Sec31

/-- Contractive operators preserve a vectorwise comparison after replacing
the input by a nearby smoothed vector. -/
theorem contraction_comparison_after_smoothing
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (first second : Space →L[ℝ] Space)
    (firstContraction : ‖first‖ ≤ 1) (secondContraction : ‖second‖ ≤ 1)
    (values smoothed : Space) (error : ℝ)
    (smoothedComparison : ‖first smoothed - second smoothed‖ ≤ error) :
    ‖first values - second values‖ ≤ 2 * ‖values - smoothed‖ + error := by
  have firstDifference : ‖first values - first smoothed‖ ≤ ‖values - smoothed‖ := by
    rw [← map_sub]
    exact (first.le_opNorm _).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right firstContraction (norm_nonneg (values - smoothed)))
  have secondDifference : ‖second smoothed - second values‖ ≤ ‖values - smoothed‖ := by
    rw [norm_sub_rev, ← map_sub]
    exact (second.le_opNorm _).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right secondContraction (norm_nonneg (values - smoothed)))
  have firstTriangle := dist_triangle (first values) (first smoothed) (second values)
  have secondTriangle := dist_triangle (first smoothed) (second smoothed) (second values)
  simp only [dist_eq_norm] at firstTriangle secondTriangle
  linarith

end IGS.Sec31

namespace EIGS

open MeasureTheory IGS.Sec31 Filter Topology
open scoped NNReal

noncomputable section

set_option maxHeartbeats 4000000

variable {K : ℕ}

theorem xiNativeFiniteSemigroup_strong_limit (system : EIGSData K)
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
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ (time : ℝ≥0)
        (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong forcing target →
      core.Strong (fun level => xiNativeFiniteSemigroup system rulesConnected mass level
        resistanceRate normalization time (forcing level))
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
          originalDense time target) := by
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
  dsimp only
  intro originalDense time forcing target forcingStrong
  by_cases timeZero : time = 0
  · simpa only [timeZero, NNReal.coe_zero, xiNativeFiniteSemigroup_zero,
      QuadraticEnergySpace.closedSemigroup_zero, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.id_apply] using forcingStrong
  let finiteResolvent (index level : ℕ) :=
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level
      resistanceRate normalization ratePositive.le normalizationPositive.le
      (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index)
  let limitResolvent (index : ℕ) :=
    QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable originalDense
      (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index)
      (QuadraticEnergySpace.canonicalYosidaStep_le_one index)
  let finiteYosida (index level : ℕ) :=
    xiNativeYosidaSemigroup system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level
      resistanceRate normalization ratePositive.le normalizationPositive.le
      (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index) time
  let limitYosida (index : ℕ) :=
    QuadraticEnergySpace.closedSemigroupApproximation originalDomain originalForm nonnegative closable
      originalDense index time
  let finiteSemigroup (level : ℕ) :=
    xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time
  let limitSemigroup :=
    QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time target
  have resolventStrong (index : ℕ) :
      ∀ (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (limit : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong sequence limit →
        core.Strong (fun level => finiteResolvent index level (sequence level)) (limitResolvent index limit) :=
    xiNativeFiniteResolvent_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
      normalizedConvergence originalDense (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index)
      (QuadraticEnergySpace.canonicalYosidaStep_le_one index)
  have resolventIdentityLimit
      (values : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)) :
      Tendsto (fun index => limitResolvent index values) atTop (nhds values) :=
    QuadraticEnergySpace.smallStepResolvent_strong_limit originalDomain originalForm nonnegative closable originalDense
      QuadraticEnergySpace.canonicalYosidaStep QuadraticEnergySpace.canonicalYosidaStep_positive
      QuadraticEnergySpace.canonicalYosidaStep_le_one QuadraticEnergySpace.canonicalYosidaStep_tendsto values
  have yosidaStrong (index : ℕ) :
      core.Strong (fun level => finiteYosida index level (forcing level)) (limitYosida index target) :=
    xiNativeYosidaSemigroup_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
      normalizedConvergence originalDense (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index)
      (QuadraticEnergySpace.canonicalYosidaStep_le_one index) time forcing target forcingStrong
  have yosidaLimit : Tendsto (fun index => limitYosida index target) atTop (nhds limitSemigroup) :=
    QuadraticEnergySpace.closedSemigroup_approximation_limit originalDomain originalForm nonnegative closable
      originalDense time target
  have initialErrorLimit : Tendsto
      (fun index => 2 * ‖target - limitResolvent index target‖) atTop (nhds 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      ((tendsto_const_nhds (x := target)).sub (resolventIdentityLimit target)).norm.const_mul 2
  intro tolerance tolerancePositive
  obtain ⟨smoothingIndex, smoothingSmall⟩ :=
    (initialErrorLimit.eventually_lt_const (by positivity : 0 < tolerance / 8)).exists
  let smoothed (level : ℕ) := finiteResolvent smoothingIndex level (forcing level)
  let smoothedTarget := limitResolvent smoothingIndex target
  have smoothedStrong : core.Strong smoothed smoothedTarget :=
    resolventStrong smoothingIndex forcing target forcingStrong
  let generatorValues (level : ℕ) :=
    xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization (smoothed level)
  let generatorTarget := QuadraticEnergySpace.closedGenerator originalDomain originalForm nonnegative closable
    originalDense
    ((QuadraticEnergySpace.smallStepEquiv originalDomain originalForm nonnegative closable originalDense
      (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)
      (QuadraticEnergySpace.canonicalYosidaStep_positive smoothingIndex)
      (QuadraticEnergySpace.canonicalYosidaStep_le_one smoothingIndex)).symm target)
  have limitGraph : (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)⁻¹ •
      (target - smoothedTarget) = generatorTarget := by
    simpa only [QuadraticEnergySpace.yosidaGenerator, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, smoothedTarget, limitResolvent,
      generatorTarget] using
      QuadraticEnergySpace.yosidaGenerator_eq_closedGenerator originalDomain originalForm nonnegative closable
        originalDense (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)
        (QuadraticEnergySpace.canonicalYosidaStep_positive smoothingIndex)
        (QuadraticEnergySpace.canonicalYosidaStep_le_one smoothingIndex) target
  have generatorStrong : core.Strong generatorValues generatorTarget := by
    have scaled := core.strong_const_smul (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)⁻¹
      (core.strong_sub forcingStrong smoothedStrong)
    have finiteGraph : generatorValues = (fun level =>
        (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)⁻¹ •
          (forcing level - smoothed level)) := by
      funext level
      exact xiNativeFiniteGenerator_resolvent_graph system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent mass level resistanceRate normalization ratePositive.le normalizationPositive.le
        (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)
        (QuadraticEnergySpace.canonicalYosidaStep_positive smoothingIndex) (forcing level)
    rw [finiteGraph, ← limitGraph]
    exact scaled
  have inputNormLimit : Tendsto (fun level => ‖forcing level - smoothed level‖)
      atTop (nhds ‖target - smoothedTarget‖) :=
    core.strong_norm_sub_tendsto forcingStrong smoothedStrong
  have generatorDefectLimit (index : ℕ) :
      Tendsto (fun level => ‖generatorValues level - finiteResolvent index level (generatorValues level)‖)
        atTop (nhds ‖generatorTarget - limitResolvent index generatorTarget‖) :=
    core.strong_norm_sub_tendsto generatorStrong
      (resolventStrong index generatorValues generatorTarget generatorStrong)
  have generatorErrorLimit : Tendsto
      (fun index => (time : ℝ) * ‖generatorTarget - limitResolvent index generatorTarget‖)
        atTop (nhds 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      ((tendsto_const_nhds (x := generatorTarget)).sub
        (resolventIdentityLimit generatorTarget)).norm.const_mul (time : ℝ)
  have targetErrorLimit : Tendsto
      (fun index => ‖limitYosida index target - limitSemigroup‖) atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using
      (yosidaLimit.sub (tendsto_const_nhds (x := limitSemigroup))).norm
  obtain ⟨yosidaIndex, generatorSmall, targetSmall⟩ :=
    ((generatorErrorLimit.eventually_lt_const (by positivity : 0 < tolerance / 8)).and
      (targetErrorLimit.eventually_lt_const (by positivity : 0 < tolerance / 3))).exists
  have comparisonNormLimit : Tendsto (fun level =>
      2 * ‖forcing level - smoothed level‖ +
        (time : ℝ) * ‖generatorValues level - finiteResolvent yosidaIndex level (generatorValues level)‖)
      atTop (nhds (2 * ‖target - smoothedTarget‖ +
        (time : ℝ) * ‖generatorTarget - limitResolvent yosidaIndex generatorTarget‖)) :=
    (inputNormLimit.const_mul 2).add ((generatorDefectLimit yosidaIndex).const_mul (time : ℝ))
  have comparisonLimitSmall : 2 * ‖target - smoothedTarget‖ +
      (time : ℝ) * ‖generatorTarget - limitResolvent yosidaIndex generatorTarget‖ < tolerance / 3 := by
    change 2 * ‖target - smoothedTarget‖ < tolerance / 8 at smoothingSmall
    linarith
  have comparisonBound (level : ℕ) :
      ‖finiteSemigroup level (forcing level) - finiteYosida yosidaIndex level (forcing level)‖ ≤
        2 * ‖forcing level - smoothed level‖ +
          (time : ℝ) * ‖generatorValues level -
            finiteResolvent yosidaIndex level (generatorValues level)‖ := by
    have smoothedComparison :
        ‖finiteSemigroup level (smoothed level) - finiteYosida yosidaIndex level (smoothed level)‖ ≤
          (time : ℝ) * ‖generatorValues level -
            finiteResolvent yosidaIndex level (generatorValues level)‖ := by
      simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using
        xiNativeFiniteSemigroup_yosida_error system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le
          (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex)
          (QuadraticEnergySpace.canonicalYosidaStep_positive yosidaIndex) time time.coe_nonneg (smoothed level)
    apply contraction_comparison_after_smoothing (finiteSemigroup level) (finiteYosida yosidaIndex level)
      (xiNativeFiniteSemigroup_norm system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le time time.coe_nonneg)
      _ (forcing level) (smoothed level) _ smoothedComparison
    exact BoundedYosida.semigroup_norm_le_one _
      (xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le
        (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex)
        (QuadraticEnergySpace.canonicalYosidaStep_positive yosidaIndex)).2
      (QuadraticEnergySpace.canonicalYosidaStep yosidaIndex)
      (QuadraticEnergySpace.canonicalYosidaStep_positive yosidaIndex) time time.coe_nonneg
  have comparisonsSmall : ∀ᶠ level in atTop,
      2 * ‖forcing level - smoothed level‖ +
        (time : ℝ) * ‖generatorValues level - finiteResolvent yosidaIndex level (generatorValues level)‖ <
          tolerance / 3 := comparisonNormLimit.eventually_lt_const comparisonLimitSmall
  obtain ⟨element, limitClose, sequenceClose⟩ :=
    yosidaStrong yosidaIndex (tolerance / 3) (by positivity)
  refine ⟨element, ?_, ?_⟩
  · have triangle : ‖core.embed element - limitSemigroup‖ ≤
        ‖core.embed element - limitYosida yosidaIndex target‖ +
          ‖limitYosida yosidaIndex target - limitSemigroup‖ := by
      calc
        _ = ‖(core.embed element - limitYosida yosidaIndex target) +
            (limitYosida yosidaIndex target - limitSemigroup)‖ :=
          congrArg norm (sub_add_sub_cancel _ _ _).symm
        _ ≤ _ := norm_add_le _ _
    exact triangle.trans_lt (by linarith)
  · filter_upwards [comparisonsSmall, sequenceClose] with level comparisonSmall sequenceClose
    have triangle : ‖finiteSemigroup level (forcing level) - core.restrict level element‖ ≤
        ‖finiteSemigroup level (forcing level) - finiteYosida yosidaIndex level (forcing level)‖ +
          ‖finiteYosida yosidaIndex level (forcing level) - core.restrict level element‖ := by
      calc
        _ = ‖(finiteSemigroup level (forcing level) - finiteYosida yosidaIndex level (forcing level)) +
            (finiteYosida yosidaIndex level (forcing level) - core.restrict level element)‖ :=
          congrArg norm (sub_add_sub_cancel _ _ _).symm
        _ ≤ _ := norm_add_le _ _
    exact triangle.trans_lt (by linarith [comparisonBound level])

theorem exists_xiNativeFiniteSemigroupStrong_of_rules (system : EIGSData K)
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
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
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
      let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
          mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
        ∀ (time : ℝ≥0)
          (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
          (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass)),
        core.Strong forcing target →
        core.Strong (fun level => xiNativeFiniteSemigroup system rulesConnected mass level
          resistanceRate normalization time (forcing level))
          (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
            originalDense time target) := by
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
  exact xiNativeFiniteSemigroup_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense


end
end EIGS

#print axioms IGS.Sec31.contraction_comparison_after_smoothing
#print axioms EIGS.xiNativeFiniteSemigroup_strong_limit

#print axioms EIGS.exists_xiNativeFiniteSemigroupStrong_of_rules
