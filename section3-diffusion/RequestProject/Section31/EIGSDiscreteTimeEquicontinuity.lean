import RequestProject.Section31.EIGSDiscreteFiniteObservations

/-! Deterministic time perturbations for the actual integer-time walks.
These estimates do not assert control of a path supremum, stopping times,
or tightness of path laws. -/

namespace IGS.Sec31.PoissonizedWalk

theorem floor_clock_difference_le (rate first second : ℝ)
    (rateNonnegative : 0 ≤ rate) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) :
    |(Nat.floor (first * rate) : ℝ) - Nat.floor (second * rate)| ≤
      rate * |first - second| + 1 := by
  have firstLower := Nat.floor_le (mul_nonneg firstNonnegative rateNonnegative)
  have secondLower := Nat.floor_le (mul_nonneg secondNonnegative rateNonnegative)
  have firstUpper := Nat.lt_floor_add_one (first * rate)
  have secondUpper := Nat.lt_floor_add_one (second * rate)
  have positiveDifference := mul_le_mul_of_nonneg_left (le_abs_self (first - second)) rateNonnegative
  have negativeDifference := mul_le_mul_of_nonneg_left (neg_le_abs (first - second)) rateNonnegative
  apply abs_le.mpr
  constructor <;> nlinarith

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem contraction_floor_time_difference_le (transition : Space →L[ℝ] Space)
    (contraction : ‖transition‖ ≤ 1) (rate : ℝ) (ratePositive : 0 < rate)
    (first second : ℝ) (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second)
    (values : Space) :
    ‖(transition ^ Nat.floor (first * rate)) values -
      (transition ^ Nat.floor (second * rate)) values‖ ≤
        (|first - second| + rate⁻¹) * ‖(rate • (1 - transition)) values‖ := by
  have powerComparison := contraction_power_difference_le transition contraction values
    (Nat.floor (first * rate)) (Nat.floor (second * rate))
  have clockComparison := floor_clock_difference_le rate first second ratePositive.le
    firstNonnegative secondNonnegative
  have generatorNorm : ‖(rate • (1 - transition)) values‖ =
      rate * ‖transition values - values‖ := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, norm_smul, Real.norm_eq_abs, abs_of_pos ratePositive, norm_sub_rev]
  calc
    _ ≤ (rate * |first - second| + 1) * ‖transition values - values‖ :=
      powerComparison.trans (mul_le_mul_of_nonneg_right clockComparison (norm_nonneg _))
    _ = _ := by rw [generatorNorm]; field_simp [ratePositive.ne'] <;> ring

end IGS.Sec31.PoissonizedWalk

namespace EIGS

open MeasureTheory IGS.Sec31 Filter Topology
open scoped NNReal
noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization)

theorem xiNativeRandomWalk_floor_time_resolvent_comparison
    (step : ℝ) (stepPositive : 0 < step) (first second : ℝ≥0)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ‖(xiNativeRandomWalk system rulesConnected mass level ^
        Nat.floor ((first : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))
        (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive values) -
      (xiNativeRandomWalk system rulesConnected mass level ^
        Nat.floor ((second : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))
        (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive values)‖ ≤
      (|(first : ℝ) - second| + (xiNativeFiniteJumpRate system level resistanceRate normalization)⁻¹) *
        ((2 / step) * ‖values‖) := by
  have comparison := PoissonizedWalk.contraction_floor_time_difference_le
    (xiNativeRandomWalk system rulesConnected mass level)
    (xiNativeRandomWalk_norm_le_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level)
    (xiNativeFiniteJumpRate system level resistanceRate normalization)
    (xiNativeFiniteJumpRate_positive system mass level resistanceRate normalization ratePositive normalizationPositive)
    first second first.coe_nonneg second.coe_nonneg
    (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive values)
  rw [← xiNativeFiniteGenerator_eq_jumpRate] at comparison
  apply comparison.trans
  apply mul_le_mul_of_nonneg_left
    (xiNativeFiniteGenerator_resolvent_norm_le system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive normalizationPositive step stepPositive values)
  exact add_nonneg (abs_nonneg _) (inv_nonneg.mpr
    (xiNativeFiniteJumpRate_positive system mass level resistanceRate normalization ratePositive normalizationPositive).le)

theorem xiNativeDiscreteWalk_varying_time_strong_limit (system : EIGSData K)
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
      ∀ (time : ℝ≥0) (times : ℕ → ℝ≥0) (timeLimit : Tendsto times atTop (nhds time))
        (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong forcing target →
      core.Strong (fun level => (xiNativeRandomWalk system rulesConnected mass level ^
        Nat.floor ((times level : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization)) (forcing level))
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
  intro originalDense time times timeLimit forcing target forcingStrong
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

  have fixedTimeStrong := xiNativeDiscreteWalk_strong_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive normalizedConvergence originalDense
    time forcing target forcingStrong
  apply core.strong_of_norm_sub_tendsto_zero _ _ _ fixedTimeStrong
  have jumpRateLimit := xiNativeFiniteJumpRate_tendsto_atTop system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent mass distancePositive resistanceRate normalization ratePositive
    normalizationPositive resistanceVector vectorPositive (by
      funext colour
      exact renormalizationEigenpair colour)
  have inverseLimit : Tendsto (fun level =>
      (xiNativeFiniteJumpRate system level resistanceRate normalization)⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp jumpRateLimit
  have realTimeLimit : Tendsto (fun level => (times level : ℝ)) atTop (nhds (time : ℝ)) :=
    (NNReal.continuous_coe.tendsto time).comp timeLimit
  have displacementLimit : Tendsto (fun level => |(times level : ℝ) - time|) atTop (nhds (0 : ℝ)) := by
    simpa only [sub_self, abs_zero] using (realTimeLimit.sub_const (time : ℝ)).abs
  have coefficientLimit := displacementLimit.add inverseLimit
  have inputNormLimit := core.strong_norm_tendsto forcingStrong
  have smoothingLimit : Tendsto (fun index => ‖target - limitResolvent index target‖)
      atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds (x := target)).sub (resolventIdentityLimit target)).norm
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  obtain ⟨smoothingIndex, smoothingSmall⟩ :=
    (smoothingLimit.eventually_lt_const (by positivity : 0 < tolerance / 8)).exists
  have smoothedStrong := resolventStrong smoothingIndex forcing target forcingStrong
  have inputErrorLimit := core.strong_norm_sub_tendsto forcingStrong smoothedStrong
  have eventualInputSmall : ∀ᶠ level in atTop,
      ‖forcing level - finiteResolvent smoothingIndex level (forcing level)‖ < tolerance / 4 :=
    inputErrorLimit.eventually_lt_const (by linarith)
  have errorLimit : Tendsto (fun level =>
      (|(times level : ℝ) - time| + (xiNativeFiniteJumpRate system level resistanceRate normalization)⁻¹) *
        ((2 / QuadraticEnergySpace.canonicalYosidaStep smoothingIndex) * ‖forcing level‖))
      atTop (nhds (0 : ℝ)) := by
    simpa only [zero_add, zero_mul] using coefficientLimit.mul
      (inputNormLimit.const_mul (2 / QuadraticEnergySpace.canonicalYosidaStep smoothingIndex))
  have eventualErrorSmall := errorLimit.eventually_lt_const (by positivity : 0 < tolerance / 2)
  filter_upwards [eventualInputSmall, eventualErrorSmall] with level inputSmall errorSmall
  have powerContraction (jumps : ℕ) :
      ‖xiNativeRandomWalk system rulesConnected mass level ^ jumps‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro values
    simpa only [one_mul] using xiNativeRandomWalk_power_apply_norm_le system rulesConnected
      rulesLoopless rulesUnique plantingNonadjacent mass level jumps values
  have smoothedComparison := xiNativeRandomWalk_floor_time_resolvent_comparison system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent mass level resistanceRate normalization
    ratePositive normalizationPositive (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)
    (QuadraticEnergySpace.canonicalYosidaStep_positive smoothingIndex) (times level) time (forcing level)
  have comparison := contraction_comparison_after_smoothing
    (xiNativeRandomWalk system rulesConnected mass level ^
      Nat.floor ((times level : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))
    (xiNativeRandomWalk system rulesConnected mass level ^
      Nat.floor ((time : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))
    (powerContraction _) (powerContraction _) (forcing level)
    (finiteResolvent smoothingIndex level (forcing level)) _ smoothedComparison
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact comparison.trans_lt (by linarith)

theorem exists_xiNativeDiscreteVaryingTimeStrong_of_rules (system : EIGSData K)
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
        ∀ (time : ℝ≥0) (times : ℕ → ℝ≥0) (timeLimit : Tendsto times atTop (nhds time))
          (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
          (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass)),
        core.Strong forcing target →
        core.Strong (fun level => (xiNativeRandomWalk system rulesConnected mass level ^
          Nat.floor ((times level : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization)) (forcing level))
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
  exact xiNativeDiscreteWalk_varying_time_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense

end
end EIGS

#print axioms IGS.Sec31.PoissonizedWalk.floor_clock_difference_le
#print axioms IGS.Sec31.PoissonizedWalk.contraction_floor_time_difference_le
#print axioms EIGS.xiNativeRandomWalk_floor_time_resolvent_comparison

#print axioms EIGS.xiNativeDiscreteWalk_varying_time_strong_limit
#print axioms EIGS.exists_xiNativeDiscreteVaryingTimeStrong_of_rules
