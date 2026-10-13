import RequestProject.Section31.EIGSContinuousResolventContraction
import RequestProject.Section31.EIGSNativeSupShortTimeOfRules
import RequestProject.Section31.EIGSNativeSupResolventApproximation
import RequestProject.Section31.GeometricResolventClockTail

/-! Sup approximate identity for the actual continuous resolvents. The native
short-time walk estimate supplies the finite geometric expansion, actual
jump rates diverge, and genuine uniform finite-resolvent convergence passes
the estimate to the continuous representative. No C-space C0 assertion is
an input to the original-rule theorem. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiContinuous_uniform_limit_norm_le_eventually
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected)
    (values : (level : ℕ) → XiVtx system level → ℝ)
    (limit : C(parameters.LimitSpace, ℝ)) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (valuesBound : ∀ᶠ level in atTop, ∀ vertex, |values level vertex| ≤ bound)
    (uniformConvergence : Tendsto (fun level => ‖fun vertex : XiVtx system level =>
      values level vertex - limit (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0)) :
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
    ‖limit‖ ≤ bound := by
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  obtain ⟨threshold, afterThreshold⟩ := eventually_atTop.mp valuesBound
  let boundedValues : (level : ℕ) → XiVtx system level → ℝ :=
    fun level => if threshold ≤ level then values level else 0
  have boundedEverywhere (level : ℕ) (vertex : XiVtx system level) :
      |boundedValues level vertex| ≤ bound := by
    by_cases ordered : threshold ≤ level
    · simpa only [boundedValues, if_pos ordered] using afterThreshold level ordered vertex
    · simpa only [boundedValues, if_neg ordered, Pi.zero_apply, abs_zero] using boundNonnegative
  have boundedConvergence : Tendsto (fun level => ‖fun vertex : XiVtx system level =>
      boundedValues level vertex - limit (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0) := by
    apply uniformConvergence.congr'
    filter_upwards [eventually_ge_atTop threshold] with level ordered
    simp only [boundedValues, if_pos ordered]
  exact xiContinuous_uniform_limit_norm_le system rulesConnected parameters distanceGreaterThanOne
    boundedValues limit bound boundNonnegative boundedEverywhere boundedConvergence

#print axioms EIGS.xiContinuous_uniform_limit_norm_le_eventually

theorem xiNativeResolvent_uniform_limits_approximate_identity
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    ∀ (function : C(parameters.LimitSpace, ℝ)) (error : ℝ), 0 < error →
      ∃ thresholdStep : ℝ, 0 < thresholdStep ∧
        ∀ (step : ℝ) (stepPositive : 0 < step) (_stepAtMostOne : step ≤ 1)
          (limit : C(parameters.LimitSpace, ℝ)),
        Tendsto (fun level => ‖fun vertex : XiVtx system level =>
          xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
            mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive
            (core.restrict level (BoundedContinuousFunction.mkOfCompact function)) vertex -
          limit (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0) →
        step < thresholdStep → ‖limit - function‖ < error := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  dsimp only
  intro function error errorPositive
  obtain ⟨window, windowPositive, windowSmall, threshold, shortTime⟩ :=
    xiNativeSupTransition_short_time_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive function (error / 2) (half_pos errorPositive)
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext renormalizationEigenpair)
  simp only [← rateEquality] at shortTime
  have exponentialLimit : Tendsto (fun height : ℝ => 2 * ‖function‖ * Real.exp (-height)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (2 * ‖function‖)
  obtain ⟨height, heightPositive, tailSmall⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (exponentialLimit.eventually_lt_const (half_pos errorPositive))).exists
  refine ⟨window / (4 * height), by positivity, ?_⟩
  intro step stepPositive stepAtMostOne limit uniformConvergence stepSmall
  have quotientLower : height < window / (4 * step) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4 * step)).mpr
    have productSmall := (lt_div_iff₀ (by positivity : 0 < 4 * height)).mp stepSmall
    nlinarith
  have exponentialBound : Real.exp (-window / (4 * step)) ≤ Real.exp (-height) := by
    apply Real.exp_le_exp.mpr
    calc
      -window / (4 * step) = -(window / (4 * step)) := by ring
      _ ≤ -height := neg_le_neg quotientLower.le
  have tailAtStep : 2 * ‖function‖ * Real.exp (-window / (4 * step)) < error / 2 :=
    (mul_le_mul_of_nonneg_left exponentialBound (by positivity)).trans_lt tailSmall
  have jumpRateLimit := xiNativeFiniteJumpRate_tendsto_atTop system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass distancePositive resistanceRate normalization ratePositive normalizationPositive
    resistanceVector vectorPositive (funext renormalizationEigenpair)
  have windowRates : Tendsto (fun level => window * xiNativeFiniteJumpRate system level resistanceRate normalization)
      atTop atTop := jumpRateLimit.const_mul_atTop windowPositive
  have stepRates : Tendsto (fun level => step * xiNativeFiniteJumpRate system level resistanceRate normalization)
      atTop atTop := jumpRateLimit.const_mul_atTop stepPositive
  let values : (level : ℕ) → XiVtx system level → ℝ := fun level vertex =>
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive
      (core.restrict level (BoundedContinuousFunction.mkOfCompact function)) vertex -
    function (parameters.vertexEmbedding level vertex)
  have valuesBound : ∀ᶠ level in atTop, ∀ vertex,
      |values level vertex| ≤ error / 2 + 2 * ‖function‖ * Real.exp (-window / (4 * step)) := by
    filter_upwards [eventually_ge_atTop threshold,
      windowRates.eventually (eventually_ge_atTop 2), stepRates.eventually (eventually_ge_atTop 1)]
        with level afterThreshold windowRateLarge stepRateLarge
    let rate := xiNativeFiniteJumpRate system level resistanceRate normalization
    have nativeRatePositive : 0 < rate := xiNativeFiniteJumpRate_positive system mass level
      resistanceRate normalization ratePositive normalizationPositive
    let forcing : XiVtx system level → ℝ := fun vertex => function (parameters.vertexEmbedding level vertex)
    have forcingNorm : ‖forcing‖ ≤ ‖function‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro vertex
      exact function.norm_coe_le_norm _
    have shortPowers : ∀ index < Nat.floor (window * rate),
        ‖(xiNativeSupTransition system rulesConnected level ^ index) forcing - forcing‖ ≤ error / 2 := by
      intro index before
      have indexBound : (index : ℝ) ≤ window * rate :=
        (by exact_mod_cast before.le : (index : ℝ) ≤ (Nat.floor (window * rate) : ℝ)).trans
          (Nat.floor_le (mul_nonneg windowPositive.le nativeRatePositive.le))
      have estimate := shortTime level afterThreshold ((index : ℝ) / rate)
        (div_nonneg (Nat.cast_nonneg index) nativeRatePositive.le)
        ((div_le_iff₀ nativeRatePositive).mpr indexBound)
      change ‖(xiNativeSupTransition system rulesConnected level ^
        Nat.floor (((index : ℝ) / rate) * rate)) forcing - forcing‖ ≤ error / 2 at estimate
      simpa only [div_mul_cancel₀ _ (ne_of_gt nativeRatePositive), Nat.floor_natCast] using estimate
    have finiteEstimate := xiNativeFiniteResolvent_sup_approximation system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level resistanceRate normalization ratePositive.le normalizationPositive.le
      step stepPositive forcing (error / 2) (half_pos errorPositive).le (Nat.floor (window * rate)) shortPowers
    have geometricBound := geometric_resolvent_floor_clock_tail step window rate stepPositive windowPositive
      nativeRatePositive windowRateLarge stepRateLarge
    have ratioNonnegative : 0 ≤ step * rate / (1 + step * rate) := by positivity
    have forcingEquality : core.restrict level (BoundedContinuousFunction.mkOfCompact function) =
        xiFiniteSpeedL2 system mass level forcing :=
      xiSpeedL2Core_restrict_eq_finiteSpeedL2 system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
        (BoundedContinuousFunction.mkOfCompact function) level
    have finiteNormBound : ‖values level‖ ≤ error / 2 + 2 * ‖function‖ * Real.exp (-window / (4 * step)) := by
      calc
        ‖values level‖ = ‖fun vertex : XiVtx system level =>
            xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
              mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive
              (xiFiniteSpeedL2 system mass level forcing) vertex - forcing vertex‖ := by
          dsimp only [values]
          rw [forcingEquality]
        _ ≤ error / 2 + 2 * (step * rate / (1 + step * rate)) ^ Nat.floor (window * rate) * ‖forcing‖ := finiteEstimate
        _ ≤ error / 2 + 2 * (step * rate / (1 + step * rate)) ^ Nat.floor (window * rate) * ‖function‖ := by
          gcongr
        _ ≤ error / 2 + 2 * ‖function‖ * Real.exp (-window / (4 * step)) := by
          nlinarith [mul_le_mul_of_nonneg_left geometricBound (by positivity : 0 ≤ 2 * ‖function‖)]
    intro vertex
    have pointBound : |values level vertex| ≤ ‖values level‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (values level) vertex
    exact pointBound.trans finiteNormBound
  have differenceConvergence : Tendsto (fun level => ‖fun vertex : XiVtx system level =>
      values level vertex - (limit - function) (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0) := by
    convert uniformConvergence using 1
    funext level
    congr 1
    funext vertex
    dsimp only [values, ContinuousMap.sub_apply]
    ring
  have continuousBound := xiContinuous_uniform_limit_norm_le_eventually system rulesConnected parameters distanceGreaterThanOne
    values (limit - function) (error / 2 + 2 * ‖function‖ * Real.exp (-window / (4 * step)))
    (by positivity) valuesBound differenceConvergence
  exact continuousBound.trans_lt (by linarith)

#print axioms EIGS.xiNativeResolvent_uniform_limits_approximate_identity

def XiContinuousResolventApproximateIdentityProperties (system : EIGSData K)
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
        (nhds function))

theorem xiContinuousResolventApproximateIdentityProperties_of_contraction (system : EIGSData K)
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
    (contractionProperties : XiContinuousResolventContractionProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive) :
    XiContinuousResolventApproximateIdentityProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
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
  dsimp only [XiContinuousResolventContractionProperties, XiContinuousResolventApproximateIdentityProperties]
    at contractionProperties ⊢
  obtain ⟨originalDense, contractionProperties⟩ := contractionProperties
  choose resolvers resolverNorm resolverRepresentations using contractionProperties
  have approximation (function : C(parameters.LimitSpace, ℝ)) (error : ℝ) (errorPositive : 0 < error) :
      ∃ thresholdStep : ℝ, 0 < thresholdStep ∧
        ∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1),
          step < thresholdStep → ‖resolvers step stepPositive stepAtMostOne function - function‖ < error := by
    obtain ⟨thresholdStep, thresholdPositive, estimate⟩ :=
      xiNativeResolvent_uniform_limits_approximate_identity system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive mass resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair normalization normalizationPositive function error errorPositive
    refine ⟨thresholdStep, thresholdPositive, ?_⟩
    intro step stepPositive stepAtMostOne stepSmall
    exact estimate step stepPositive stepAtMostOne (resolvers step stepPositive stepAtMostOne function)
      (resolverRepresentations step stepPositive stepAtMostOne function).2 stepSmall
  refine ⟨originalDense, resolvers, ?_, approximation, ?_⟩
  · intro step stepPositive stepAtMostOne
    exact ⟨resolverNorm step stepPositive stepAtMostOne, resolverRepresentations step stepPositive stepAtMostOne⟩
  · intro function
    apply Metric.tendsto_nhds.2
    intro error errorPositive
    obtain ⟨thresholdStep, thresholdPositive, estimate⟩ := approximation function error errorPositive
    apply eventually_comap.mpr
    filter_upwards [eventually_lt_nhds thresholdPositive] with step stepSmall
    intro admissibleStep equality
    rw [dist_eq_norm]
    exact estimate admissibleStep.1 admissibleStep.2.1 admissibleStep.2.2
      (by simpa only [equality] using stepSmall)

theorem exists_xiContinuousResolventApproximateIdentity_of_rules (system : EIGSData K)
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
        atTop (nhds (normalization • resistanceVector)) ∧
      XiContinuousResolventApproximateIdentityProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, contractionProperties⟩ :=
    exists_xiContinuousResolventContraction_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiContinuousResolventApproximateIdentityProperties_of_contraction system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive contractionProperties


end
end EIGS

#print axioms EIGS.xiContinuousResolventApproximateIdentityProperties_of_contraction
#print axioms EIGS.exists_xiContinuousResolventApproximateIdentity_of_rules
