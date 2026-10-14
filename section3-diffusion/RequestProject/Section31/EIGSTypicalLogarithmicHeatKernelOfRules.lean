import RequestProject.Section31.EIGSContinuousKernelLocalStayLowerOfRules
import RequestProject.Section31.EIGSTypicalLogarithmicBallMass
import RequestProject.Section31.GeometricFixedBufferBallMass
import RequestProject.Section31.GeometricLogarithmicHeatLowerOptimization
import RequestProject.Section31.ContinuousKernelLocalLowerMeasurable
import RequestProject.Section31.NashTwoScaleOptimization
import RequestProject.Section31.EIGSAnalyticTimeScale
import RequestProject.Section2PrimitiveIntegerGrowth

/-! Actual typical-point heat lower bound with the precise logarithmic
exponent, for the same strict jointly continuous kernel and its global
upper bound. Collar probability, physical ball mass, all-point native stay,
same-closed-semigroup identification, geometric optimization and physical
AE transfer are all consumed internally. Final assumptions are the original
rules and the paper's standing primitive-degree condition; no restriction
that the resistance rate exceed one is added. The nonprimitive degree-rate
one convention is a separate unproved extension, not asserted here.
Candidate source: no compilation is claimed. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 9000000
variable {K : ℕ}

def XiTypicalLogarithmicHeatKernelProperties (system : EIGSData K)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
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
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
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
      ∃ timeThreshold : ℝ, 0 < timeThreshold ∧ ∃ upperConstant : ℝ, 0 < upperConstant ∧
        ∃ kernel : {time : ℝ≥0 // 0 < time} → parameters.LimitSpace → parameters.LimitSpace → ℝ,
          Continuous (fun point : {time : ℝ≥0 // 0 < time} × parameters.LimitSpace × parameters.LimitSpace =>
            kernel point.1 point.2.1 point.2.2) ∧
          (∀ time : {time : ℝ≥0 // 0 < time},
            (∀ first second, kernel time first second = kernel time second first) ∧
            (∀ first second, 0 < kernel time first second) ∧
            (∀ first second, kernel time first second ≤ upperConstant / (min ((time.val : ℝ) / 2) timeThreshold) ^
              (Real.log mass.rate / Real.log (mass.rate * resistanceRate))) ∧
            (∀ point, (∫ other, kernel time point other ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) = 1) ∧
            (∀ (function : C(parameters.LimitSpace, ℝ)) point,
              semigroup time.val function point = ∫ other, kernel time point other * function other
                ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
                  (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) ∧
            ∃ lifted : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
                (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) →L[ℝ]
                C(parameters.LimitSpace, ℝ),
              (∀ forcing point, lifted forcing point = ∫ other, kernel time point other * forcing other
                ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
                  (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) ∧
              ∀ forcing,
                xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
                  (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
                  (lifted forcing) =
                QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time.val forcing) ∧
          ∀ epsilon : ℝ, 0 < epsilon →
          ∀ᵐ point ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass,
          ∃ lowerConstant : ℝ, 0 < lowerConstant ∧ ∃ timeThreshold : ℝ, 0 < timeThreshold ∧
          ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ timeThreshold →
          lowerConstant * (time.val : ℝ) ^ (-(Real.log mass.rate / Real.log (mass.rate * resistanceRate))) *
            |Real.log (time.val : ℝ)| ^
              (-(1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + epsilon)) ≤
          kernel time point point

theorem xiTypicalLogarithmicHeatKernelProperties_of_actual_local_lower (system : EIGSData K)
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
    (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (lowerProperties : XiContinuousKernelLocalStayLowerProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair) :
    XiTypicalLogarithmicHeatKernelProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
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
  dsimp only [XiContinuousKernelLocalStayLowerProperties, XiTypicalLogarithmicHeatKernelProperties]
    at lowerProperties ⊢
  obtain ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
    kernel, jointContinuous, kernelProperties, fraction, fractionPositive, count, inverseBallLower⟩ := lowerProperties
  refine ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
    kernel, jointContinuous, kernelProperties, ?_⟩
  intro epsilon epsilonPositive
  let degreeRate := finiteRealMatrixSpectralRadius (degreeMatrix system)
  let timeRate := mass.rate * resistanceRate
  let exponent := Real.log mass.rate / Real.log timeRate
  let logExponent := 1 / (Real.log mass.rate / Real.log degreeRate - 1) + epsilon
  have degreeGreaterThanOne : 1 < degreeRate := degree_spectralRadius_gt_one_of_primitive system primitiveDegree
  have degreePositive := zero_lt_one.trans degreeGreaterThanOne
  have degreeMass : degreeRate < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_primitive system rulesConnected rulesLoopless
      plantingNonadjacent distancePositive primitiveDegree
  have timeRateGreaterThanOne : 1 < timeRate := xiAnalyticTimeRate_gt_one system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive mass resistanceRate ratePositive
    resistanceVector vectorPositive (funext renormalizationEigenpair)
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    timeRate mass.rate timeRateGreaterThanOne (degreeGreaterThanOne.trans degreeMass).le
  obtain ⟨width, widthLarge, widthIdentity⟩ := logarithmic_collar_width_for_exact_exponent
    mass.rate degreeRate epsilon degreeGreaterThanOne degreeMass epsilonPositive
  have ratioLogPositive : 0 < Real.log (mass.rate / degreeRate) :=
    Real.log_pos ((one_lt_div degreePositive).mpr degreeMass)
  have widthPositive : 0 < width := (div_pos zero_lt_one ratioLogPositive).trans widthLarge
  have logExponentNonnegative : 0 ≤ logExponent := by
    change 0 ≤ 1 / (Real.log mass.rate / Real.log degreeRate - 1) + epsilon
    rw [← widthIdentity]
    exact mul_nonneg widthPositive.le (Real.log_pos degreeGreaterThanOne).le
  obtain ⟨massConstant, massConstantPositive, spatialFraction, spatialFractionPositive, ballMassAE⟩ :=
    exists_xiTypicalLogarithmicBallMass_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive primitiveDegree width widthLarge
  let outerFactor := 4 * ((count + 2 : ℝ) * (3 * xiRuleRadius system parameters.lengths + 1))
  obtain ⟨buffer, bufferFit⟩ := exists_fixed_geometric_buffer
    (system.distanceSpectralRadius rulesConnected) outerFactor spatialFraction
    distanceGreaterThanOne spatialFractionPositive
  have massCoefficientPositive : 0 < massConstant * mass.rate ^ buffer * degreeRate :=
    mul_pos (mul_pos massConstantPositive (pow_pos mass.rate_positive buffer)) degreePositive
  let coefficient := (9 / 16 : ℝ) / (massConstant * mass.rate ^ buffer * degreeRate)
  have coefficientPositive : 0 < coefficient := div_pos (by norm_num) massCoefficientPositive
  let realDiagonal : ℝ → parameters.LimitSpace → ℝ := fun time point =>
    if positive : 0 < time then kernel ⟨⟨time, positive.le⟩, positive⟩ point point else 0
  let weight : ℝ → ℝ := fun time => time ^ (-exponent) * |Real.log time| ^ (-logExponent)
  let thresholds : ℕ → ℝ := fun index => min (Real.exp (-1)) (1 / ((index : ℝ) + 1))
  have realDiagonalContinuous : ∀ time, 0 < time → Continuous (realDiagonal time) := by
    intro time positive
    dsimp only [realDiagonal]
    simp only [dif_pos positive]
    exact jointContinuous.comp (continuous_const.prodMk (continuous_id.prodMk continuous_id))
  have weightNonnegative : ∀ time : ℝ, 0 < time → time ≤ Real.exp (-1) → 0 ≤ weight time := by
    intro time positive small
    exact mul_nonneg (Real.rpow_nonneg positive.le _) (Real.rpow_nonneg (abs_nonneg _) _)
  have addressGood : ∀ᵐ address ∂mass.addressMeasure, ∃ coefficientIndex thresholdIndex : ℕ,
      ∀ time : ℝ, 0 < time → time ≤ thresholds thresholdIndex →
      (1 / ((coefficientIndex : ℝ) + 1)) * weight time ≤
        realDiagonal time (xiAddressLimit system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair address) := by
    filter_upwards [ballMassAE] with address ballEventually
    let center := xiAddressLimit system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair address
    obtain ⟨threshold, afterThreshold⟩ := Filter.eventually_atTop.mp ballEventually
    have levelLower : ∀ level : ℕ, threshold + buffer ≤ level → ∀ time : ℝ, 0 < time →
        time ≤ (2 * fraction) / timeRate ^ level →
        coefficient * mass.rate ^ level / (level + 2 : ℝ) ^ logExponent ≤ realDiagonal time center := by
      intro level levelLarge time positive timeAtLevel
      have bufferAtMost : buffer ≤ level := (Nat.le_add_left buffer threshold).trans levelLarge
      have coarseLarge : threshold ≤ level - buffer := by
        apply Nat.le_of_add_le_add_right
        exact levelLarge.trans_eq (Nat.sub_add_cancel bufferAtMost).symm
      let radius := (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
        (system.distanceSpectralRadius rulesConnected)⁻¹ ^ level)
      have radiusPositive : 0 < radius := by
        have ruleRadiusNonnegative := xiRuleRadius_nonnegative system
          (fun colour => (parameters.lengthsPositive colour).le)
        have distanceRatePositive := zero_lt_one.trans distanceGreaterThanOne
        dsimp only [radius]
        positivity
      have radiusFit : 4 * radius < spatialFraction *
          (system.distanceSpectralRadius rulesConnected)⁻¹ ^ (level - buffer) := by
        have fit := geometric_radius_fit_of_fixed_buffer
          (system.distanceSpectralRadius rulesConnected) outerFactor spatialFraction
          (zero_lt_one.trans distanceGreaterThanOne) buffer level bufferAtMost bufferFit
        convert fit using 1 <;> dsimp only [outerFactor, radius] <;> ring
      let law := xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      have coarseMass := afterThreshold (level - buffer) coarseLarge (4 * radius) radiusFit
      have shiftedMass := shifted_logarithmic_geometric_volume_bound mass.rate degreeRate width massConstant
        (law.real (Metric.closedBall center (4 * radius))) mass.rate_positive degreeGreaterThanOne.le
        widthPositive.le massConstantPositive.le buffer level bufferAtMost coarseMass
      have degreeCost := EIGS.logarithmic_ceiling_degree_cost_le degreeRate width
        degreeGreaterThanOne widthPositive.le level
      rw [widthIdentity] at degreeCost
      have volumeBound : law.real (Metric.closedBall center (4 * radius)) ≤
          (massConstant * mass.rate ^ buffer * degreeRate) * (level + 2 : ℝ) ^ logExponent / mass.rate ^ level := by
        have multiplied := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left degreeCost
            (mul_nonneg massConstantPositive.le (pow_nonneg mass.rate_positive.le buffer)))
          (pow_nonneg mass.rate_positive.le level)
        exact (shiftedMass.trans multiplied).trans_eq (by ring)
      have volumePositive : 0 < law.real (Metric.closedBall center (4 * radius)) :=
        ENNReal.toReal_pos
          (((xiLimitMeasure_ball_positive system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
            center (by positivity : 0 < 4 * radius)).trans_le
              (measure_mono Metric.ball_subset_closedBall)).ne') (measure_ne_top law _)
      have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
        ratePositive vectorPositive (funext renormalizationEigenpair)
      have timeRateEquality :
          realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive = timeRate := by
        rw [← XiMassParameters.rate_eq_spectralRadius system mass, ← rateEquality]
      have actualTimeBound : time ≤ (2 * fraction) *
          (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ level := by
        simpa only [timeRateEquality, inv_pow, div_eq_mul_inv] using timeAtLevel
      have inverseLower := inverseBallLower level ⟨⟨time, positive.le⟩, positive⟩ actualTimeBound center
      have reciprocals := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 9 / 16)
        volumePositive volumeBound
      have logPowerPositive : 0 < (level + 2 : ℝ) ^ logExponent := Real.rpow_pos_of_pos (by positivity) _
      have algebra : coefficient * mass.rate ^ level / (level + 2 : ℝ) ^ logExponent =
          (9 / 16 : ℝ) /
            ((massConstant * mass.rate ^ buffer * degreeRate) * (level + 2 : ℝ) ^ logExponent / mass.rate ^ level) := by
        dsimp only [coefficient]
        field_simp [massCoefficientPositive.ne', (pow_pos mass.rate_positive level).ne', logPowerPositive.ne']
        <;> ring
      rw [algebra]
      dsimp only [realDiagonal]
      rw [dif_pos positive]
      exact reciprocals.trans inverseLower
    obtain ⟨lowerConstant, lowerPositive, localThreshold, localThresholdPositive, lowerCurve⟩ :=
      geometric_logarithmic_heat_lower_of_eventual_levels timeRate mass.rate exponent logExponent
        (2 * fraction) coefficient timeRateGreaterThanOne exponentNonnegative growthIdentity
        logExponentNonnegative (by positivity) coefficientPositive (threshold + buffer)
        (fun time => realDiagonal time center) levelLower
    exact local_lower_archimedean_quantization realDiagonal weight (Real.exp (-1)) weightNonnegative
      center lowerConstant localThreshold lowerPositive localThresholdPositive
      (fun time positive small => by
        simpa only [weight, mul_assoc] using lowerCurve time positive small.le)
  have physicalGood := ae_quantized_local_lower_map mass.addressMeasure
    (xiAddressLimit system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair)
    (measurable_xiAddressLimit system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair)
    realDiagonal realDiagonalContinuous weight thresholds addressGood
  filter_upwards [physicalGood] with point bound
  obtain ⟨coefficientIndex, thresholdIndex, bound⟩ := bound
  refine ⟨1 / ((coefficientIndex : ℝ) + 1), by positivity,
    thresholds thresholdIndex, by dsimp only [thresholds]; positivity, ?_⟩
  intro time small
  have positive : 0 < (time.val : ℝ) := time.property
  have result := bound (time.val : ℝ) positive small
  simpa only [realDiagonal, dif_pos positive, weight, exponent, logExponent, timeRate, degreeRate, mul_assoc] using result

theorem exists_xiTypicalLogarithmicHeatKernel_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      XiTypicalLogarithmicHeatKernelProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, lowerProperties⟩ :=
    exists_xiContinuousKernelLocalStayLower_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiTypicalLogarithmicHeatKernelProperties_of_actual_local_lower system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair primitiveDegree lowerProperties

end
end EIGS

#print axioms EIGS.xiTypicalLogarithmicHeatKernelProperties_of_actual_local_lower
#print axioms EIGS.exists_xiTypicalLogarithmicHeatKernel_of_rules
