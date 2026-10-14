import RequestProject.Section31.EIGSHarmonicNodalCutoff
import RequestProject.Section31.EIGSClosedEvaluationContinuousRepresentative
import RequestProject.Section31.EIGSDegreeHeatExponent
import RequestProject.Section31.QuadraticEnergyRieszCutoffLower
import RequestProject.Section31.CompactContinuousKernelRows
import RequestProject.Section31.GeometricDiagonalHeatUpper

/-! Finite-born lower bounds for half-time Riesz rows of the actual closed
semigroup. The cutoff is the constructed harmonic extension of a finite
vertex spike. Its norm and energy estimates use the proved incidence growth.
The closed point evaluation, its continuous agreement, all-scale estimates,
and the semigroup increment are filled internally. No semigroup-cutoff
closeness, local profile or desired diagonal estimate is assumed. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical BigOperators BoundedContinuousFunction NNReal ENNReal
noncomputable section
set_option maxHeartbeats 8000000
variable {K : ℕ}

theorem exists_xiFiniteBorn_riesz_diagonal_lower (system : EIGSData K)
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
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    letI finiteBornLowerStatementCompactSpace := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair
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
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair mass))),
    ∀ (birth : ℕ) (vertex : XiVtx system birth),
      ∃ lowerConstant cutoffTime : ℝ, 0 < lowerConstant ∧ 0 < cutoffTime ∧ cutoffTime ≤ 1 ∧
        ∀ (time : ℝ≥0), 0 < time → (time : ℝ) ≤ cutoffTime →
        ∀ smoothing : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass) →L[ℝ]
            C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
          (∀ forcing, xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass (smoothing forcing) =
              QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense
                (time / 2) forcing) →
          lowerConstant / (time : ℝ) ^ ((Real.log mass.rate -
            Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) / Real.log (mass.rate * resistanceRate)) ≤
              ‖continuousOperatorKernelRow smoothing (xiCompletionEmbedding system rulesConnected lengths lengthsPositive
                distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex)‖ ^ 2 := by
  letI finiteBornLowerProofCompactSpace := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive
    distanceRate distanceRateGreaterThanOne metricEigenpair
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
  dsimp only
  intro originalDense birth vertex
  obtain ⟨normConstant, energyConstant, normPositive, energyPositive, evaluation, _, pointBound, evaluationAgreement⟩ :=
    exists_xiClosedFiniteBorn_point_evaluation_with_continuous_agreement system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair primitiveDegree birth vertex
  obtain ⟨cutoffMassConstant, cutoffTraceConstant, cutoffMassPositive, cutoffTracePositive, cutoffs⟩ :=
    exists_xiHarmonic_nodal_cutoffs system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      distancePositive oneColourDistance
  obtain ⟨degreePositive, degreeGrowth⟩ := degree_spectral_growth_from_primitive_rules system rulesConnected primitiveDegree
  obtain ⟨degreeLower, degreeUpper, degreeLowerPositive, degreeUpperPositive, degreeBounds⟩ := degreeGrowth birth vertex
  let degreeRate := finiteRealMatrixSpectralRadius (degreeMatrix system)
  let growthRate := mass.rate / degreeRate
  let decayRate := degreeRate * resistanceRate
  let exponent := (Real.log mass.rate - Real.log degreeRate) / Real.log (mass.rate * resistanceRate)
  let scaledNormConstant := normConstant * mass.rate ^ birth
  let scaledEnergyConstant := energyConstant / resistanceRate ^ birth
  let cutoffNormConstant := cutoffMassConstant * degreeUpper / mass.rate ^ birth
  let cutoffEnergyConstant := cutoffTraceConstant * degreeUpper * resistanceRate ^ birth
  have massPositive := mass.rate_positive
  have growthPositive : 0 < growthRate := div_pos massPositive degreePositive
  have decayPositive : 0 < decayRate := mul_pos degreePositive ratePositive
  have scaledNormPositive : 0 < scaledNormConstant := mul_pos normPositive (pow_pos massPositive birth)
  have scaledEnergyPositive : 0 < scaledEnergyConstant := div_pos energyPositive (pow_pos ratePositive birth)
  have cutoffNormPositive : 0 < cutoffNormConstant :=
    div_pos (mul_pos cutoffMassPositive degreeUpperPositive) (pow_pos massPositive birth)
  have cutoffEnergyPositive : 0 < cutoffEnergyConstant :=
    mul_pos (mul_pos cutoffTracePositive degreeUpperPositive) (pow_pos ratePositive birth)
  have degreeMass : degreeRate < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_primitive system rulesConnected rulesLoopless plantingNonadjacent distancePositive primitiveDegree
  have timeGreaterThanOne : 1 < mass.rate * resistanceRate :=
    xiAnalyticTimeRate_gt_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      mass resistanceRate ratePositive resistanceVector vectorPositive (by funext colour; exact renormalizationEigenpair colour)
  have exponentBounds : 0 < exponent ∧ exponent < 1 :=
    xiFiniteBorn_heat_exponent_between_zero_one system rulesConnected rulesLoopless plantingNonadjacent distancePositive
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair primitiveDegree
  have timeScaleIdentity : mass.rate * resistanceRate = growthRate * decayRate := by
    dsimp only [growthRate, decayRate]
    field_simp [(show degreeRate ≠ 0 from degreePositive.ne')]
  have growthIdentity : growthRate = (mass.rate * resistanceRate) ^ exponent := by
    have logarithmic := (geometric_growth_logarithmic_exponent (mass.rate * resistanceRate) growthRate
      timeGreaterThanOne ((one_le_div degreePositive).mpr degreeMass.le)).2
    dsimp only [growthRate] at logarithmic
    rw [Real.log_div massPositive.ne' (show degreeRate ≠ 0 from degreePositive.ne')] at logarithmic
    exact logarithmic
  have scaledPointBound : ∀ (target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative) age,
      evaluation target ^ 2 ≤ scaledNormConstant * growthRate ^ age * ‖target.val‖ ^ 2 +
        scaledEnergyConstant / decayRate ^ age *
          QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target := by
    intro target age
    have normCoefficient : normConstant * (mass.rate ^ (birth + age) / degreeRate ^ age) =
        scaledNormConstant * growthRate ^ age := by
      dsimp only [scaledNormConstant, growthRate]
      rw [pow_add, div_pow]
      ring
    have energyCoefficient : energyConstant * (1 / (degreeRate ^ age * resistanceRate ^ (birth + age))) =
        scaledEnergyConstant / decayRate ^ age := by
      dsimp only [scaledEnergyConstant, decayRate]
      rw [pow_add, mul_pow]
      field_simp [degreePositive.ne', ratePositive.ne']
      <;> ring
    have actual := pointBound age target
    change evaluation target ^ 2 ≤
      (normConstant * (mass.rate ^ (birth + age) / degreeRate ^ age)) * ‖target.val‖ ^ 2 +
        (energyConstant * (1 / (degreeRate ^ age * resistanceRate ^ (birth + age)))) *
          QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target at actual
    rw [normCoefficient, energyCoefficient] at actual
    exact actual
  have actualCutoffs : ∀ age, ∃ cutoff : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
      evaluation cutoff = 1 ∧ ‖cutoff.val‖ ^ 2 ≤ cutoffNormConstant / growthRate ^ age ∧
        QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable cutoff ≤
          cutoffEnergyConstant * decayRate ^ age := by
    intro age
    obtain ⟨extension, _, valuesAtLevel, _, _, normBound, traceIdentity, traceBound⟩ :=
      cutoffs (birth + age) (xiForward system birth age vertex)
    have finiteEnergy : xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ := by
      rw [traceIdentity]
      exact ENNReal.ofReal_ne_top
    obtain ⟨membership, energyIdentity⟩ := xiContinuous_finite_energy_closedForm_eq system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair extension finiteEnergy closable
    let cutoff : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative :=
      ⟨xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass extension,
        membership⟩
    have incidenceUpper : (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) ≤
        degreeUpper * degreeRate ^ age := by
      rw [xiVertexIncidenceCount_eq_degree_state_sum]
      exact (degreeBounds age).2
    refine ⟨cutoff, ?_, ?_, ?_⟩
    · rw [evaluationAgreement cutoff extension rfl]
      have centerValue := valuesAtLevel (xiForward system birth age vertex)
      rw [xiCompletionEmbedding_forward] at centerValue
      simpa only [xiNodalSpike, if_pos rfl] using centerValue
    · have enlarged := normBound.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left incidenceUpper cutoffMassPositive.le) (pow_pos massPositive (birth + age)).le)
      change ‖cutoff.val‖ ^ 2 ≤ cutoffNormConstant / growthRate ^ age
      have coefficientIdentity : cutoffMassConstant * (degreeUpper * degreeRate ^ age) / mass.rate ^ (birth + age) =
          cutoffNormConstant / growthRate ^ age := by
        dsimp only [cutoffNormConstant, growthRate]
        rw [pow_add, div_pow]
        field_simp [degreePositive.ne', massPositive.ne']
        <;> ring
      rw [← coefficientIdentity]
      exact enlarged
    · change QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable
        ⟨xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass extension,
          membership⟩ ≤ _
      rw [energyIdentity]
      have enlarged := traceBound.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left incidenceUpper cutoffTracePositive.le) (pow_pos ratePositive (birth + age)).le)
      convert enlarged using 1
      dsimp only [cutoffEnergyConstant, decayRate]
      rw [pow_add, mul_pow]
      ring
  let pointCoefficient := (2 * scaledNormConstant + 4 * scaledEnergyConstant) * growthRate
  have holderPositive : 0 < 1 - exponent := sub_pos.mpr exponentBounds.2
  have smallCoefficientContinuous : ContinuousAt (fun value : ℝ =>
      pointCoefficient * cutoffEnergyConstant * value ^ (1 - exponent)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 (1 - exponent) (Or.inr holderPositive.le))
  obtain ⟨duration, durationPositive, nearZero⟩ :=
    Metric.continuousAt_iff.mp smallCoefficientContinuous (1 / 4) (by norm_num)
  let cutoffTime : ℝ := min 1 (duration / 2)
  have cutoffTimePositive : 0 < cutoffTime := lt_min zero_lt_one (half_pos durationPositive)
  have cutoffTimeAtMostOne : cutoffTime ≤ 1 := min_le_left _ _
  have cutoffTimeNear : dist cutoffTime (0 : ℝ) < duration := by
    rw [Real.dist_eq, sub_zero, abs_of_pos cutoffTimePositive]
    exact (min_le_right _ _).trans_lt (half_lt_self durationPositive)
  have smallTimeBound : pointCoefficient * cutoffEnergyConstant * cutoffTime ^ (1 - exponent) ≤ (1 / 4 : ℝ) := by
    have near := nearZero cutoffTimeNear
    simp only [Real.zero_rpow holderPositive.ne', mul_zero, Real.dist_eq, sub_zero] at near
    exact (abs_lt.mp near).2.le
  refine ⟨(cutoffTime / (mass.rate * resistanceRate)) ^ exponent / (4 * cutoffNormConstant), cutoffTime,
    div_pos (Real.rpow_pos_of_pos (div_pos cutoffTimePositive (mul_pos massPositive ratePositive)) _)
      (mul_pos (by norm_num : (0 : ℝ) < 4) cutoffNormPositive),
    cutoffTimePositive, cutoffTimeAtMostOne, ?_⟩
  intro time timePositive timeAtMostCutoff smoothing compatibility
  have timeRealPositive : 0 < (time : ℝ) := timePositive
  obtain ⟨age, timeAtScale, growthBound⟩ := geometric_cutoff_lower_scale_choice
    (mass.rate * resistanceRate) growthRate exponent cutoffTime (time : ℝ) timeGreaterThanOne
    exponentBounds.1.le growthIdentity timeRealPositive timeAtMostCutoff
  obtain ⟨cutoff, cutoffValue, cutoffNormBound, cutoffEnergyBound⟩ := actualCutoffs age
  have halfTimeAtScale : ((time / 2 : ℝ≥0) : ℝ) ≤ cutoffTime / (mass.rate * resistanceRate) ^ age := by
    have halfAtMost : (time / 2 : ℝ≥0) ≤ time := by exact div_le_self (by positivity) (by norm_num)
    exact (show ((time / 2 : ℝ≥0) : ℝ) ≤ (time : ℝ) from halfAtMost).trans timeAtScale
  have rowBound := QuadraticEnergySpace.closedSemigroup_rieszRow_norm_sq_lower_at_cutoff_scale
    originalDomain originalForm nonnegative closable originalDense evaluation
    (mass.rate * resistanceRate) growthRate decayRate exponent scaledNormConstant scaledEnergyConstant
    timeGreaterThanOne growthPositive decayPositive timeScaleIdentity exponentBounds.1.le exponentBounds.2 growthIdentity
    scaledNormPositive.le scaledEnergyPositive.le scaledPointBound cutoffNormConstant cutoffEnergyConstant cutoffTime
    cutoffNormPositive cutoffEnergyPositive.le cutoffTimePositive smallTimeBound age cutoff cutoffValue cutoffNormBound cutoffEnergyBound
    (time / 2) (by positivity) (by
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      linarith [timeAtMostCutoff.trans cutoffTimeAtMostOne]) halfTimeAtScale
    (continuousOperatorKernelRow smoothing (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex)) (by
      intro lifted liftedAgreement
      calc
        evaluation lifted = smoothing cutoff.val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex) :=
          evaluationAgreement lifted (smoothing cutoff.val) ((compatibility cutoff.val).trans liftedAgreement.symm)
        _ = _ := continuousOperatorKernelRow_represents smoothing _ cutoff.val)
  have scaledLower := (div_le_div_of_nonneg_right growthBound
    (mul_pos (by norm_num : (0 : ℝ) < 4) cutoffNormPositive).le).trans rowBound
  have quotientIdentity : (cutoffTime / ((mass.rate * resistanceRate) * (time : ℝ))) ^ exponent /
        (4 * cutoffNormConstant) =
      ((cutoffTime / (mass.rate * resistanceRate)) ^ exponent / (4 * cutoffNormConstant)) /
        (time : ℝ) ^ exponent := by
    rw [← div_div cutoffTime (mass.rate * resistanceRate) (time : ℝ),
      Real.div_rpow (div_pos cutoffTimePositive (mul_pos massPositive ratePositive)).le timeRealPositive.le]
    ring
  rw [quotientIdentity] at scaledLower
  exact scaledLower

end
end EIGS

#print axioms EIGS.exists_xiFiniteBorn_riesz_diagonal_lower
