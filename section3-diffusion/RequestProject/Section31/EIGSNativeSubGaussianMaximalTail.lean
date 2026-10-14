import RequestProject.Section31.EIGSNativeFinestMeshNoExit
import RequestProject.Section31.GeometricExponentialTailOptimization
import RequestProject.Section31.SubGaussianLogarithmicExponent
import RequestProject.Section2SpectralScaleInequality

/-! The actual native finite walk has the optimized sub-Gaussian maximal
displacement tail. The coarse probability estimate, canonical rates,
geometric optimization and finest-mesh zero event are all supplied inside
the proof from the original rules. No Azuma or target exit-tail input occurs.
Transport to the original diameter-normalized balls is a separate consumer. -/

namespace EIGS
open MeasureTheory ProbabilityTheory IGS.Sec31
open scoped Classical
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

theorem exists_xiNativeSubGaussianMaximalTail_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    [∀ level, MeasurableSpace (XiVtx system level)]
    [∀ level, MeasurableSingletonClass (XiVtx system level)] :
    ∃ constant coefficient cutoff : ℝ, 0 < constant ∧ 0 < coefficient ∧ 0 < cutoff ∧
      ∀ (level : ℕ) (start : XiVtx system level) (radius time : ℝ),
        0 < radius → 0 < time → time ≤ cutoff * radius →
      let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
      let timeRate := realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive
      let walkExponent := Real.log timeRate / Real.log (system.distanceSpectralRadius rulesConnected)
      ((xiGraphWalkPathLaw system rulesConnected level start)
        (xiNativeMaximalDisplacementEvent system rulesConnected parameters level
          ⌊xiNativeFiniteJumpRate system level
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * time⌋₊ start radius)).toReal ≤
        constant * Real.exp (-coefficient * (radius ^ walkExponent / time) ^ (1 / (walkExponent - 1))) := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceRate := system.distanceSpectralRadius rulesConnected
  let timeRate := realMatrixSpectralRadius (massMatrixR system.toRuleData) *
    system.resistanceSpectralRadius rulesConnected distancePositive
  have distanceGeTwo : 2 ≤ distanceRate :=
    system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive
  have distanceGreaterThanOne : 1 < distanceRate := by linarith
  have distancePositiveRate := zero_lt_one.trans distanceGreaterThanOne
  have squareBound : distanceRate ^ 2 ≤ timeRate :=
    system.distanceSpectralRadius_sq_le_mass_mul_resistance rulesConnected rulesLoopless rulesUnique distancePositive
  have timeGreaterThanDistance : distanceRate < timeRate := by nlinarith
  have timeRatePositive := distancePositiveRate.trans timeGreaterThanDistance
  have quotientGreaterThanOne : 1 < timeRate / distanceRate :=
    (one_lt_div distancePositiveRate).mpr timeGreaterThanDistance
  have quotientPositive := zero_lt_one.trans quotientGreaterThanOne
  obtain ⟨fraction, decay, fractionPositive, decayPositive, decayLessThanOne, envelope⟩ :=
    exists_xiNativeRadiusExponentialEnvelope_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  obtain ⟨massPositive, massLower, massUpper, massLowerPositive, massUpperPositive, massBounds⟩ :=
    eigs_mass_spectral_growth system rulesConnected distancePositive
  have resistancePositive :=
    (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
  let jumpCoefficient := 2 * normalization * massUpper
  have jumpCoefficientPositive : 0 < jumpCoefficient := by dsimp [jumpCoefficient]; positivity
  have jumpUpper (level : ℕ) : xiNativeFiniteJumpRate system level
      (system.resistanceSpectralRadius rulesConnected distancePositive) normalization ≤ jumpCoefficient * timeRate ^ level := by
    have multiplied := mul_le_mul_of_nonneg_left (massBounds level).2
      (show 0 ≤ 2 * normalization *
        (system.resistanceSpectralRadius rulesConnected distancePositive) ^ level by positivity)
    dsimp only [xiNativeFiniteJumpRate]
    convert multiplied using 1 <;> simp only [jumpCoefficient, timeRate, mul_pow] <;> ring
  let spatialFactor := 3 * xiRuleRadius system parameters.lengths + 1
  have radiusNonnegative := xiRuleRadius_nonnegative system
    (fun colour => (parameters.lengthsPositive colour).le)
  have spatialFactorPositive : 0 < spatialFactor := by dsimp [spatialFactor]; positivity
  let spatialCoefficient := (-Real.log decay) / (4 * spatialFactor)
  have logarithmNegative := Real.log_neg decayPositive decayLessThanOne
  have spatialCoefficientPositive : 0 < spatialCoefficient :=
    div_pos (neg_pos.mpr logarithmNegative) (mul_pos (by norm_num) spatialFactorPositive)
  let timeCoefficient := 1 / fraction + jumpCoefficient * spatialCoefficient / (timeRate / distanceRate) + 1
  have timeCoefficientPositive : 0 < timeCoefficient := by dsimp [timeCoefficient]; positivity
  have fractionComparison : 1 / fraction ≤ timeCoefficient := by
    dsimp [timeCoefficient]
    have nonnegative : 0 ≤ jumpCoefficient * spatialCoefficient / (timeRate / distanceRate) := by positivity
    linarith
  have jumpComparison : jumpCoefficient * spatialCoefficient / (timeRate / distanceRate) ≤ timeCoefficient := by
    dsimp [timeCoefficient]
    have nonnegative : 0 ≤ 1 / fraction := by positivity
    linarith
  let exponent := Real.log distanceRate / Real.log (timeRate / distanceRate)
  let coefficient := spatialCoefficient / (2 * distanceRate) *
    (spatialCoefficient / (2 * timeCoefficient)) ^ exponent
  have coefficientPositive : 0 < coefficient := by dsimp [coefficient]; positivity
  refine ⟨Real.exp (2 * (-Real.log decay)), coefficient,
    spatialCoefficient / (2 * timeCoefficient), Real.exp_pos _, coefficientPositive, by positivity, ?_⟩
  intro level start radius time radiusPositive timePositive timeSmall
  dsimp only
  have timeSmall' : time ≤ spatialCoefficient * radius / (2 * timeCoefficient) := by
    convert timeSmall using 1 <;> ring
  obtain ⟨coarse, lower, upper, beforeFine, optimized⟩ := geometric_exponential_envelope_choice
    distanceRate timeRate timeCoefficient spatialCoefficient radius time (2 * (-Real.log decay))
    distanceGreaterThanOne timeGreaterThanDistance timeCoefficientPositive spatialCoefficientPositive
    radiusPositive timePositive timeSmall'
  have exponentIdentity : -(spatialCoefficient / (2 * distanceRate)) * radius *
      (spatialCoefficient * radius / (2 * timeCoefficient * time)) ^ exponent =
      -coefficient * (radius ^ (Real.log timeRate / Real.log distanceRate) / time) ^
        (1 / (Real.log timeRate / Real.log distanceRate - 1)) := by
    have ratioIdentity : spatialCoefficient * radius / (2 * timeCoefficient * time) =
        (spatialCoefficient / (2 * timeCoefficient)) * (radius / time) := by ring
    rw [ratioIdentity, Real.mul_rpow (by positivity) (by positivity)]
    calc
      _ = -coefficient * (radius * (radius / time) ^ exponent) := by
        dsimp only [coefficient]
        ring
      _ = _ := by
        rw [logarithmic_subGaussian_exponent_identity distanceRate timeRate radius time
          distanceGreaterThanOne timeGreaterThanDistance radiusPositive timePositive]
  by_cases coarseBefore : coarse ≤ level
  · obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le coarseBefore
    have actual := envelope coarse steps start radius time radiusPositive timePositive.le
    have rawExponentIdentity :
        2 * (-Real.log decay) + time / (fraction * timeRate⁻¹ ^ coarse) +
          Real.log decay * (radius / (4 * (spatialFactor * distanceRate⁻¹ ^ coarse))) =
        2 * (-Real.log decay) + (1 / fraction) * time * timeRate ^ coarse -
          spatialCoefficient * radius * distanceRate ^ coarse := by
      dsimp only [spatialCoefficient]
      rw [inv_pow, inv_pow]
      field_simp [fractionPositive.ne', spatialFactorPositive.ne',
        pow_ne_zero coarse timeRatePositive.ne', pow_ne_zero coarse distancePositiveRate.ne']
      <;> ring
    have rawBound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right fractionComparison timePositive.le)
      (pow_nonneg timeRatePositive.le coarse)
    have enlarged : Real.exp (2 * (-Real.log decay) + time / (fraction * timeRate⁻¹ ^ coarse) +
        Real.log decay * (radius / (4 * (spatialFactor * distanceRate⁻¹ ^ coarse)))) ≤
      Real.exp (2 * (-Real.log decay) + timeCoefficient * time * timeRate ^ coarse -
        spatialCoefficient * radius * distanceRate ^ coarse) := by
      rw [rawExponentIdentity]
      exact Real.exp_le_exp.mpr (by linarith [rawBound])
    have actualBound : ((xiGraphWalkPathLaw system rulesConnected (coarse + steps) start)
        (xiNativeMaximalDisplacementEvent system rulesConnected parameters (coarse + steps)
          ⌊xiNativeFiniteJumpRate system (coarse + steps)
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * time⌋₊ start radius)).toReal ≤
        Real.exp (2 * (-Real.log decay) + time / (fraction * timeRate⁻¹ ^ coarse) +
          Real.log decay * (radius / (4 * (spatialFactor * distanceRate⁻¹ ^ coarse)))) := actual
    have result := actualBound.trans (enlarged.trans optimized)
    change _ ≤ Real.exp (2 * (-Real.log decay)) *
      Real.exp (-(spatialCoefficient / (2 * distanceRate)) * radius *
        (spatialCoefficient * radius / (2 * timeCoefficient * time)) ^ exponent) at result
    rw [exponentIdentity] at result
    exact result
  · have fineBefore : level + 1 ≤ coarse := Nat.succ_le_of_lt (Nat.lt_of_not_ge coarseBefore)
    have meshLower := (pow_le_pow_right₀ quotientGreaterThanOne.le fineBefore).trans lower
    have meshTime : time * (timeRate / distanceRate) ^ level ≤
        spatialCoefficient * radius / (2 * timeCoefficient * (timeRate / distanceRate)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * timeCoefficient * (timeRate / distanceRate))).mpr
      have multiplied := (le_div_iff₀ (by positivity : 0 < 2 * timeCoefficient * time)).mp meshLower
      rw [pow_succ] at multiplied
      nlinarith [multiplied]
    have coefficientBound : jumpCoefficient * spatialCoefficient /
        (2 * timeCoefficient * (timeRate / distanceRate)) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * timeCoefficient * (timeRate / distanceRate))).mpr
      have multiplied := (div_le_iff₀ quotientPositive).mp jumpComparison
      nlinarith
    have speedBound :
        (Nat.floor (xiNativeFiniteJumpRate system level
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * time) : ℝ) *
            distanceRate⁻¹ ^ level ≤ radius / 2 := by
      have floorBound := Nat.floor_le (mul_nonneg
        (xiNativeFiniteJumpRate_nonnegative system level _ _ resistancePositive.le normalizationPositive.le) timePositive.le)
      have first := mul_le_mul_of_nonneg_right floorBound (pow_nonneg (inv_nonneg.mpr distancePositiveRate.le) level)
      have second := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (jumpUpper level) timePositive.le)
        (pow_nonneg (inv_nonneg.mpr distancePositiveRate.le) level)
      have speedIdentity : jumpCoefficient * timeRate ^ level * time * distanceRate⁻¹ ^ level =
          jumpCoefficient * (time * (timeRate / distanceRate) ^ level) := by
        rw [div_pow, inv_pow]
        ring
      rw [speedIdentity] at second
      have third := mul_le_mul_of_nonneg_left meshTime jumpCoefficientPositive.le
      have fourth := mul_le_mul_of_nonneg_right coefficientBound radiusPositive.le
      have combined : jumpCoefficient * (time * (timeRate / distanceRate) ^ level) ≤ radius / 2 := by
        calc
          _ ≤ jumpCoefficient * (spatialCoefficient * radius /
            (2 * timeCoefficient * (timeRate / distanceRate))) := third
          _ = (jumpCoefficient * spatialCoefficient /
            (2 * timeCoefficient * (timeRate / distanceRate))) * radius := by ring
          _ ≤ _ := by convert fourth using 1 <;> ring
      exact first.trans (second.trans combined)
    have zeroEvent := xiNativeMaximalDisplacementEvent_eq_zero_of_finest_mesh system rulesConnected
      parameters level ⌊xiNativeFiniteJumpRate system level
        (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * time⌋₊ start radius
      (speedBound.trans_lt (by linarith))
    rw [zeroEvent, ENNReal.toReal_zero]
    exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

end
end EIGS

#print axioms EIGS.exists_xiNativeSubGaussianMaximalTail_of_rules
