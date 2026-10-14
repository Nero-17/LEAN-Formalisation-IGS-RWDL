import RequestProject.Section31.DiameterNormalizationHomeomorph
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Exact ball identity and quantitative local volume transport under
positive diameter scaling. The measure and its measurable space are kept
fixed; only the explicit ball metric is rescaled. -/

namespace EIGS.MeasuredGHP
open Metric Set
noncomputable section

theorem diameterNormalized_ball_eq_native (Space : Type) [original : MetricSpace Space]
    (diameterPositive : 0 < Metric.diam (univ : Set Space)) (center : Space) (radius : ℝ) :
    @Metric.ball Space (normalizedMetric Space original diameterPositive).toPseudoMetricSpace center radius =
      Metric.ball center (Metric.diam (univ : Set Space) * radius) := by
  ext other
  change (Metric.diam (univ : Set Space))⁻¹ * dist other center < radius ↔
    dist other center < Metric.diam (univ : Set Space) * radius
  rw [mul_comm (Metric.diam (univ : Set Space))⁻¹, ← div_eq_mul_inv,
    div_lt_iff₀ diameterPositive, mul_comm radius]

end
end EIGS.MeasuredGHP

namespace IGS.Sec31
noncomputable section

theorem local_power_volume_lower_positive_scaling
    (volume : ℝ → ℝ) (diameter exponent coefficient threshold : ℝ)
    (diameterPositive : 0 < diameter) (coefficientPositive : 0 < coefficient)
    (thresholdPositive : 0 < threshold)
    (lower : ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
      coefficient * radius ^ exponent ≤ volume radius) :
    ∃ scaledCoefficient scaledThreshold : ℝ, 0 < scaledCoefficient ∧ 0 < scaledThreshold ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ scaledThreshold →
        scaledCoefficient * radius ^ exponent ≤ volume (diameter * radius) := by
  refine ⟨coefficient * diameter ^ exponent, threshold / diameter,
    mul_pos coefficientPositive (Real.rpow_pos_of_pos diameterPositive _),
    div_pos thresholdPositive diameterPositive, ?_⟩
  intro radius radiusPositive radiusSmall
  have multipliedSmall : diameter * radius ≤ threshold := by
    simpa only [mul_comm] using (le_div_iff₀ diameterPositive).mp radiusSmall
  have bound := lower (diameter * radius) (mul_pos diameterPositive radiusPositive) multipliedSmall
  simpa only [Real.mul_rpow diameterPositive.le radiusPositive.le, mul_assoc] using bound

theorem local_logarithmic_volume_upper_positive_scaling
    (volume : ℝ → ℝ) (diameter exponent logExponent coefficient threshold : ℝ)
    (diameterPositive : 0 < diameter) (logExponentNonnegative : 0 ≤ logExponent)
    (coefficientPositive : 0 < coefficient) (thresholdPositive : 0 < threshold)
    (upper : ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
      volume radius ≤ coefficient * radius ^ exponent * |Real.log radius| ^ logExponent) :
    ∃ scaledCoefficient scaledThreshold : ℝ, 0 < scaledCoefficient ∧ 0 < scaledThreshold ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ scaledThreshold →
        volume (diameter * radius) ≤
          scaledCoefficient * radius ^ exponent * |Real.log radius| ^ logExponent := by
  let logarithmFactor := 1 + |Real.log diameter|
  have logarithmFactorPositive : 0 < logarithmFactor := by dsimp only [logarithmFactor]; positivity
  refine ⟨coefficient * diameter ^ exponent * logarithmFactor ^ logExponent,
    min (threshold / diameter) (Real.exp (-1)),
    mul_pos (mul_pos coefficientPositive (Real.rpow_pos_of_pos diameterPositive _))
      (Real.rpow_pos_of_pos logarithmFactorPositive _),
    lt_min (div_pos thresholdPositive diameterPositive) (Real.exp_pos _), ?_⟩
  intro radius radiusPositive radiusSmall
  have nativeSmall : diameter * radius ≤ threshold := by
    simpa only [mul_comm] using (le_div_iff₀ diameterPositive).mp
      (radiusSmall.trans (min_le_left _ _))
  have logarithmSmall : Real.log radius ≤ -1 := by
    have compared := Real.log_le_log radiusPositive (radiusSmall.trans (min_le_right _ _))
    simpa only [Real.log_exp] using compared
  have logarithmLarge : 1 ≤ |Real.log radius| := by
    rw [abs_of_nonpos (logarithmSmall.trans (by norm_num))]
    linarith
  have logarithmComparison : |Real.log (diameter * radius)| ≤ logarithmFactor * |Real.log radius| := by
    rw [Real.log_mul diameterPositive.ne' radiusPositive.ne']
    have triangle := abs_add_le (Real.log diameter) (Real.log radius)
    have scaled := mul_le_mul_of_nonneg_left logarithmLarge (abs_nonneg (Real.log diameter))
    dsimp only [logarithmFactor]
    nlinarith
  have powerComparison := Real.rpow_le_rpow (abs_nonneg (Real.log (diameter * radius)))
    logarithmComparison logExponentNonnegative
  have multiplied := mul_le_mul_of_nonneg_left powerComparison
    (mul_pos coefficientPositive (Real.rpow_pos_of_pos (mul_pos diameterPositive radiusPositive) exponent)).le
  have identity : coefficient * (diameter * radius) ^ exponent *
        (logarithmFactor * |Real.log radius|) ^ logExponent =
      (coefficient * diameter ^ exponent * logarithmFactor ^ logExponent) *
        radius ^ exponent * |Real.log radius| ^ logExponent := by
    rw [Real.mul_rpow diameterPositive.le radiusPositive.le,
      Real.mul_rpow logarithmFactorPositive.le (abs_nonneg _)]
    ring
  exact (upper (diameter * radius) (mul_pos diameterPositive radiusPositive) nativeSmall).trans
    (multiplied.trans_eq identity)

end
end IGS.Sec31

#print axioms EIGS.MeasuredGHP.diameterNormalized_ball_eq_native
#print axioms IGS.Sec31.local_power_volume_lower_positive_scaling
#print axioms IGS.Sec31.local_logarithmic_volume_upper_positive_scaling
