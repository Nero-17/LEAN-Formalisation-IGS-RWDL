import RequestProject.Section31.GeometricLogarithmicHeatTimeChoice
import Mathlib.Tactic

/-! Convert eventual geometric ball mass bounds to every small radius.
The level threshold controls only the final positive radius cutoff. -/

namespace IGS.Sec31
noncomputable section

theorem geometric_logarithmic_ball_mass_upper_all_radii
    (volume : ℝ → ℝ) (volumeMonotone : Monotone volume)
    (rate massRate exponent logExponent radiusScale coefficient : ℝ)
    (rateGreaterThanOne : 1 < rate) (exponentNonnegative : 0 ≤ exponent)
    (growthIdentity : massRate = rate ^ exponent) (logExponentNonnegative : 0 ≤ logExponent)
    (radiusScalePositive : 0 < radiusScale) (coefficientPositive : 0 < coefficient)
    (threshold : ℕ)
    (levelUpper : ∀ level : ℕ, threshold ≤ level →
      volume (radiusScale * rate⁻¹ ^ level) ≤
        coefficient * (level + 2 : ℝ) ^ logExponent / massRate ^ level) :
    ∃ upperConstant radiusThreshold : ℝ, 0 < upperConstant ∧ 0 < radiusThreshold ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
        volume radius ≤ upperConstant * radius ^ exponent * |Real.log radius| ^ logExponent := by
  have ratePositive := zero_lt_one.trans rateGreaterThanOne
  have logRatePositive := Real.log_pos rateGreaterThanOne
  have massPositive : 0 < massRate := by
    rw [growthIdentity]
    exact Real.rpow_pos_of_pos ratePositive _
  let logarithmConstant :=
    (|Real.log radiusScale| + 1 + 2 * Real.log rate) / Real.log rate
  have logarithmConstantPositive : 0 < logarithmConstant := by
    dsimp only [logarithmConstant]
    exact div_pos (by positivity) (Real.log_pos rateGreaterThanOne)
  let upperConstant := coefficient * logarithmConstant ^ logExponent *
    (rate / radiusScale) ^ exponent
  have upperConstantPositive : 0 < upperConstant := by
    dsimp only [upperConstant]
    exact mul_pos (mul_pos coefficientPositive
      (Real.rpow_pos_of_pos logarithmConstantPositive _))
      (Real.rpow_pos_of_pos (div_pos ratePositive radiusScalePositive) _)
  refine ⟨upperConstant, min (radiusScale / rate ^ threshold) (Real.exp (-1)),
    upperConstantPositive,
    lt_min (div_pos radiusScalePositive (pow_pos ratePositive _)) (Real.exp_pos _), ?_⟩
  intro radius radiusPositive radiusSmall
  obtain ⟨level, afterThreshold, powerLower, powerUpper, logarithmBound⟩ :=
    geometric_heat_time_level_with_log_bound rate radiusScale radius rateGreaterThanOne
      radiusScalePositive radiusPositive threshold
      (radiusSmall.trans (min_le_left _ _)) (radiusSmall.trans (min_le_right _ _))
  have radiusAtLevel : radius ≤ radiusScale * rate⁻¹ ^ level := by
    rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos ratePositive level)).mpr
    simpa only [mul_comm] using (le_div_iff₀ radiusPositive).mp powerLower
  have baseLower : radiusScale / (rate * radius) ≤ rate ^ level := by
    have divided : (radiusScale / radius) / rate < rate ^ level :=
      (div_lt_iff₀ ratePositive).mpr (by simpa only [pow_succ] using powerUpper)
    simpa only [div_div, mul_comm radius rate] using divided.le
  have basePositive : 0 < radiusScale / (rate * radius) := by positivity
  have massLower : (radiusScale / (rate * radius)) ^ exponent ≤ massRate ^ level := by
    calc
      _ ≤ (rate ^ level) ^ exponent :=
        Real.rpow_le_rpow basePositive.le baseLower exponentNonnegative
      _ = massRate ^ level := by
        rw [growthIdentity, ← Real.rpow_mul_natCast ratePositive.le,
          mul_comm exponent, Real.rpow_natCast_mul ratePositive.le]
  have logarithmCost : (level + 2 : ℝ) ^ logExponent ≤
      (logarithmConstant * |Real.log radius|) ^ logExponent := by
    apply Real.rpow_le_rpow (by positivity) _ logExponentNonnegative
    exact logarithmBound
  have comparison : coefficient * (level + 2 : ℝ) ^ logExponent / massRate ^ level ≤
      coefficient * (logarithmConstant * |Real.log radius|) ^ logExponent /
        (radiusScale / (rate * radius)) ^ exponent :=
    div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left logarithmCost coefficientPositive.le)
      (Real.rpow_pos_of_pos basePositive _) massLower
  have profileIdentity :
      coefficient * (logarithmConstant * |Real.log radius|) ^ logExponent /
        (radiusScale / (rate * radius)) ^ exponent =
      upperConstant * radius ^ exponent * |Real.log radius| ^ logExponent := by
    rw [Real.mul_rpow logarithmConstantPositive.le (abs_nonneg _),
      Real.div_rpow radiusScalePositive.le (mul_pos ratePositive radiusPositive).le,
      Real.mul_rpow ratePositive.le radiusPositive.le]
    dsimp only [upperConstant]
    rw [Real.div_rpow ratePositive.le radiusScalePositive.le]
    field_simp
    <;> ring
  exact (volumeMonotone radiusAtLevel).trans
    ((levelUpper level afterThreshold).trans (comparison.trans_eq profileIdentity))

end
end IGS.Sec31

#print axioms IGS.Sec31.geometric_logarithmic_ball_mass_upper_all_radii
