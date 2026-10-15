import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! A matching logarithmic volume lower bound at arbitrarily small radii
precludes every strictly smaller eventual logarithmic upper exponent. -/

namespace IGS.Sec31
noncomputable section

theorem logarithmic_volume_lower_excludes_smaller_exponent
    (volume : ℝ → ℝ) (exponent : ℝ) (exponentBelowOne : exponent < 1)
    (lower : ℝ) (lowerPositive : 0 < lower)
    (arbitrarilySmall : ∀ radiusThreshold : ℝ, 0 < radiusThreshold →
      ∃ radius : ℝ, 0 < radius ∧ radius < radiusThreshold ∧
        lower * |Real.log radius| ^ (1 - (1 - exponent) / 2) * radius ^ 2 ≤ volume radius) :
    ∀ upper : ℝ, 0 < upper → ∀ radiusThreshold : ℝ, 0 < radiusThreshold →
      ∃ radius : ℝ, 0 < radius ∧ radius < radiusThreshold ∧
        upper * |Real.log radius| ^ exponent * radius ^ 2 < volume radius := by
  intro upper upperPositive radiusThreshold thresholdPositive
  let gap := (1 - exponent) / 2
  have gapPositive : 0 < gap := div_pos (sub_pos.mpr exponentBelowOne) (by norm_num)
  let logarithmThreshold := max 1 ((upper / lower + 1) ^ gap⁻¹)
  have thresholdAboveOne : (1 : ℝ) ≤ logarithmThreshold := le_max_left _ _
  have logarithmThresholdPositive : 0 < logarithmThreshold := zero_lt_one.trans_le thresholdAboveOne
  have thresholdPower : upper / lower + 1 ≤ logarithmThreshold ^ gap := by
    have bound := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) gap⁻¹)
      (le_max_right (1 : ℝ) ((upper / lower + 1) ^ gap⁻¹)) gapPositive.le
    rw [Real.rpow_inv_rpow (by positivity : 0 ≤ upper / lower + 1) gapPositive.ne'] at bound
    exact bound
  obtain ⟨radius, positive, small, volumeLower⟩ := arbitrarilySmall
    (min radiusThreshold (Real.exp (-logarithmThreshold)))
    (lt_min thresholdPositive (Real.exp_pos _))
  have logSmall : Real.log radius ≤ -logarithmThreshold := by
    have comparison := Real.log_le_log positive (small.le.trans (min_le_right _ _))
    simpa only [Real.log_exp] using comparison
  have logMagnitude : logarithmThreshold ≤ |Real.log radius| := by
    rw [abs_of_nonpos (by linarith : Real.log radius ≤ 0)]
    linarith
  have logPositive : 0 < |Real.log radius| := logarithmThresholdPositive.trans_le logMagnitude
  have gain := thresholdPower.trans
    (Real.rpow_le_rpow logarithmThresholdPositive.le logMagnitude gapPositive.le)
  have ratioStrict : upper / lower < |Real.log radius| ^ gap :=
    lt_of_lt_of_le (by linarith : upper / lower < upper / lower + 1) gain
  have factorStrict : upper < lower * |Real.log radius| ^ gap := by
    simpa only [mul_comm] using (div_lt_iff₀ lowerPositive).mp ratioStrict
  have exponentIdentity : 1 - (1 - exponent) / 2 = exponent + gap := by
    dsimp only [gap]
    ring
  rw [exponentIdentity, Real.rpow_add logPositive] at volumeLower
  refine ⟨radius, positive, small.trans_le (min_le_left _ _), ?_⟩
  calc
    upper * |Real.log radius| ^ exponent * radius ^ 2 <
        (lower * |Real.log radius| ^ gap) * |Real.log radius| ^ exponent * radius ^ 2 :=
      mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right factorStrict (Real.rpow_pos_of_pos logPositive _)) (sq_pos_of_pos positive)
    _ = lower * (|Real.log radius| ^ exponent * |Real.log radius| ^ gap) * radius ^ 2 := by ring
    _ ≤ _ := volumeLower

end
end IGS.Sec31

#print axioms IGS.Sec31.logarithmic_volume_lower_excludes_smaller_exponent
