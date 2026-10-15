import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! A deterministic conversion of arbitrarily fine DHL cell-scale volume
gains to the original logarithmic-radius lower profile. -/

namespace IGS.Sec31
open Filter Topology
noncomputable section

theorem infinite_geometric_volume_lower_logarithmic
    (volume : ℝ → ℝ) (coefficient radiusFactor epsilon : ℝ)
    (coefficientPositive : 0 < coefficient) (radiusFactorPositive : 0 < radiusFactor)
    (epsilonPositive : 0 < epsilon) (epsilonBelowOne : epsilon < 1)
    (infiniteScales : ∀ threshold : ℕ, ∃ level : ℕ, threshold ≤ level ∧
      coefficient * (level : ℝ) ^ (1 - epsilon) / (4 : ℝ) ^ level ≤
        volume (radiusFactor * (2 : ℝ)⁻¹ ^ level)) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ radiusThreshold : ℝ, 0 < radiusThreshold →
      ∃ radius : ℝ, 0 < radius ∧ radius < radiusThreshold ∧
        lower * |Real.log radius| ^ (1 - epsilon) * radius ^ 2 ≤ volume radius := by
  let logarithmConstant := |Real.log radiusFactor| + Real.log 2
  have logarithmPositive : 0 < logarithmConstant :=
    add_pos_of_nonneg_of_pos (abs_nonneg _) (Real.log_pos (by norm_num))
  let lower := coefficient / (radiusFactor ^ 2 * logarithmConstant ^ (1 - epsilon))
  have lowerPositive : 0 < lower := div_pos coefficientPositive
    (mul_pos (sq_pos_of_pos radiusFactorPositive) (Real.rpow_pos_of_pos logarithmPositive _))
  refine ⟨lower, lowerPositive, ?_⟩
  intro radiusThreshold thresholdPositive
  have radiusLimit : Tendsto (fun level : ℕ => radiusFactor * (2 : ℝ)⁻¹ ^ level) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul radiusFactor
  obtain ⟨threshold, small⟩ := eventually_atTop.mp (radiusLimit.eventually (gt_mem_nhds thresholdPositive))
  obtain ⟨level, large, volumeLower⟩ := infiniteScales (max threshold 1)
  have levelAboveOne : (1 : ℝ) ≤ level := by
    exact_mod_cast (le_max_right threshold 1).trans large
  have radiusPositive : 0 < radiusFactor * (2 : ℝ)⁻¹ ^ level := by positivity
  have logarithmIdentity : Real.log (radiusFactor * (2 : ℝ)⁻¹ ^ level) =
      Real.log radiusFactor - (level : ℝ) * Real.log 2 := by
    rw [Real.log_mul radiusFactorPositive.ne' (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) level).ne',
      Real.log_pow, Real.log_inv]
    ring
  have logarithmBound : |Real.log (radiusFactor * (2 : ℝ)⁻¹ ^ level)| ≤
      logarithmConstant * (level : ℝ) := by
    rw [logarithmIdentity]
    have triangle := abs_sub_le (Real.log radiusFactor) 0 ((level : ℝ) * Real.log 2)
    simp only [sub_zero, zero_sub, abs_neg] at triangle
    have productNonnegative : 0 ≤ (level : ℝ) * Real.log 2 :=
      mul_nonneg (Nat.cast_nonneg level) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    rw [abs_of_nonneg productNonnegative] at triangle
    dsimp only [logarithmConstant]
    nlinarith [abs_nonneg (Real.log radiusFactor)]
  have logarithmPower : |Real.log (radiusFactor * (2 : ℝ)⁻¹ ^ level)| ^ (1 - epsilon) ≤
      logarithmConstant ^ (1 - epsilon) * (level : ℝ) ^ (1 - epsilon) := by
    have bound := Real.rpow_le_rpow (abs_nonneg _) logarithmBound (by linarith : 0 ≤ 1 - epsilon)
    simpa only [Real.mul_rpow logarithmPositive.le (Nat.cast_nonneg level)] using bound
  have radiusSquare : (radiusFactor * (2 : ℝ)⁻¹ ^ level) ^ 2 = radiusFactor ^ 2 / (4 : ℝ) ^ level := by
    rw [mul_pow]
    have power : (((2 : ℝ)⁻¹) ^ level) ^ 2 = ((4 : ℝ) ^ level)⁻¹ := by
      calc
        _ = (((2 : ℝ)⁻¹) ^ 2) ^ level := by rw [← pow_mul, ← pow_mul]; congr 1; omega
        _ = ((4 : ℝ)⁻¹) ^ level := by norm_num
        _ = _ := inv_pow _ _
    rw [power, div_eq_mul_inv]
  refine ⟨radiusFactor * (2 : ℝ)⁻¹ ^ level, radiusPositive,
    small level ((le_max_left threshold 1).trans large), ?_⟩
  calc
    lower * |Real.log (radiusFactor * (2 : ℝ)⁻¹ ^ level)| ^ (1 - epsilon) *
        (radiusFactor * (2 : ℝ)⁻¹ ^ level) ^ 2 ≤
      lower * (logarithmConstant ^ (1 - epsilon) * (level : ℝ) ^ (1 - epsilon)) *
        (radiusFactor * (2 : ℝ)⁻¹ ^ level) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left logarithmPower lowerPositive.le) (sq_nonneg _)
    _ = coefficient * (level : ℝ) ^ (1 - epsilon) / (4 : ℝ) ^ level := by
      rw [radiusSquare]
      dsimp only [lower]
      field_simp [radiusFactorPositive.ne', (Real.rpow_pos_of_pos logarithmPositive (1 - epsilon)).ne']
      <;> ring
    _ ≤ _ := volumeLower

end
end IGS.Sec31

#print axioms IGS.Sec31.infinite_geometric_volume_lower_logarithmic
