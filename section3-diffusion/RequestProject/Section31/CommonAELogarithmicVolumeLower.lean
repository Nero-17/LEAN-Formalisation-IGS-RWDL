import RequestProject.Section31.LogarithmicVolumeExponentOptimality
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Countably many cofinal logarithmic exponents give one full-measure set
on which every positive epsilon has arbitrarily small volume lower bounds. -/

namespace IGS.Sec31
open MeasureTheory
noncomputable section

theorem ae_all_logarithmic_volume_lower
    {State : Type*} [MeasurableSpace State] (law : Measure State)
    (volume : State → ℝ → ℝ)
    (eachEpsilon : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᵐ point ∂law, ∃ lower : ℝ, 0 < lower ∧
        ∀ radiusThreshold : ℝ, 0 < radiusThreshold →
          ∃ radius : ℝ, 0 < radius ∧ radius < radiusThreshold ∧
            lower * |Real.log radius| ^ (1 - epsilon) * radius ^ 2 ≤ volume point radius) :
    ∀ᵐ point ∂law, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ lower : ℝ, 0 < lower ∧ ∀ radiusThreshold : ℝ, 0 < radiusThreshold →
        ∃ radius : ℝ, 0 < radius ∧ radius < radiusThreshold ∧
          lower * |Real.log radius| ^ (1 - epsilon) * radius ^ 2 ≤ volume point radius := by
  have countableBounds := ae_all_iff.mpr (fun index : ℕ =>
    eachEpsilon (1 / ((index : ℝ) + 1)) (by positivity))
  filter_upwards [countableBounds] with point allIndices
  intro epsilon epsilonPositive
  obtain ⟨index, indexSmall⟩ := exists_nat_one_div_lt epsilonPositive
  obtain ⟨lower, lowerPositive, arbitrarilySmall⟩ := allIndices index
  refine ⟨lower, lowerPositive, ?_⟩
  intro radiusThreshold thresholdPositive
  obtain ⟨radius, positive, small, volumeLower⟩ := arbitrarilySmall
    (min radiusThreshold (Real.exp (-1))) (lt_min thresholdPositive (Real.exp_pos _))
  have logSmall : Real.log radius ≤ -1 := by
    have comparison := Real.log_le_log positive (small.le.trans (min_le_right _ _))
    simpa only [Real.log_exp] using comparison
  have logMagnitude : 1 ≤ |Real.log radius| := by
    rw [abs_of_nonpos (by linarith : Real.log radius ≤ 0)]
    linarith
  have profile := Real.rpow_le_rpow_of_exponent_le logMagnitude
    (sub_le_sub_left indexSmall.le 1)
  exact ⟨radius, positive, small.trans_le (min_le_left _ _),
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left profile lowerPositive.le)
      (sq_nonneg radius)).trans volumeLower⟩

end
end IGS.Sec31

#print axioms IGS.Sec31.ae_all_logarithmic_volume_lower
