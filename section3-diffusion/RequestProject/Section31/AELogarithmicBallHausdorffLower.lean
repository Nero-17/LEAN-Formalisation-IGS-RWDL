import RequestProject.Section31.SmallBallPowerHausdorffLower
import RequestProject.Section31.PositiveUniformSmallBallMassSubset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! An almost-everywhere logarithmic ball upper estimate gives every
strictly smaller positive Hausdorff dimension lower bound. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Classical
noncomputable section
variable {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]

 theorem hausdorff_dimension_lower_of_ae_logarithmic_ball_upper
    (law : Measure Space) [IsProbabilityMeasure law]
    (dimension logExponent : ℝ) (lowerExponent : ℝ≥0)
    (lowerPositive : 0 < lowerExponent) (strictLower : (lowerExponent : ℝ) < dimension)
    (almostEverywhere : ∀ᵐ point ∂law, ∃ coefficient threshold : ℝ,
      0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        law.real (Metric.ball point radius) ≤
          coefficient * radius ^ dimension * |Real.log radius| ^ logExponent) :
    (lowerExponent : ℝ≥0∞) ≤ dimH (Set.univ : Set Space) := by
  have logarithmDominated : ∀ᶠ radius : ℝ in 𝓝[>] 0,
      |Real.log radius| ^ logExponent ≤ radius ^ ((lowerExponent : ℝ) - dimension) := by
    have comparison := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero logExponent
      (sub_neg.mpr strictLower)).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [comparison, self_mem_nhdsWithin] with radius bound radiusPositive
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (Real.rpow_nonneg radiusPositive.le _), one_mul] using bound
  obtain ⟨logThreshold, logThresholdPositive, dominated⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp logarithmDominated
  have powerAlmostEverywhere : ∀ᵐ point ∂law, ∃ coefficient threshold : ℝ,
      0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        law.real (Metric.ball point radius) ≤ coefficient * radius ^ (lowerExponent : ℝ) := by
    filter_upwards [almostEverywhere] with point property
    obtain ⟨coefficient, threshold, coefficientPositive, thresholdPositive, bound⟩ := property
    refine ⟨coefficient, min threshold logThreshold, coefficientPositive,
      lt_min thresholdPositive logThresholdPositive, ?_⟩
    intro radius radiusPositive radiusSmall
    calc
      law.real (Metric.ball point radius) ≤
          coefficient * radius ^ dimension * |Real.log radius| ^ logExponent :=
        bound radius radiusPositive (radiusSmall.trans (min_le_left _ _))
      _ ≤ coefficient * radius ^ dimension * radius ^ ((lowerExponent : ℝ) - dimension) :=
        mul_le_mul_of_nonneg_left (dominated ⟨radiusPositive, radiusSmall.trans (min_le_right _ _)⟩)
          (mul_nonneg coefficientPositive.le (Real.rpow_nonneg radiusPositive.le _))
      _ = coefficient * radius ^ (lowerExponent : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add radiusPositive]
        congr 2
        ring
  obtain ⟨coefficient, threshold, coefficientPositive, thresholdPositive, positiveMass⟩ :=
    exists_positive_uniform_small_ball_mass_subset law
      (fun radius : ℝ => radius ^ (lowerExponent : ℝ))
      (fun radius positive => Real.rpow_nonneg positive.le _) powerAlmostEverywhere
  exact hausdorff_dimension_lower_of_small_ball_power_upper law _ lowerExponent coefficient threshold
    lowerPositive coefficientPositive thresholdPositive (ne_of_gt positiveMass)
    (fun point membership => membership)

end
end IGS.Sec31

#print axioms IGS.Sec31.hausdorff_dimension_lower_of_ae_logarithmic_ball_upper
