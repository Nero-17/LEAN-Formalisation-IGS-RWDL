import RequestProject.Section31.CompactBallCoveringNumberMassBounds
import RequestProject.Section31.PositiveUniformSmallBallMassSubset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Real-valued standard covering numbers and quantitative power bounds
from uniform lower volume and almost-everywhere logarithmic upper volume. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology Metric Set
open scoped Classical NNReal
noncomputable section

def realCoveringNumber (Space : Type*) [MetricSpace Space] (radius : ℝ) : ℝ :=
  ((Metric.coveringNumber (Real.toNNReal radius) (Set.univ : Set Space)).toNat : ℝ)

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]

theorem compact_realCoveringNumber_upper_of_ball_mass_lower
    (physicalMeasure : Measure Space) [IsProbabilityMeasure physicalMeasure]
    (exponent massConstant radiusThreshold : ℝ)
    (massConstantPositive : 0 < massConstant) (radiusThresholdPositive : 0 < radiusThreshold)
    (ballMassLower : ∀ point : Space, ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
      massConstant * radius ^ exponent ≤ physicalMeasure.real (Metric.ball point radius)) :
    ∃ coefficient threshold : ℝ, 0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ,
      0 < radius → radius ≤ threshold → realCoveringNumber Space radius ≤ coefficient * radius ^ (-exponent) := by
  refine ⟨(2 : ℝ) ^ exponent / massConstant, 2 * radiusThreshold,
    div_pos (Real.rpow_pos_of_pos (by norm_num) _) massConstantPositive, by positivity, ?_⟩
  intro radius radiusPositive radiusSmall
  have halfPositive : 0 < radius / 2 := by positivity
  have halfSmall : radius / 2 ≤ radiusThreshold := by linarith
  have radiusNNPositive : 0 < Real.toNNReal radius := by
    exact_mod_cast (show (0 : ℝ) < (Real.toNNReal radius : ℝ) by
      rwa [Real.coe_toNNReal radius radiusPositive.le])
  have massPositive : 0 < massConstant * (radius / 2) ^ exponent :=
    mul_pos massConstantPositive (Real.rpow_pos_of_pos halfPositive _)
  have bound := compact_coveringNumber_mass_upper_bound physicalMeasure
    (Real.toNNReal radius) radiusNNPositive (massConstant * (radius / 2) ^ exponent)
    massPositive.le (fun point => by
      simpa only [Real.coe_toNNReal radius radiusPositive.le] using
        ballMassLower point (radius / 2) halfPositive halfSmall)
  change realCoveringNumber Space radius * (massConstant * (radius / 2) ^ exponent) ≤ _ at bound
  have normalized : realCoveringNumber Space radius * (massConstant * (radius / 2) ^ exponent) ≤ 1 := by
    simpa using bound
  calc
    realCoveringNumber Space radius ≤ 1 / (massConstant * (radius / 2) ^ exponent) :=
      (le_div_iff₀ massPositive).mpr normalized
    _ = ((2 : ℝ) ^ exponent / massConstant) * radius ^ (-exponent) := by
      rw [Real.div_rpow radiusPositive.le (by norm_num), Real.rpow_neg radiusPositive.le]
      field_simp [massConstantPositive.ne', (Real.rpow_pos_of_pos radiusPositive exponent).ne',
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) exponent).ne']
      <;> ring

theorem compact_realCoveringNumber_lower_of_ae_ball_mass_upper
    (physicalMeasure : Measure Space) [IsProbabilityMeasure physicalMeasure]
    (exponent logExponent : ℝ) (logExponentNonnegative : 0 ≤ logExponent)
    (ballMassUpper : ∀ᵐ point ∂physicalMeasure, ∃ coefficient threshold : ℝ,
      0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        physicalMeasure.real (Metric.ball point radius) ≤
          coefficient * (radius ^ exponent * |Real.log radius| ^ logExponent)) :
    ∃ coefficient threshold : ℝ, 0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ,
      0 < radius → radius ≤ threshold →
        coefficient * |Real.log radius| ^ (-logExponent) * radius ^ (-exponent) ≤
          realCoveringNumber Space radius := by
  obtain ⟨massConstant, radiusThreshold, massConstantPositive, radiusThresholdPositive, subsetPositive⟩ :=
    exists_positive_uniform_small_ball_mass_subset physicalMeasure
      (fun radius => radius ^ exponent * |Real.log radius| ^ logExponent)
      (fun radius positive => mul_nonneg (Real.rpow_nonneg positive.le _) (Real.rpow_nonneg (abs_nonneg _) _))
      ballMassUpper
  let subset := {point : Space | ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
    physicalMeasure.real (Metric.ball point radius) ≤
      massConstant * (radius ^ exponent * |Real.log radius| ^ logExponent)}
  have subsetRealPositive : 0 < physicalMeasure.real subset :=
    ENNReal.toReal_pos subsetPositive.ne' (measure_ne_top physicalMeasure subset)
  have constantPositive : 0 < massConstant * (3 : ℝ) ^ exponent :=
    mul_pos massConstantPositive (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨physicalMeasure.real subset / (massConstant * (3 : ℝ) ^ exponent),
    min (radiusThreshold / 3) (1 / 3), div_pos subsetRealPositive constantPositive,
      lt_min (by positivity) (by norm_num), ?_⟩
  intro radius radiusPositive radiusSmall
  have triplePositive : 0 < 3 * radius := by positivity
  have tripleSmall : 3 * radius ≤ radiusThreshold := by
    have := radiusSmall.trans (min_le_left _ _)
    linarith
  have radiusLessOne : radius < 1 := by
    have := radiusSmall.trans (min_le_right _ _)
    linarith
  have tripleAtMostOne : 3 * radius ≤ 1 := by
    have := radiusSmall.trans (min_le_right _ _)
    linarith
  have logRadiusNegative : Real.log radius < 0 := Real.log_neg radiusPositive radiusLessOne
  have logTripleNonpositive : Real.log (3 * radius) ≤ 0 :=
    Real.log_nonpos triplePositive.le tripleAtMostOne
  have logarithmBound : |Real.log (3 * radius)| ≤ |Real.log radius| := by
    rw [abs_of_nonpos logTripleNonpositive, abs_of_neg logRadiusNegative,
      Real.log_mul (by norm_num) radiusPositive.ne']
    have logThreePositive : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have boundPositive : 0 < (massConstant * (3 : ℝ) ^ exponent) * radius ^ exponent *
      |Real.log radius| ^ logExponent := by
    exact mul_pos (mul_pos constantPositive (Real.rpow_pos_of_pos radiusPositive _))
      (Real.rpow_pos_of_pos (abs_pos.mpr logRadiusNegative.ne) _)
  have uniformBound (point : Space) (membership : point ∈ subset) :
      physicalMeasure.real (Metric.ball point (3 * radius)) ≤
        (massConstant * (3 : ℝ) ^ exponent) * radius ^ exponent * |Real.log radius| ^ logExponent := by
    have actual := membership (3 * radius) triplePositive tripleSmall
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) radiusPositive.le] at actual
    have cost := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) logarithmBound logExponentNonnegative)
      (mul_pos (mul_pos massConstantPositive (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) exponent))
        (Real.rpow_pos_of_pos radiusPositive exponent)).le
    exact actual.trans (by convert cost using 1 <;> ring)
  have radiusNNPositive : 0 < Real.toNNReal radius := by
    exact_mod_cast (show (0 : ℝ) < (Real.toNNReal radius : ℝ) by
      rwa [Real.coe_toNNReal radius radiusPositive.le])
  have coverBound := compact_coveringNumber_mass_lower_bound physicalMeasure subset
    (Real.toNNReal radius) radiusNNPositive
    ((massConstant * (3 : ℝ) ^ exponent) * radius ^ exponent * |Real.log radius| ^ logExponent)
    boundPositive.le (fun point membership => by
      simpa only [Real.coe_toNNReal radius radiusPositive.le] using uniformBound point membership)
  change physicalMeasure.real subset ≤ realCoveringNumber Space radius *
    ((massConstant * (3 : ℝ) ^ exponent) * radius ^ exponent * |Real.log radius| ^ logExponent) at coverBound
  calc
    physicalMeasure.real subset / (massConstant * (3 : ℝ) ^ exponent) *
        |Real.log radius| ^ (-logExponent) * radius ^ (-exponent) =
        physicalMeasure.real subset /
          ((massConstant * (3 : ℝ) ^ exponent) * radius ^ exponent * |Real.log radius| ^ logExponent) := by
      rw [Real.rpow_neg (abs_nonneg _), Real.rpow_neg radiusPositive.le]
      field_simp [constantPositive.ne', (Real.rpow_pos_of_pos radiusPositive exponent).ne',
        (Real.rpow_pos_of_pos (abs_pos.mpr logRadiusNegative.ne) logExponent).ne']
      <;> ring
    _ ≤ realCoveringNumber Space radius := (div_le_iff₀ boundPositive).mpr coverBound

end
end IGS.Sec31

#print axioms IGS.Sec31.compact_realCoveringNumber_upper_of_ball_mass_lower
#print axioms IGS.Sec31.compact_realCoveringNumber_lower_of_ae_ball_mass_upper
