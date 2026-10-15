import RequestProject.Section31.GeometricInverseBallLowerOptimization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Pure-power diagonal bounds from the same inverse-ball kernel estimate.
The actual bounded-degree driver must supply the ball mass bound from the
literal rule graph. No logarithmic degree expression is evaluated at rate1. -/
namespace IGS.Sec31
open MeasureTheory Metric
open scoped NNReal
noncomputable section

theorem ball_mass_power_upper_all_radii_of_local
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space]
    (law : Measure Space) [IsFiniteMeasure law]
    (volumeConstant volumeRadius dimension : ℝ)
    (volumeConstantPositive : 0 < volumeConstant)
    (volumeRadiusPositive : 0 < volumeRadius) (dimensionNonnegative : 0 ≤ dimension)
    (localVolume : ∀ point : Space, ∀ radius : ℝ, 0 < radius → radius ≤ volumeRadius →
      law.real (ball point radius) ≤ volumeConstant * radius ^ dimension) :
    ∃ globalConstant : ℝ, 0 < globalConstant ∧ ∀ point : Space, ∀ radius : ℝ,
      0 < radius → law.real (ball point radius) ≤ globalConstant * radius ^ dimension := by
  let globalConstant := volumeConstant + law.real Set.univ / volumeRadius ^ dimension
  have radiusPowerPositive : 0 < volumeRadius ^ dimension :=
    Real.rpow_pos_of_pos volumeRadiusPositive dimension
  have totalNonnegative : 0 ≤ law.real Set.univ := ENNReal.toReal_nonneg
  have extraNonnegative : 0 ≤ law.real Set.univ / volumeRadius ^ dimension :=
    div_nonneg totalNonnegative radiusPowerPositive.le
  refine ⟨globalConstant, by dsimp only [globalConstant]; linarith, ?_⟩
  intro point radius radiusPositive
  by_cases radiusSmall : radius ≤ volumeRadius
  · exact (localVolume point radius radiusPositive radiusSmall).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [globalConstant]; linarith)
        (Real.rpow_nonneg radiusPositive.le dimension))
  · have radiusOrder : volumeRadius ≤ radius := (lt_of_not_ge radiusSmall).le
    have powerOrder := Real.rpow_le_rpow volumeRadiusPositive.le radiusOrder dimensionNonnegative
    have totalBound : law.real Set.univ ≤
        (law.real Set.univ / volumeRadius ^ dimension) * radius ^ dimension := by
      calc
        law.real Set.univ = (law.real Set.univ / volumeRadius ^ dimension) *
            volumeRadius ^ dimension := by field_simp [radiusPowerPositive.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left powerOrder extraNonnegative
    exact (measureReal_mono (Set.subset_univ _)).trans
      (totalBound.trans (mul_le_mul_of_nonneg_right
        (by dsimp only [globalConstant]; linarith)
        (Real.rpow_nonneg radiusPositive.le dimension)))

theorem diagonal_power_lower_of_inverse_ball_and_volume_upper
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (law : Measure Space) [IsFiniteMeasure law] [law.IsOpenPosMeasure]
    (volumeConstant radiusConstant coefficient radiusExponent dimension heatExponent cutoffTime : ℝ)
    (volumeConstantPositive : 0 < volumeConstant)
    (radiusConstantPositive : 0 < radiusConstant) (coefficientPositive : 0 < coefficient)
    (exponentIdentity : radiusExponent * dimension = heatExponent)
    (volumeUpper : ∀ point : Space, ∀ radius : ℝ, 0 < radius →
      law.real (ball point radius) ≤ volumeConstant * radius ^ dimension)
    (diagonal : {time : ℝ≥0 // 0 < time} → Space → ℝ)
    (inverseLower : ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime →
      ∀ point, coefficient / law.real
        (ball point (radiusConstant * (time.val : ℝ) ^ radiusExponent)) ≤ diagonal time point) :
    ∃ lowerConstant : ℝ, 0 < lowerConstant ∧
      ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime → ∀ point,
      lowerConstant / (time.val : ℝ) ^ heatExponent ≤ diagonal time point := by
  let lowerConstant := coefficient / (volumeConstant * radiusConstant ^ dimension)
  have constantPowerPositive : 0 < radiusConstant ^ dimension :=
    Real.rpow_pos_of_pos radiusConstantPositive dimension
  refine ⟨lowerConstant, div_pos coefficientPositive
    (mul_pos volumeConstantPositive constantPowerPositive), ?_⟩
  intro time timeSmall point
  have timePositive : 0 < (time.val : ℝ) := time.property
  have radiusPositive : 0 < radiusConstant * (time.val : ℝ) ^ radiusExponent :=
    mul_pos radiusConstantPositive (Real.rpow_pos_of_pos timePositive radiusExponent)
  have ballMassPositive : 0 < law.real
      (ball point (radiusConstant * (time.val : ℝ) ^ radiusExponent)) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos law point radiusPositive).ne' (measure_ne_top law _)
  have volumeBound := volumeUpper point _ radiusPositive
  have radiusPowerIdentity :
      (radiusConstant * (time.val : ℝ) ^ radiusExponent) ^ dimension =
        radiusConstant ^ dimension * (time.val : ℝ) ^ heatExponent := by
    rw [Real.mul_rpow radiusConstantPositive.le (Real.rpow_nonneg timePositive.le _),
      ← Real.rpow_mul timePositive.le, exponentIdentity]
  rw [radiusPowerIdentity] at volumeBound
  have lowerComparison := div_le_div_of_nonneg_left coefficientPositive.le ballMassPositive volumeBound
  have divisionIdentity : lowerConstant / (time.val : ℝ) ^ heatExponent =
      coefficient / (volumeConstant * (radiusConstant ^ dimension *
        (time.val : ℝ) ^ heatExponent)) := by
    dsimp only [lowerConstant]
    rw [div_div]
    congr 1
    ring
  rw [divisionIdentity]
  exact lowerComparison.trans (inverseLower time timeSmall point)

theorem diagonal_power_two_sided_of_inverse_ball_and_volume_upper
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (law : Measure Space) [IsFiniteMeasure law] [law.IsOpenPosMeasure]
    (volumeConstant radiusConstant coefficient radiusExponent dimension heatExponent
      lowerCutoff upperCutoff upperConstant : ℝ)
    (volumeConstantPositive : 0 < volumeConstant)
    (radiusConstantPositive : 0 < radiusConstant) (coefficientPositive : 0 < coefficient)
    (lowerCutoffPositive : 0 < lowerCutoff) (upperCutoffPositive : 0 < upperCutoff)
    (upperConstantPositive : 0 < upperConstant)
    (exponentIdentity : radiusExponent * dimension = heatExponent)
    (volumeUpper : ∀ point : Space, ∀ radius : ℝ, 0 < radius →
      law.real (ball point radius) ≤ volumeConstant * radius ^ dimension)
    (diagonal : {time : ℝ≥0 // 0 < time} → Space → ℝ)
    (inverseLower : ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ lowerCutoff →
      ∀ point, coefficient / law.real
        (ball point (radiusConstant * (time.val : ℝ) ^ radiusExponent)) ≤ diagonal time point)
    (diagonalUpper : ∀ time : {time : ℝ≥0 // 0 < time}, ∀ point,
      diagonal time point ≤ upperConstant /
        (min ((time.val : ℝ) / 2) upperCutoff) ^ heatExponent) :
    ∃ cutoffTime lowerConstant upperPowerConstant : ℝ,
      0 < cutoffTime ∧ 0 < lowerConstant ∧ 0 < upperPowerConstant ∧
      ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime → ∀ point,
      lowerConstant / (time.val : ℝ) ^ heatExponent ≤ diagonal time point ∧
      diagonal time point ≤ upperPowerConstant / (time.val : ℝ) ^ heatExponent := by
  obtain ⟨lowerConstant, lowerPositive, powerLower⟩ :=
    diagonal_power_lower_of_inverse_ball_and_volume_upper law volumeConstant radiusConstant coefficient
      radiusExponent dimension heatExponent lowerCutoff volumeConstantPositive radiusConstantPositive
      coefficientPositive exponentIdentity volumeUpper diagonal inverseLower
  refine ⟨min lowerCutoff (2 * upperCutoff), lowerConstant,
    upperConstant * (2 : ℝ) ^ heatExponent,
    lt_min lowerCutoffPositive (mul_pos (by norm_num) upperCutoffPositive), lowerPositive,
    mul_pos upperConstantPositive (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro time timeSmall point
  refine ⟨powerLower time (timeSmall.trans (min_le_left _ _)) point, ?_⟩
  have timePositive : 0 < (time.val : ℝ) := time.property
  have halfSmall : (time.val : ℝ) / 2 ≤ upperCutoff := by
    linarith [timeSmall.trans (min_le_right _ _)]
  have upper := diagonalUpper time point
  rw [min_eq_left halfSmall, Real.div_rpow timePositive.le (by norm_num : (0 : ℝ) ≤ 2)] at upper
  have timePowerPositive : 0 < (time.val : ℝ) ^ heatExponent :=
    Real.rpow_pos_of_pos timePositive _
  have twoPowerPositive : 0 < (2 : ℝ) ^ heatExponent :=
    Real.rpow_pos_of_pos (by norm_num) _
  convert upper using 1 <;> field_simp [timePowerPositive.ne', twoPowerPositive.ne'] <;> ring

end
end IGS.Sec31

#print axioms IGS.Sec31.ball_mass_power_upper_all_radii_of_local
#print axioms IGS.Sec31.diagonal_power_lower_of_inverse_ball_and_volume_upper
#print axioms IGS.Sec31.diagonal_power_two_sided_of_inverse_ball_and_volume_upper
