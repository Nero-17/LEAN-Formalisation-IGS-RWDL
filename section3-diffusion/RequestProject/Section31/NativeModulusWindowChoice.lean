import RequestProject.Section31.NativeModulusScaleSequences
import RequestProject.Section31.CoarseModulusSpatialThreshold

/-! Simultaneously choose the coarse level, integer crossing threshold and
physical time window. The exact finite grid bound is made arbitrarily small,
and its spatial threshold is below the requested modulus tolerance. -/

namespace IGS.Sec31

open Filter
open scoped Topology
noncomputable section

theorem exists_nativeModulusWindowChoice
    {distanceRate timeRate contraction horizon fraction factor spatialConstant
      tolerance probabilityTolerance maximumWindow : ℝ}
    (rateGeTwo : 2 ≤ distanceRate) (timeGeSquare : distanceRate ^ 2 ≤ timeRate)
    (contractionNonnegative : 0 ≤ contraction) (contractionLessOne : contraction < 1)
    (horizonNonnegative : 0 ≤ horizon) (fractionPositive : 0 < fraction)
    (factorNonnegative : 0 ≤ factor) (spatialPositive : 0 < spatialConstant)
    (tolerancePositive : 0 < tolerance) (probabilityPositive : 0 < probabilityTolerance)
    (maximumWindowPositive : 0 < maximumWindow) :
    ∃ (coarse count : ℕ) (window : ℝ), 0 < window ∧ window < maximumWindow ∧
      2 * ((count + 2 : ℝ) * (spatialConstant * distanceRate⁻¹ ^ coarse)) < tolerance ∧
      ((⌊horizon / window⌋₊ : ℝ) + 1) * factor *
        Real.exp (2 * window / (fraction * timeRate⁻¹ ^ coarse)) * contraction ^ count <
          probabilityTolerance := by
  have scalePositive : 0 < tolerance / (4 * spatialConstant) := by positivity
  obtain ⟨coefficient, enlarged, coefficientPositive, contractionLe, enlargedPositive,
      enlargedLessOne, windowsPositive, windowsLimit, tailLimit⟩ :=
    exists_nativeModulusWindows (factor := factor) scalePositive rateGeTwo timeGeSquare
      contractionNonnegative contractionLessOne horizonNonnegative fractionPositive
  have spatialLimit := coarseModulusSpatialThreshold_eventually_lt
    (scale := tolerance / (4 * spatialConstant)) (tolerance := tolerance / 2)
    scalePositive rateGeTwo spatialPositive (by
      have cancellation : spatialConstant * (tolerance / (4 * spatialConstant)) = tolerance / 4 := by
        field_simp [spatialPositive.ne']
      rw [cancellation]
      linarith)
  have windowSmall := windowsLimit.eventually (gt_mem_nhds maximumWindowPositive)
  have tailSmall := tailLimit.eventually (gt_mem_nhds probabilityPositive)
  obtain ⟨coarse, spatialBound, windowBound, probabilityBound⟩ :=
    (spatialLimit.and (windowSmall.and tailSmall)).exists
  refine ⟨coarse, coarseModulusCrossings (tolerance / (4 * spatialConstant)) distanceRate coarse,
    fraction / 2 * coarseModulusWindow (tolerance / (4 * spatialConstant)) distanceRate
      timeRate coefficient coarse, windowsPositive coarse, windowBound, ?_, ?_⟩
  · nlinarith [spatialBound]
  · let window := fraction / 2 * coarseModulusWindow (tolerance / (4 * spatialConstant))
      distanceRate timeRate coefficient coarse
    have windowPositive : 0 < window := windowsPositive coarse
    have gridBound : (⌊horizon / window⌋₊ : ℝ) + 1 ≤ horizon / window + 1 := by
      have floorBound := Nat.floor_le (div_nonneg horizonNonnegative windowPositive.le)
      linarith
    have powerBound := pow_le_pow_left₀ contractionNonnegative contractionLe
      (coarseModulusCrossings (tolerance / (4 * spatialConstant)) distanceRate coarse)
    have tailBound : ((⌊horizon / window⌋₊ : ℝ) + 1) * factor *
        Real.exp (2 * window / (fraction * timeRate⁻¹ ^ coarse)) *
          contraction ^ coarseModulusCrossings (tolerance / (4 * spatialConstant)) distanceRate coarse ≤
        (horizon / window + 1) * (factor *
          Real.exp (2 * window / (fraction * timeRate⁻¹ ^ coarse)) *
            enlarged ^ coarseModulusCrossings (tolerance / (4 * spatialConstant)) distanceRate coarse) := by
      calc
        _ ≤ ((horizon / window + 1) * factor *
            Real.exp (2 * window / (fraction * timeRate⁻¹ ^ coarse))) *
              enlarged ^ coarseModulusCrossings (tolerance / (4 * spatialConstant)) distanceRate coarse := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right gridBound factorNonnegative) (Real.exp_pos _).le
          · exact powerBound
          · exact pow_nonneg contractionNonnegative _
          · positivity
        _ = _ := by ring
    exact tailBound.trans_lt probabilityBound

end
end IGS.Sec31

#print axioms IGS.Sec31.exists_nativeModulusWindowChoice
