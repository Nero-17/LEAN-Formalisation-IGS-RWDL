import RequestProject.Section31.CoarseModulusScaleSequences

/-! Rescale the numerical windows by the actual positive clock fraction.
The double-window factor, grid cardinality, and fixed floor-clock correction
are all retained. This is numerical input for the actual process consumer. -/

namespace IGS.Sec31

open Filter
open scoped Topology
noncomputable section

theorem exists_nativeModulusWindows
    {scale distanceRate timeRate contraction horizon fraction factor : ℝ}
    (scalePositive : 0 < scale) (rateGeTwo : 2 ≤ distanceRate)
    (timeGeSquare : distanceRate ^ 2 ≤ timeRate)
    (contractionNonnegative : 0 ≤ contraction) (contractionLessOne : contraction < 1)
    (horizonNonnegative : 0 ≤ horizon) (fractionPositive : 0 < fraction) :
    ∃ coefficient enlargedContraction : ℝ,
      0 < coefficient ∧ contraction ≤ enlargedContraction ∧
      0 < enlargedContraction ∧ enlargedContraction < 1 ∧
      (∀ level, 0 < fraction / 2 *
        coarseModulusWindow scale distanceRate timeRate coefficient level) ∧
      Tendsto (fun level => fraction / 2 *
        coarseModulusWindow scale distanceRate timeRate coefficient level) atTop (𝓝 0) ∧
      Tendsto (fun level =>
        (horizon / (fraction / 2 * coarseModulusWindow scale distanceRate timeRate coefficient level) + 1) *
          (factor * Real.exp (2 * (fraction / 2 *
            coarseModulusWindow scale distanceRate timeRate coefficient level) /
              (fraction * timeRate⁻¹ ^ level)) *
            enlargedContraction ^ coarseModulusCrossings scale distanceRate level))
        atTop (𝓝 0) := by
  have enlargedPositive : 0 < (1 + contraction) / 2 := by linarith
  have enlargedLessOne : (1 + contraction) / 2 < 1 := by linarith
  obtain ⟨coefficient, coefficientPositive, windowsPositive, windowsLimit, tailLimit⟩ :=
    exists_coarseModulusWindows (horizon := 2 * horizon / fraction)
      scalePositive rateGeTwo timeGeSquare enlargedPositive enlargedLessOne (by positivity)
  refine ⟨coefficient, (1 + contraction) / 2, coefficientPositive, by linarith,
    enlargedPositive, enlargedLessOne, ?_, ?_, ?_⟩
  · intro level
    exact mul_pos (by positivity) (windowsPositive level)
  · simpa using windowsLimit.const_mul (fraction / 2)
  · have result := tailLimit.const_mul factor
    have distancePositive : 0 < distanceRate := by linarith
    have timePositive : 0 < timeRate := by nlinarith
    have expressionsEqual : (fun level : ℕ =>
        (horizon / (fraction / 2 * coarseModulusWindow scale distanceRate timeRate coefficient level) + 1) *
          (factor * Real.exp (2 * (fraction / 2 *
            coarseModulusWindow scale distanceRate timeRate coefficient level) /
              (fraction * timeRate⁻¹ ^ level)) *
            ((1 + contraction) / 2) ^ coarseModulusCrossings scale distanceRate level)) =
        (fun level : ℕ => factor *
          ((2 * horizon / fraction / coarseModulusWindow scale distanceRate timeRate coefficient level + 1) *
            Real.exp (coarseModulusWindow scale distanceRate timeRate coefficient level / timeRate⁻¹ ^ level) *
              ((1 + contraction) / 2) ^ coarseModulusCrossings scale distanceRate level)) := by
      funext level
      have exponentEquality : 2 * (fraction / 2 *
          coarseModulusWindow scale distanceRate timeRate coefficient level) /
            (fraction * timeRate⁻¹ ^ level) =
          coarseModulusWindow scale distanceRate timeRate coefficient level / timeRate⁻¹ ^ level := by
        field_simp [fractionPositive.ne']
      have gridEquality : horizon / (fraction / 2 *
          coarseModulusWindow scale distanceRate timeRate coefficient level) =
          2 * horizon / fraction / coarseModulusWindow scale distanceRate timeRate coefficient level := by
        field_simp [fractionPositive.ne', (windowsPositive level).ne']
        <;> ring
      rw [exponentEquality, gridEquality]
      ring
    rw [expressionsEqual]
    simpa using result

end
end IGS.Sec31

#print axioms IGS.Sec31.exists_nativeModulusWindows
