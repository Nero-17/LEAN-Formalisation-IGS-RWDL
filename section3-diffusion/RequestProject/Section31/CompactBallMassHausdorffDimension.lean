import RequestProject.Section31.CoveringNumberPowerHausdorffDimensionUpper
import RequestProject.Section31.AELogarithmicBallHausdorffLower

/-! Hausdorff dimension from uniform ball mass lower bounds and physical
almost-everywhere logarithmic upper bounds. No covering conclusion is input. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology Set
open scoped Classical ENNReal NNReal
noncomputable section
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

 theorem compact_hausdorff_dimension_eq_of_ball_mass_bounds
    (law : Measure Space) [IsProbabilityMeasure law]
    (dimension logExponent massConstant radiusThreshold : ℝ)
    (dimensionNonnegative : 0 ≤ dimension)
    (constantPositive : 0 < massConstant) (thresholdPositive : 0 < radiusThreshold)
    (ballLower : ∀ point : Space, ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
      massConstant * radius ^ dimension ≤ law.real (Metric.ball point radius))
    (almostEverywhere : ∀ᵐ point ∂law, ∃ coefficient threshold : ℝ,
      0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        law.real (Metric.ball point radius) ≤ coefficient * radius ^ dimension * |Real.log radius| ^ logExponent) :
    dimH (Set.univ : Set Space) = ENNReal.ofReal dimension := by
  obtain ⟨coefficient, threshold, coefficientPositive, thresholdPositive, coverUpper⟩ :=
    compact_realCoveringNumber_upper_of_ball_mass_lower law dimension massConstant radiusThreshold
      constantPositive thresholdPositive ballLower
  apply le_antisymm
  · exact hausdorff_dimension_upper_of_coveringNumber_power_upper dimension coefficient threshold
      dimensionNonnegative coefficientPositive thresholdPositive coverUpper
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro lowerExponent lowerPositive strictLower
    exact hausdorff_dimension_lower_of_ae_logarithmic_ball_upper law dimension logExponent
      lowerExponent lowerPositive (ENNReal.coe_lt_ofReal.mp strictLower) almostEverywhere

end
end IGS.Sec31

#print axioms IGS.Sec31.compact_hausdorff_dimension_eq_of_ball_mass_bounds
