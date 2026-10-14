import RequestProject.Section31.SmallDiameterMassHausdorffLower
import RequestProject.Section31.SmallBallPowerMassDiameterBound

/-! A positive outer-mass subset with a uniform ball power upper bound
supplies the corresponding Hausdorff dimension lower bound. -/

namespace IGS.Sec31
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
variable {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]

 theorem hausdorff_dimension_lower_of_small_ball_power_upper
    (law : Measure Space) [IsFiniteMeasure law] (positiveSet : Set Space)
    (exponent : ℝ≥0) (massConstant radiusThreshold : ℝ)
    (exponentPositive : 0 < exponent) (constantPositive : 0 < massConstant)
    (thresholdPositive : 0 < radiusThreshold) (positiveMass : law positiveSet ≠ 0)
    (ballUpper : ∀ point ∈ positiveSet, ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
      law.real (Metric.ball point radius) ≤ massConstant * radius ^ (exponent : ℝ)) :
    (exponent : ℝ≥0∞) ≤ dimH (Set.univ : Set Space) := by
  apply hausdorff_dimension_lower_of_small_diameter_mass law positiveSet exponent
    (Real.toNNReal (massConstant * (2 : ℝ) ^ (exponent : ℝ)))
    (ENNReal.ofReal (radiusThreshold / 2))
    (ne_of_gt (Real.toNNReal_pos.mpr (mul_pos constantPositive
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _))))
    (ENNReal.ofReal_pos.mpr (div_pos thresholdPositive (by norm_num))) positiveMass
  intro subset smallDiameter
  simpa only [ENNReal.ofReal] using
    small_diameter_mass_bound_of_ball_power_upper law positiveSet (exponent : ℝ) massConstant
      radiusThreshold (by exact_mod_cast exponentPositive) constantPositive thresholdPositive
      ballUpper subset smallDiameter

end
end IGS.Sec31

#print axioms IGS.Sec31.hausdorff_dimension_lower_of_small_ball_power_upper
