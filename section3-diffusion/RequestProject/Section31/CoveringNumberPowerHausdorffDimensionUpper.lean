import RequestProject.Section31.CoveringNumberPowerHausdorffUpper

namespace IGS.Sec31
open MeasureTheory Filter Topology Set Metric
open scoped Classical ENNReal NNReal
noncomputable section
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

 theorem hausdorff_dimension_upper_of_coveringNumber_power_upper
    (dimension massConstant radiusThreshold : ℝ)
    (dimensionNonnegative : 0 ≤ dimension)
    (constantPositive : 0 < massConstant) (thresholdPositive : 0 < radiusThreshold)
    (coverUpper : ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
      realCoveringNumber Space radius ≤ massConstant * radius ^ (-dimension)) :
    dimH (Set.univ : Set Space) ≤ ENNReal.ofReal dimension := by
  apply dimH_le
  intro exponent infiniteMeasure
  by_contra notBounded
  have strictExponent : dimension < (exponent : ℝ) := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dimensionNonnegative).mp
    simpa only [ENNReal.ofReal_coe_nnreal] using lt_of_not_ge notBounded
  have zeroMeasure := hausdorffMeasure_zero_of_coveringNumber_power_upper
    (Space := Space) dimension (exponent : ℝ) massConstant radiusThreshold
    dimensionNonnegative strictExponent constantPositive thresholdPositive coverUpper
  exact ENNReal.zero_ne_top (zeroMeasure.symm.trans infiniteMeasure)

end
end IGS.Sec31

#print axioms IGS.Sec31.hausdorff_dimension_upper_of_coveringNumber_power_upper
