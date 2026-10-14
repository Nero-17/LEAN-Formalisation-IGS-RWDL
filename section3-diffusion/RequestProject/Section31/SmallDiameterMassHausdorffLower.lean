import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! An outer-mass distribution principle. The positive subset need not be
measurable; diameter control applies directly to its outer restriction. -/

namespace IGS.Sec31
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
variable {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]

 theorem hausdorff_dimension_lower_of_small_diameter_mass
    (law : Measure Space) (positiveSet : Set Space)
    (exponent : ℝ≥0) (massConstant : ℝ≥0) (radiusThreshold : ℝ≥0∞)
    (constantNonzero : massConstant ≠ 0) (thresholdPositive : 0 < radiusThreshold)
    (positiveMass : law positiveSet ≠ 0)
    (smallSetBound : ∀ subset : Set Space, Metric.ediam subset ≤ radiusThreshold →
      law (subset ∩ positiveSet) ≤ massConstant * Metric.ediam subset ^ (exponent : ℝ)) :
    (exponent : ℝ≥0∞) ≤ dimH (Set.univ : Set Space) := by
  have comparison :
      OuterMeasure.restrict positiveSet law.toOuterMeasure ≤
        OuterMeasure.mkMetric ((massConstant : ℝ≥0∞) •
          (fun radius : ℝ≥0∞ => radius ^ (exponent : ℝ))) := by
    apply OuterMeasure.le_mkMetric _ _ radiusThreshold thresholdPositive
    intro subset small
    simpa only [OuterMeasure.restrict_apply, Measure.coe_toOuterMeasure, Pi.smul_apply,
      smul_eq_mul] using smallSetBound subset small
  rw [OuterMeasure.mkMetric_smul _ ENNReal.coe_ne_top
    (ENNReal.coe_ne_zero.mpr constantNonzero)] at comparison
  have fullBound := comparison (Set.univ : Set Space)
  have hausdorffPositive : Measure.hausdorffMeasure (exponent : ℝ) (Set.univ : Set Space) ≠ 0 := by
    intro zeroMeasure
    change (Measure.mkMetric (fun radius : ℝ≥0∞ => radius ^ (exponent : ℝ)))
      (Set.univ : Set Space) = 0 at zeroMeasure
    have zeroMass : law positiveSet ≤ 0 := by
      simpa only [OuterMeasure.restrict_apply, Set.univ_inter, Measure.coe_toOuterMeasure,
        OuterMeasure.smul_apply, smul_eq_mul, OuterMeasure.coe_mkMetric,
        zeroMeasure, mul_zero] using fullBound
    exact positiveMass (le_antisymm zeroMass bot_le)
  exact le_dimH_of_hausdorffMeasure_ne_zero hausdorffPositive

end
end IGS.Sec31

#print axioms IGS.Sec31.hausdorff_dimension_lower_of_small_diameter_mass
