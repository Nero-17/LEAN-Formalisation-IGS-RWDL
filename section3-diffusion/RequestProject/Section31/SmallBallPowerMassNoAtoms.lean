import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Positive local ball exponents exclude atoms at the corresponding point. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology
noncomputable section
variable {Space : Type*} [MetricSpace Space] [MeasurableSpace Space]

 theorem singleton_mass_zero_of_small_ball_power_upper
    (law : Measure Space) [IsFiniteMeasure law] (point : Space)
    (exponent massConstant radiusThreshold : ℝ)
    (exponentPositive : 0 < exponent) (thresholdPositive : 0 < radiusThreshold)
    (ballUpper : ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
      law.real (Metric.ball point radius) ≤ massConstant * radius ^ exponent) :
    law {point} = 0 := by
  have powerLimit : Tendsto (fun radius : ℝ => massConstant * radius ^ exponent)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.zero_rpow exponentPositive.ne', mul_zero] using
      ((((Real.continuousAt_rpow_const (0 : ℝ) exponent (Or.inr exponentPositive.le)).tendsto).mono_left
        nhdsWithin_le_nhds).const_mul massConstant)
  have singletonRealZero : law.real {point} = 0 := by
    apply le_antisymm _ (measureReal_nonneg)
    apply ge_of_tendsto powerLimit
    filter_upwards [Ioc_mem_nhdsGT thresholdPositive] with radius radiusInRange
    exact (measureReal_mono (show ({point} : Set Space) ⊆ Metric.ball point radius by
      intro other member
      rw [Set.mem_singleton_iff] at member
      subst other
      simpa only [Metric.mem_ball, dist_self] using radiusInRange.1)).trans
        (ballUpper radius radiusInRange.1 radiusInRange.2)
  by_contra singletonNonzero
  have singletonPositive := ENNReal.toReal_pos singletonNonzero (measure_ne_top law {point})
  change (law {point}).toReal = 0 at singletonRealZero
  exact (ne_of_gt singletonPositive) singletonRealZero

end
end IGS.Sec31

#print axioms IGS.Sec31.singleton_mass_zero_of_small_ball_power_upper
