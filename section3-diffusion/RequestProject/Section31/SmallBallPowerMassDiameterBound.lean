import RequestProject.Section31.SmallBallPowerMassNoAtoms
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-! Convert small-ball mass control on a subset into small-diameter outer
mass control, including zero-diameter sets. -/

namespace IGS.Sec31
open MeasureTheory Set
open scoped ENNReal
noncomputable section
variable {Space : Type*} [MetricSpace Space] [MeasurableSpace Space]

 theorem small_diameter_mass_bound_of_ball_power_upper
    (law : Measure Space) [IsFiniteMeasure law] (positiveSet : Set Space)
    (exponent massConstant radiusThreshold : ℝ)
    (exponentPositive : 0 < exponent) (constantPositive : 0 < massConstant)
    (thresholdPositive : 0 < radiusThreshold)
    (ballUpper : ∀ point ∈ positiveSet, ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
      law.real (Metric.ball point radius) ≤ massConstant * radius ^ exponent)
    (subset : Set Space) (smallDiameter : Metric.ediam subset ≤ ENNReal.ofReal (radiusThreshold / 2)) :
    law (subset ∩ positiveSet) ≤
      ENNReal.ofReal (massConstant * (2 : ℝ) ^ exponent) * Metric.ediam subset ^ exponent := by
  by_cases emptyIntersection : subset ∩ positiveSet = ∅
  · simp only [emptyIntersection, measure_empty, zero_le]
  obtain ⟨point, pointInSubset, pointInPositive⟩ := Set.nonempty_iff_ne_empty.mpr emptyIntersection
  have finiteDiameter : Metric.ediam subset ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top smallDiameter
  have diameterSmall : Metric.diam subset ≤ radiusThreshold / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) smallDiameter
  by_cases diameterZero : Metric.diam subset = 0
  · have containedSingleton : subset ∩ positiveSet ⊆ {point} := by
      intro other member
      apply Set.mem_singleton_iff.mpr
      apply dist_eq_zero.mp
      exact le_antisymm (by simpa only [diameterZero] using
        Metric.dist_le_diam_of_mem' finiteDiameter member.1 pointInSubset) dist_nonneg
    have singletonZero := singleton_mass_zero_of_small_ball_power_upper law point exponent massConstant
      radiusThreshold exponentPositive thresholdPositive (ballUpper point pointInPositive)
    exact (measure_mono containedSingleton).trans (by rw [singletonZero]; exact zero_le _)
  have diameterPositive : 0 < Metric.diam subset :=
    lt_of_le_of_ne Metric.diam_nonneg (fun equality => diameterZero equality.symm)
  have doubledSmall : 2 * Metric.diam subset ≤ radiusThreshold := by linarith
  have containedBall : subset ∩ positiveSet ⊆ Metric.ball point (2 * Metric.diam subset) := by
    intro other member
    exact lt_of_le_of_lt (Metric.dist_le_diam_of_mem' finiteDiameter member.1 pointInSubset)
      (by linarith)
  have realMassBound : law.real (subset ∩ positiveSet) ≤ massConstant * (2 * Metric.diam subset) ^ exponent :=
    (measureReal_mono containedBall).trans
      (ballUpper point pointInPositive _ (by positivity) doubledSmall)
  calc
    law (subset ∩ positiveSet) = ENNReal.ofReal (law.real (subset ∩ positiveSet)) :=
      (ENNReal.ofReal_toReal (measure_ne_top law _)).symm
    _ ≤ ENNReal.ofReal (massConstant * (2 * Metric.diam subset) ^ exponent) :=
      ENNReal.ofReal_le_ofReal realMassBound
    _ = ENNReal.ofReal (massConstant * (2 : ℝ) ^ exponent) * Metric.ediam subset ^ exponent := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) Metric.diam_nonneg, ← mul_assoc,
        ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg Metric.diam_nonneg exponentPositive.le]
      change _ * (ENNReal.ofReal (Metric.ediam subset).toReal) ^ exponent = _
      rw [ENNReal.ofReal_toReal finiteDiameter]

end
end IGS.Sec31

#print axioms IGS.Sec31.small_diameter_mass_bound_of_ball_power_upper
