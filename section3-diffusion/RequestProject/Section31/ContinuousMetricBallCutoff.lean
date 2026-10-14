import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A continuous unit-range test equal to one on a closed inner ball and
zero outside the doubled ball. This test uses only the metric, and imposes
no form-energy or point-evaluation assumption. Candidate source. -/

namespace IGS.Sec31
open scoped Topology
noncomputable section
variable {Space : Type*} [MetricSpace Space]

def continuousMetricBallCutoff (center : Space) (radius : ℝ) : C(Space, ℝ) where
  toFun point := max 0 (min 1 (2 - dist point center / radius))
  continuous_toFun := continuous_const.max
    (continuous_const.min (continuous_const.sub ((continuous_id.dist continuous_const).div_const radius)))

theorem continuousMetricBallCutoff_bounds (center point : Space) (radius : ℝ) :
    0 ≤ continuousMetricBallCutoff center radius point ∧
      continuousMetricBallCutoff center radius point ≤ 1 := by
  change 0 ≤ max 0 (min 1 _) ∧ max 0 (min 1 _) ≤ 1
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem continuousMetricBallCutoff_eq_one (center point : Space) (radius : ℝ)
    (radiusPositive : 0 < radius) (inside : point ∈ Metric.closedBall center radius) :
    continuousMetricBallCutoff center radius point = 1 := by
  have distanceBound : dist point center ≤ radius := Metric.mem_closedBall.mp inside
  have quotientBound := (div_le_one radiusPositive).mpr distanceBound
  change max 0 (min 1 (2 - dist point center / radius)) = 1
  rw [min_eq_left (by linarith), max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem continuousMetricBallCutoff_eq_zero_outside (center point : Space) (radius : ℝ)
    (radiusPositive : 0 < radius) (outside : point ∉ Metric.closedBall center (2 * radius)) :
    continuousMetricBallCutoff center radius point = 0 := by
  have distanceBound : 2 * radius < dist point center := by
    simpa only [Metric.mem_closedBall, not_le] using outside
  have quotientBound : 2 < dist point center / radius := (lt_div_iff₀ radiusPositive).mpr distanceBound
  have nonpositive : min 1 (2 - dist point center / radius) ≤ 0 :=
    (min_le_right _ _).trans (by linarith)
  exact max_eq_left nonpositive

end
end IGS.Sec31

#print axioms IGS.Sec31.continuousMetricBallCutoff_bounds
#print axioms IGS.Sec31.continuousMetricBallCutoff_eq_one
#print axioms IGS.Sec31.continuousMetricBallCutoff_eq_zero_outside
