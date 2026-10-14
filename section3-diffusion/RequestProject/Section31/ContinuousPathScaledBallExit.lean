import RequestProject.Section31.ContinuousPathBallExit
import RequestProject.Section31.PositiveScaledMetric

/-! Exact first-exit identification under a positive scaling of distances.
The continuous path carrier is unchanged because its topology is preserved
definitionally. The distance formulas are never identified. Candidate source. -/

namespace IGS.Sec31
open Set
open scoped NNReal ENNReal Classical
noncomputable section

theorem continuousPathBallExit_positiveScaled_eq
    {Space : Type*} [original : MetricSpace Space]
    (scale : ℝ) (scalePositive : 0 < scale)
    (path : C(ℝ≥0, Space)) (center : Space) (radius : ℝ) :
    @continuousPathBallExit Space (EIGS.positiveScaledMetricSpace Space scale scalePositive)
      path center radius = continuousPathBallExit path center (radius / scale) := by
  have hittingSetEquality :
      {time : ℝ≥0 | radius ≤ scale * dist (path time) center} =
        {time : ℝ≥0 | radius / scale ≤ dist (path time) center} := by
    ext time
    simp only [mem_setOf_eq]
    rw [div_le_iff₀ scalePositive, mul_comm (dist (path time) center) scale]
  unfold continuousPathBallExit
  change (if reached : ({time : ℝ≥0 | radius ≤ scale * dist (path time) center}).Nonempty then
      ((sInf {time : ℝ≥0 | radius ≤ scale * dist (path time) center} : ℝ≥0) : ℝ≥0∞)
      else (⊤ : ℝ≥0∞)) = _
  rw [hittingSetEquality]

end
end IGS.Sec31

#print axioms IGS.Sec31.continuousPathBallExit_positiveScaled_eq
