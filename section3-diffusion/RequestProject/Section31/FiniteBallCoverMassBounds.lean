import RequestProject.Section31.MetricBallMassMeasurable
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-! Quantitative mass bounds for actual finite metric covers and packings.
The lower-cover argument only assumes an upper ball mass on a positive-mass
subset, allowing the nonuniform typical-point estimates to be used later. -/

namespace IGS.Sec31
open MeasureTheory Set Metric
open scoped Classical BigOperators
noncomputable section

variable {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]

theorem real_measure_le_finite_ball_cover_card_mul (physicalMeasure : Measure Space)
    [IsFiniteMeasure physicalMeasure] (subset : Set Space) (centers : Finset Space)
    (radius bound : ℝ) (radiusPositive : 0 < radius) (boundNonnegative : 0 ≤ bound)
    (cover : ∀ point ∈ subset, ∃ center ∈ centers, dist point center ≤ radius)
    (ballMassUpper : ∀ point ∈ subset, physicalMeasure.real (Metric.ball point (3 * radius)) ≤ bound) :
    physicalMeasure.real subset ≤ (centers.card : ℝ) * bound := by
  have pieceBound (center : Space) :
      physicalMeasure.real (subset ∩ Metric.closedBall center radius) ≤ bound := by
    by_cases nonempty : (subset ∩ Metric.closedBall center radius).Nonempty
    · obtain ⟨reference, referenceInSubset, referenceInBall⟩ := nonempty
      have inside : subset ∩ Metric.closedBall center radius ⊆ Metric.ball reference (3 * radius) := by
        intro point membership
        have pointNear : dist point center ≤ radius := membership.2
        have referenceNear : dist center reference ≤ radius := by
          simpa only [Metric.mem_closedBall, dist_comm] using referenceInBall
        have triangle := dist_triangle point center reference
        change dist point reference < 3 * radius
        linarith
      exact (measureReal_mono inside).trans (ballMassUpper reference referenceInSubset)
    · have empty : subset ∩ Metric.closedBall center radius = ∅ := Set.not_nonempty_iff_eq_empty.mp nonempty
      simpa only [empty, measureReal_empty] using boundNonnegative
  have covered : subset ⊆ ⋃ center ∈ centers, subset ∩ Metric.closedBall center radius := by
    intro point membership
    obtain ⟨center, centerIn, near⟩ := cover point membership
    exact Set.mem_iUnion.mpr ⟨center, Set.mem_iUnion.mpr ⟨centerIn, membership, near⟩⟩
  calc
    physicalMeasure.real subset ≤
        physicalMeasure.real (⋃ center ∈ centers, subset ∩ Metric.closedBall center radius) :=
      measureReal_mono covered
    _ ≤ ∑ center ∈ centers, physicalMeasure.real (subset ∩ Metric.closedBall center radius) :=
      measureReal_biUnion_finset_le centers _
    _ ≤ ∑ _center ∈ centers, bound := Finset.sum_le_sum (fun center _ => pieceBound center)
    _ = (centers.card : ℝ) * bound := by simp

theorem separated_finite_ball_card_mul_le_total_mass (physicalMeasure : Measure Space)
    [IsFiniteMeasure physicalMeasure] {Index : Type*} [Fintype Index]
    (centers : Index → Space) (radius massLower : ℝ)
    (separated : ∀ first second, first ≠ second → 2 * radius ≤ dist (centers first) (centers second))
    (ballMassLower : ∀ index, massLower ≤ physicalMeasure.real (Metric.ball (centers index) radius)) :
    (Fintype.card Index : ℝ) * massLower ≤ physicalMeasure.real Set.univ := by
  have disjoint : Pairwise (Disjoint on (fun index => Metric.ball (centers index) radius)) := by
    intro first second different
    apply Set.disjoint_left.mpr
    intro point firstNear secondNear
    have firstDistance : dist (centers first) point < radius := by
      simpa only [Metric.mem_ball, dist_comm] using firstNear
    have secondDistance : dist point (centers second) < radius := secondNear
    have triangle := dist_triangle (centers first) point (centers second)
    have lower := separated first second different
    linarith
  calc
    (Fintype.card Index : ℝ) * massLower = ∑ _index : Index, massLower := by simp
    _ ≤ ∑ index : Index, physicalMeasure.real (Metric.ball (centers index) radius) :=
      Finset.sum_le_sum (fun index _ => ballMassLower index)
    _ = physicalMeasure.real (⋃ index : Index, Metric.ball (centers index) radius) :=
      (measureReal_iUnion_fintype disjoint (fun _ => measurableSet_ball)).symm
    _ ≤ physicalMeasure.real Set.univ := measureReal_mono (Set.subset_univ _)

end
end IGS.Sec31

#print axioms IGS.Sec31.real_measure_le_finite_ball_cover_card_mul
#print axioms IGS.Sec31.separated_finite_ball_card_mul_le_total_mass
