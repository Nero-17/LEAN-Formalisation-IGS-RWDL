import RequestProject.Section31.CadlagJ1CarrierInstances

/-! Separation for the actual time-change infimum on a compact real interval.
Right continuity alone suffices. The terminal point is treated separately,
because an increasing bijection of the closed interval fixes that point.
The metric upgrade below does not assert completeness or Polishness.

The separation argument was suggested by IGSIII34/Diffusion/
SkorokhodCadlagSeparationCompletion.lean at reference commit
cb0183af15f571bb0b1b5d3b8de367a419716f1b. This proof is independently written
for the RWDL distance convention first(t), second(lambda(t)). -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set Filter Topology
open scoped UniformConvergence NNReal

variable {State : Type*} [MetricSpace State] [BoundedSpace State]

local instance j1SeparationIntervalBoundedSpace (horizon : ℝ≥0) :
    BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) := ⟨Metric.isBounded_of_compactSpace⟩

theorem intervalTimeChange_fixes_terminal (horizon : ℝ≥0)
    (change : Icc (0 : ℝ) (horizon : ℝ) ≃o Icc (0 : ℝ) (horizon : ℝ))
    (time : Icc (0 : ℝ) (horizon : ℝ)) (terminal : time.val = (horizon : ℝ)) :
    change time = time := by
  have upper (point : Icc (0 : ℝ) (horizon : ℝ)) : point ≤ time := by
    change point.val ≤ time.val
    rw [terminal]
    exact point.property.2
  apply le_antisymm (upper (change time))
  simpa only [OrderIso.apply_symm_apply] using change.monotone (upper (change.symm time))

theorem skorokhodJ1Distance_eq_zero_of_rightContinuous
    (horizon : ℝ≥0)
    (first second : Icc (0 : ℝ) (horizon : ℝ) → State)
    (firstRight : ∀ time, ContinuousWithinAt first (Ici time) time)
    (secondRight : ∀ time, ContinuousWithinAt second (Ici time) time)
    (zeroDistance : skorokhodJ1Distance first second = 0) : first = second := by
  have smallChange (epsilon : ℝ) (positive : 0 < epsilon) :
      ∃ change : Icc (0 : ℝ) (horizon : ℝ) ≃o Icc (0 : ℝ) (horizon : ℝ),
        skorokhodJ1Cost first second change < epsilon := by
    apply exists_lt_of_ciInf_lt
    change skorokhodJ1Distance first second < epsilon
    rwa [zeroDistance]
  funext time
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro epsilon positive
  by_cases terminal : time.val = (horizon : ℝ)
  · obtain ⟨change, small⟩ := smallChange epsilon positive
    have distance := skorokhodJ1Cost_path_le first second change time
    rw [intervalTimeChange_fixes_terminal horizon change time terminal] at distance
    simpa only [zero_add] using distance.trans small.le
  · have remainingPositive : 0 < (horizon : ℝ) - time.val := by
      have before : time.val < (horizon : ℝ) := lt_of_le_of_ne time.property.2 terminal
      linarith
    obtain ⟨firstDuration, firstPositive, firstNear⟩ :=
      Metric.continuousWithinAt_iff.mp (firstRight time) (epsilon / 3) (by positivity)
    obtain ⟨secondDuration, secondPositive, secondNear⟩ :=
      Metric.continuousWithinAt_iff.mp (secondRight time) (epsilon / 3) (by positivity)
    let duration : ℝ := min ((horizon : ℝ) - time.val) (min firstDuration secondDuration)
    have durationPositive : 0 < duration :=
      lt_min remainingPositive (lt_min firstPositive secondPositive)
    have durationRemaining : duration ≤ (horizon : ℝ) - time.val := min_le_left _ _
    have durationFirst : duration ≤ firstDuration := (min_le_right _ _).trans (min_le_left _ _)
    have durationSecond : duration ≤ secondDuration := (min_le_right _ _).trans (min_le_right _ _)
    let later : Icc (0 : ℝ) (horizon : ℝ) :=
      ⟨time.val + duration / 2, ⟨by linarith [time.property.1], by linarith⟩⟩
    have laterAfter : time ≤ later := by
      change time.val ≤ time.val + duration / 2
      linarith
    have laterDistance : dist later time = duration / 2 := by
      change |(time.val + duration / 2) - time.val| = duration / 2
      rw [add_sub_cancel_left, abs_of_pos (by positivity)]
    have errorPositive : 0 < min (duration / 4) (epsilon / 3) := by positivity
    obtain ⟨change, small⟩ := smallChange (min (duration / 4) (epsilon / 3)) errorPositive
    have clockClose : dist (change later) later < duration / 4 :=
      ((skorokhodJ1Cost_clock_le first second change later).trans_lt small).trans_le (min_le_left _ _)
    have changedAfter : time ≤ change later := by
      change time.val ≤ (change later).val
      change |(change later).val - (time.val + duration / 2)| < duration / 4 at clockClose
      have lower := (abs_lt.mp clockClose).1
      linarith
    have firstClose : dist (first later) (first time) < epsilon / 3 :=
      firstNear laterAfter (by rw [laterDistance]; linarith)
    have secondClose : dist (second (change later)) (second time) < epsilon / 3 :=
      secondNear changedAfter ((dist_triangle (change later) later time).trans_lt
        (by rw [laterDistance]; linarith))
    have pathsClose : dist (first later) (second (change later)) < epsilon / 3 :=
      ((skorokhodJ1Cost_path_le first second change later).trans_lt small).trans_le (min_le_right _ _)
    have triangle := (dist_triangle (first time) (first later) (second time)).trans
      (add_le_add le_rfl (dist_triangle (first later) (second (change later)) (second time)))
    rw [dist_comm (first later) (first time)] at firstClose
    simpa only [zero_add] using (show dist (first time) (second time) ≤ epsilon by linarith)

theorem cadlagIntervalJ1_dist_separates (horizon : ℝ≥0)
    (first second : CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State)
    (zeroDistance : dist first second = 0) : first = second := by
  have functions : first.val.toFun = second.val.toFun :=
    skorokhodJ1Distance_eq_zero_of_rightContinuous horizon first.val.toFun second.val.toFun
      first.property.1 second.property.1 zeroDistance
  apply Subtype.ext
  have reconstruct (path : J1Function (Icc (0 : ℝ) (horizon : ℝ)) State) :
      J1Function.mk path.toFun = path := by cases path; rfl
  exact (reconstruct first.val).symm.trans ((congrArg J1Function.mk functions).trans (reconstruct second.val))

/-- The existing subtype pseudometric is separated by the preceding proof.
This is an explicit structure, leaving its existing topology unchanged. -/
def cadlagIntervalJ1MetricSpace (horizon : ℝ≥0) :
    MetricSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) :=
  { toPseudoMetricSpace := inferInstance
    eq_of_dist_eq_zero := fun zero => cadlagIntervalJ1_dist_separates horizon _ _ zero }

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.intervalTimeChange_fixes_terminal
#print axioms IGS.Sec31.DiscreteMarkov.skorokhodJ1Distance_eq_zero_of_rightContinuous
#print axioms IGS.Sec31.DiscreteMarkov.cadlagIntervalJ1MetricSpace
