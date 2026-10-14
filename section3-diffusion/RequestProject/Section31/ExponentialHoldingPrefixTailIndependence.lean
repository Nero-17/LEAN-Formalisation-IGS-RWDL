import RequestProject.Section31.ExponentialHoldingClockShift

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 2200000

/-- All future holding times, as a single infinite random sequence, are
independent of the entire finite prefix. -/
theorem exponential_holding_prefix_tail_independent (count : ℕ) :
    IndepFun (fun holdingTimes : ℕ → ℝ => fun index : Fin count => holdingTimes index)
      (shiftedHoldingTimes count) exponentialHoldingTimeLaw := by
  let coordinateSpaces : ℕ → MeasurableSpace (ℕ → ℝ) := fun index =>
    (inferInstance : MeasurableSpace ℝ).comap (fun holdingTimes => holdingTimes index)
  have coordinateMeasurable : ∀ index, coordinateSpaces index ≤
      (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
    intro index
    exact (measurable_pi_apply index).comap_le
  have coordinateIndependent : iIndep coordinateSpaces exponentialHoldingTimeLaw :=
    exponentialHoldingTimeLaw_independent.iIndep
  have indicesDisjoint : Disjoint {index : ℕ | index < count} {index : ℕ | count ≤ index} := by
    apply Set.disjoint_left.mpr
    intro index before after
    exact Nat.not_lt.mpr after before
  have independent := indep_iSup_of_disjoint coordinateMeasurable coordinateIndependent indicesDisjoint
  have prefixMeasurable :
      (inferInstance : MeasurableSpace (Fin count → ℝ)).comap
          (fun holdingTimes : ℕ → ℝ => fun index : Fin count => holdingTimes index) ≤
        ⨆ index ∈ {index : ℕ | index < count}, coordinateSpaces index := by
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro index
    simp only [MeasurableSpace.comap_comp, Function.comp_def]
    change coordinateSpaces (index : ℕ) ≤ _
    apply le_iSup_of_le (index : ℕ)
    apply le_iSup_of_le (show (index : ℕ) ∈ {index : ℕ | index < count} from index.isLt)
    exact le_rfl
  have tailMeasurable :
      (inferInstance : MeasurableSpace (ℕ → ℝ)).comap (shiftedHoldingTimes count) ≤
        ⨆ index ∈ {index : ℕ | count ≤ index}, coordinateSpaces index := by
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro index
    simp only [MeasurableSpace.comap_comp, Function.comp_def, shiftedHoldingTimes]
    change coordinateSpaces (count + index) ≤ _
    apply le_iSup_of_le (count + index)
    apply le_iSup_of_le
      (show count + index ∈ {index : ℕ | count ≤ index} from Nat.le_add_right count index)
    exact le_rfl
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left independent prefixMeasurable) tailMeasurable

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponential_holding_prefix_tail_independent
