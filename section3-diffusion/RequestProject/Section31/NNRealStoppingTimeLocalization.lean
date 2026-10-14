import Mathlib.Probability.Process.Stopping
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-! Localize an extended NNReal stopping time by finite deterministic
cutoffs. Every truncated value is genuinely finite. No process value at
an infinite stopping time is interpreted through the arbitrary default
of WithTop.untopA. -/

namespace IGS.Sec31.StoppingApproximation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 4000000

theorem coe_untopA_of_ne_top (time : WithTop ℝ≥0) (finite : time ≠ ⊤) :
    (time.untopA : WithTop ℝ≥0) = time := by
  lift time to ℝ≥0 using finite
  rfl

def finiteTruncation {Sample : Type*} (stoppingTime : Sample → WithTop ℝ≥0) (cutoff : ℝ≥0) (sample : Sample) : ℝ≥0 :=
  (min (stoppingTime sample) (cutoff : WithTop ℝ≥0)).untopA

theorem finiteTruncation_coe {Sample : Type*} (stoppingTime : Sample → WithTop ℝ≥0) (cutoff : ℝ≥0) (sample : Sample) :
    (finiteTruncation stoppingTime cutoff sample : WithTop ℝ≥0) = min (stoppingTime sample) (cutoff : WithTop ℝ≥0) := by
  apply coe_untopA_of_ne_top
  exact ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)

theorem finiteTruncation_eq_of_le {Sample : Type*} (stoppingTime : Sample → WithTop ℝ≥0) (cutoff : ℝ≥0) (sample : Sample)
    (timeBound : stoppingTime sample ≤ (cutoff : WithTop ℝ≥0)) :
    finiteTruncation stoppingTime cutoff sample = (stoppingTime sample).untopA := by
  unfold finiteTruncation
  rw [min_eq_left timeBound]

theorem finiteTruncation_isStoppingTime
    {Sample : Type*} {ambient : MeasurableSpace Sample}
    (filtration : Filtration ℝ≥0 ambient) (stoppingTime : Sample → WithTop ℝ≥0)
    (stopping : IsStoppingTime filtration stoppingTime) (cutoff : ℝ≥0) :
    IsStoppingTime filtration (fun sample => (finiteTruncation stoppingTime cutoff sample : WithTop ℝ≥0)) := by
  intro horizon
  have eventEquality :
      {sample | (finiteTruncation stoppingTime cutoff sample : WithTop ℝ≥0) ≤ horizon} =
        {sample | min (stoppingTime sample) (cutoff : WithTop ℝ≥0) ≤ horizon} := by
    ext sample
    change ((finiteTruncation stoppingTime cutoff sample : WithTop ℝ≥0) ≤ horizon) ↔ _
    rw [finiteTruncation_coe]
  rw [eventEquality]
  exact (stopping.min_const cutoff).measurableSet_le horizon

theorem finiteTruncation_localized_event_measurable
    {Sample : Type*} [ambient : MeasurableSpace Sample]
    (filtration : Filtration ℝ≥0 ambient) (stoppingTime : Sample → WithTop ℝ≥0)
    (stopping : IsStoppingTime filtration stoppingTime) (cutoff : ℝ≥0) (event : Set Sample)
    (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    MeasurableSet[(finiteTruncation_isStoppingTime filtration stoppingTime stopping cutoff).measurableSpace]
      (event ∩ {sample | stoppingTime sample ≤ (cutoff : WithTop ℝ≥0)}) := by
  have localizedOriginal := (stopping.measurableSet_inter_le_const_iff event cutoff).mp
    (eventMeasurable.inter (stopping.measurableSet_le' cutoff))
  change MeasurableSet (event ∩ {sample | stoppingTime sample ≤ (cutoff : WithTop ℝ≥0)}) ∧
    ∀ horizon, MeasurableSet[filtration horizon]
      ((event ∩ {sample | stoppingTime sample ≤ (cutoff : WithTop ℝ≥0)}) ∩
        {sample | min (stoppingTime sample) (cutoff : WithTop ℝ≥0) ≤ horizon}) at localizedOriginal
  change MeasurableSet (event ∩ {sample | stoppingTime sample ≤ (cutoff : WithTop ℝ≥0)}) ∧
    ∀ horizon, MeasurableSet[filtration horizon]
      ((event ∩ {sample | stoppingTime sample ≤ (cutoff : WithTop ℝ≥0)}) ∩
        {sample | (finiteTruncation stoppingTime cutoff sample : WithTop ℝ≥0) ≤ horizon})
  refine ⟨localizedOriginal.1, ?_⟩
  intro horizon
  have eventEquality :
      ((event ∩ {sample | stoppingTime sample ≤ (cutoff : WithTop ℝ≥0)}) ∩
        {sample | (finiteTruncation stoppingTime cutoff sample : WithTop ℝ≥0) ≤ horizon}) =
      ((event ∩ {sample | stoppingTime sample ≤ (cutoff : WithTop ℝ≥0)}) ∩
        {sample | min (stoppingTime sample) (cutoff : WithTop ℝ≥0) ≤ horizon}) := by
    ext sample
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, finiteTruncation_coe]
  rw [eventEquality]
  exact localizedOriginal.2 horizon

theorem iUnion_stoppingTime_le_nat {Sample : Type*} (stoppingTime : Sample → WithTop ℝ≥0) :
    (⋃ cutoff : ℕ, {sample | stoppingTime sample ≤ ((cutoff : ℝ≥0) : WithTop ℝ≥0)}) =
      {sample | stoppingTime sample ≠ ⊤} := by
  ext sample
  constructor
  · intro membership
    obtain ⟨cutoff, timeBound⟩ := Set.mem_iUnion.mp membership
    exact ne_top_of_le_ne_top WithTop.coe_ne_top timeBound
  · intro finite
    have timeBound : ((stoppingTime sample).untopA : WithTop ℝ≥0) ≤
        ((Nat.ceil (stoppingTime sample).untopA : ℝ≥0) : WithTop ℝ≥0) :=
      WithTop.coe_le_coe.mpr (Nat.le_ceil _)
    rw [coe_untopA_of_ne_top (stoppingTime sample) finite] at timeBound
    exact Set.mem_iUnion.mpr ⟨Nat.ceil (stoppingTime sample).untopA, timeBound⟩

end
end IGS.Sec31.StoppingApproximation

#print axioms IGS.Sec31.StoppingApproximation.coe_untopA_of_ne_top
#print axioms IGS.Sec31.StoppingApproximation.finiteTruncation_coe
#print axioms IGS.Sec31.StoppingApproximation.finiteTruncation_eq_of_le
#print axioms IGS.Sec31.StoppingApproximation.finiteTruncation_isStoppingTime
#print axioms IGS.Sec31.StoppingApproximation.finiteTruncation_localized_event_measurable
#print axioms IGS.Sec31.StoppingApproximation.iUnion_stoppingTime_le_nat
