import Mathlib.Probability.Process.Stopping
import Mathlib.Data.NNReal.Basic

/-! Adding a deterministic nonnegative delay preserves an NNReal-indexed
stopping time, including an extended stopping time that may equal infinity.
The proof uses a truncated-subtraction threshold and filtration monotonicity,
without a countability assumption on the time index. -/

namespace IGS.Sec31.StoppingApproximation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal
noncomputable section

theorem isStoppingTime_add_nnreal_delay
    {Sample : Type*} {ambient : MeasurableSpace Sample}
    (filtration : Filtration ℝ≥0 ambient) (stoppingTime : Sample → WithTop ℝ≥0)
    (stopping : IsStoppingTime filtration stoppingTime) (delay : ℝ≥0) :
    IsStoppingTime filtration (fun sample => stoppingTime sample + (delay : WithTop ℝ≥0)) := by
  intro horizon
  by_cases delayBound : delay ≤ horizon
  · have eventEquality :
        {sample | stoppingTime sample + (delay : WithTop ℝ≥0) ≤ horizon} =
          {sample | stoppingTime sample ≤ (horizon - delay : ℝ≥0)} := by
      ext sample
      cases stoppingTime sample with
      | top => simp
      | coe time =>
          simp only [Set.mem_setOf_eq]
          norm_cast
          exact (le_tsub_iff_right delayBound).symm
    rw [eventEquality]
    exact filtration.mono tsub_le_self _ (stopping.measurableSet_le (horizon - delay))
  · have eventEmpty : {sample | stoppingTime sample + (delay : WithTop ℝ≥0) ≤ horizon} = ∅ := by
      ext sample
      cases stoppingTime sample with
      | top => simp
      | coe time =>
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro inequality
          have realBound : time + delay ≤ horizon := by exact_mod_cast inequality
          exact delayBound ((le_add_of_nonneg_left (zero_le time)).trans realBound)
    rw [eventEmpty]
    exact @MeasurableSet.empty Sample (filtration horizon)

theorem isStoppingTime_finite_add_nnreal_delay
    {Sample : Type*} {ambient : MeasurableSpace Sample}
    (filtration : Filtration ℝ≥0 ambient) (stoppingTime : Sample → ℝ≥0)
    (stopping : IsStoppingTime filtration (fun sample => (stoppingTime sample : WithTop ℝ≥0))) (delay : ℝ≥0) :
    IsStoppingTime filtration (fun sample => (stoppingTime sample + delay : ℝ≥0)) := by
  simpa using isStoppingTime_add_nnreal_delay filtration
    (fun sample => (stoppingTime sample : WithTop ℝ≥0)) stopping delay

end
end IGS.Sec31.StoppingApproximation

#print axioms IGS.Sec31.StoppingApproximation.isStoppingTime_add_nnreal_delay
#print axioms IGS.Sec31.StoppingApproximation.isStoppingTime_finite_add_nnreal_delay
