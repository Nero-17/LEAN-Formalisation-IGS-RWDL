import Mathlib.Probability.Process.Stopping
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-! Dyadic upper approximations of real, everywhere finite stopping times.
The stopping time is represented by an NNReal-valued function, so no value
at infinity is assigned an artificial finite process state. The stopping
proof uses only the original filtration's monotonicity. -/

namespace IGS.Sec31.StoppingApproximation

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 4000000

def dyadicUpwardTime (level : ℕ) (time : ℝ≥0) : ℝ≥0 :=
  (Nat.ceil ((2 : ℝ≥0) ^ level * time) : ℝ≥0) / (2 : ℝ≥0) ^ level

theorem time_le_dyadicUpwardTime (level : ℕ) (time : ℝ≥0) :
    time ≤ dyadicUpwardTime level time := by
  rw [dyadicUpwardTime, le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) level)]
  simpa only [mul_comm] using Nat.le_ceil ((2 : ℝ≥0) ^ level * time)

theorem dyadicUpwardTime_lt_add_mesh (level : ℕ) (time : ℝ≥0) :
    dyadicUpwardTime level time < time + 1 / (2 : ℝ≥0) ^ level := by
  rw [dyadicUpwardTime, div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) level)]
  calc
    (Nat.ceil ((2 : ℝ≥0) ^ level * time) : ℝ≥0) < (2 : ℝ≥0) ^ level * time + 1 :=
      Nat.ceil_lt_add_one (zero_le _)
    _ = (time + 1 / (2 : ℝ≥0) ^ level) * (2 : ℝ≥0) ^ level := by
      rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num : (2 : ℝ≥0) ≠ 0))]
      rw [mul_comm]

theorem dyadicUpwardTime_le_iff (level : ℕ) (time horizon : ℝ≥0) :
    dyadicUpwardTime level time ≤ horizon ↔
      time ≤ (Nat.floor ((2 : ℝ≥0) ^ level * horizon) : ℝ≥0) / (2 : ℝ≥0) ^ level := by
  rw [dyadicUpwardTime, div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) level),
    ← Nat.le_floor_iff (zero_le (horizon * (2 : ℝ≥0) ^ level)), Nat.ceil_le,
    le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) level)]
  simp only [mul_comm]

theorem dyadicFloorTime_le (level : ℕ) (horizon : ℝ≥0) :
    (Nat.floor ((2 : ℝ≥0) ^ level * horizon) : ℝ≥0) / (2 : ℝ≥0) ^ level ≤ horizon := by
  rw [div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) level)]
  simpa only [mul_comm] using Nat.floor_le (zero_le ((2 : ℝ≥0) ^ level * horizon))

theorem dyadicUpwardTime_range_countable (level : ℕ) :
    (Set.range (dyadicUpwardTime level)).Countable := by
  apply (Set.countable_range (fun index : ℕ => (index : ℝ≥0) / (2 : ℝ≥0) ^ level)).mono
  rintro _ ⟨time, rfl⟩
  exact ⟨Nat.ceil ((2 : ℝ≥0) ^ level * time), rfl⟩

theorem dyadicUpwardTime_tendsto (time : ℝ≥0) :
    Tendsto (fun level => dyadicUpwardTime level time) atTop (𝓝 time) := by
  have meshTendsto : Tendsto (fun level : ℕ => 1 / (2 : ℝ≥0) ^ level) atTop (𝓝 0) := by
    simpa only [one_div, ← inv_pow] using
      NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0)⁻¹) (by norm_num)
  have upperTendsto : Tendsto (fun level : ℕ => time + 1 / (2 : ℝ≥0) ^ level) atTop (𝓝 time) := by
    simpa only [add_zero] using tendsto_const_nhds.add meshTendsto
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds upperTendsto
    (fun level => time_le_dyadicUpwardTime level time)
    (fun level => (dyadicUpwardTime_lt_add_mesh level time).le)

theorem isStoppingTime_dyadicUpwardTime
    {Sample : Type*} {measurableSpace : MeasurableSpace Sample}
    (filtration : Filtration ℝ≥0 measurableSpace) (stoppingTime : Sample → ℝ≥0)
    (stopping : IsStoppingTime filtration (fun sample => (stoppingTime sample : WithTop ℝ≥0)))
    (level : ℕ) :
    IsStoppingTime filtration
      (fun sample => (dyadicUpwardTime level (stoppingTime sample) : WithTop ℝ≥0)) := by
  intro horizon
  have eventEquality :
      {sample | (dyadicUpwardTime level (stoppingTime sample) : WithTop ℝ≥0) ≤ horizon} =
        {sample | (stoppingTime sample : WithTop ℝ≥0) ≤
          ((Nat.floor ((2 : ℝ≥0) ^ level * horizon) : ℝ≥0) / (2 : ℝ≥0) ^ level : ℝ≥0)} := by
    ext sample
    simpa only [Set.mem_setOf_eq, WithTop.coe_le_coe] using
      dyadicUpwardTime_le_iff level (stoppingTime sample) horizon
  rw [eventEquality]
  exact filtration.mono (dyadicFloorTime_le level horizon) _
    (stopping.measurableSet_le ((Nat.floor ((2 : ℝ≥0) ^ level * horizon) : ℝ≥0) / (2 : ℝ≥0) ^ level))

end
end IGS.Sec31.StoppingApproximation

#print axioms IGS.Sec31.StoppingApproximation.time_le_dyadicUpwardTime
#print axioms IGS.Sec31.StoppingApproximation.dyadicUpwardTime_lt_add_mesh
#print axioms IGS.Sec31.StoppingApproximation.dyadicUpwardTime_le_iff
#print axioms IGS.Sec31.StoppingApproximation.dyadicFloorTime_le
#print axioms IGS.Sec31.StoppingApproximation.dyadicUpwardTime_range_countable
#print axioms IGS.Sec31.StoppingApproximation.dyadicUpwardTime_tendsto
#print axioms IGS.Sec31.StoppingApproximation.isStoppingTime_dyadicUpwardTime
