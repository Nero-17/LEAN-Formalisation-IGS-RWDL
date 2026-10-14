import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Strict positive continuity extends an eventual positive lower bound to
any fixed positive time window on which its weight is positive continuous.
The coefficient can change. This separates a uniform time-window statement
from the stronger, generally false, demand for a uniform coefficient. -/

namespace IGS.Sec31
open Set
noncomputable section
set_option autoImplicit false

theorem positive_local_lower_extend_to_fixed_window
    (value weight : ℝ → ℝ) (window : ℝ) (windowPositive : 0 < window)
    (valueContinuous : ContinuousOn value (Ioc 0 window))
    (weightContinuous : ContinuousOn weight (Ioc 0 window))
    (valuePositive : ∀ time ∈ Ioc 0 window, 0 < value time)
    (weightPositive : ∀ time ∈ Ioc 0 window, 0 < weight time)
    (coefficient threshold : ℝ) (coefficientPositive : 0 < coefficient)
    (thresholdPositive : 0 < threshold)
    (lower : ∀ time, 0 < time → time ≤ threshold → coefficient * weight time ≤ value time) :
    ∃ fixedCoefficient : ℝ, 0 < fixedCoefficient ∧
      ∀ time, 0 < time → time ≤ window → fixedCoefficient * weight time ≤ value time := by
  let first := min (threshold / 2) (window / 2)
  have firstPositive : 0 < first := lt_min (by positivity) (by positivity)
  have firstThreshold : first ≤ threshold :=
    (min_le_left _ _).trans (by linarith)
  have firstWindow : first ≤ window :=
    (min_le_right _ _).trans (by linarith)
  have subset : Icc first window ⊆ Ioc 0 window := by
    intro time membership
    exact ⟨firstPositive.trans_le membership.1, membership.2⟩
  have ratioContinuous : ContinuousOn (fun time => value time / weight time) (Icc first window) :=
    (valueContinuous.mono subset).div (weightContinuous.mono subset)
      (fun time membership => (weightPositive time (subset membership)).ne')
  obtain ⟨minimumTime, minimumMembership, minimumBound⟩ :=
    isCompact_Icc.exists_isMinOn ⟨first, le_rfl, firstWindow⟩ ratioContinuous
  have minimumPositive : 0 < value minimumTime / weight minimumTime :=
    div_pos (valuePositive minimumTime (subset minimumMembership))
      (weightPositive minimumTime (subset minimumMembership))
  refine ⟨min coefficient (value minimumTime / weight minimumTime),
    lt_min coefficientPositive minimumPositive, ?_⟩
  intro time timePositive timeWindow
  by_cases before : time ≤ first
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (weightPositive time ⟨timePositive, timeWindow⟩).le).trans
        (lower time timePositive (before.trans firstThreshold))
  · apply (le_div_iff₀ (weightPositive time ⟨timePositive, timeWindow⟩)).mp
    exact (min_le_right _ _).trans (minimumBound ⟨(le_of_not_ge before), timeWindow⟩)

end
end IGS.Sec31

#print axioms IGS.Sec31.positive_local_lower_extend_to_fixed_window
