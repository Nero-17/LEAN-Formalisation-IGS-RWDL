import RequestProject.Section31.ExponentialResidualClockMeasurable
import RequestProject.Section31.ExponentialHoldingPrefixNextTailLaw

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000

def holdingPrefixExtension {count : ℕ} (historyPoint : Fin count → ℝ) (index : ℕ) : ℝ :=
  if small : index < count then historyPoint ⟨index, small⟩ else 0

theorem holdingPrefixExtension_measurable (count : ℕ) :
    Measurable (holdingPrefixExtension (count := count)) := by
  apply measurable_pi_lambda
  intro index
  by_cases small : index < count
  · simpa only [holdingPrefixExtension, dif_pos small] using
      (measurable_pi_apply (⟨index, small⟩ : Fin count))
  · simpa only [holdingPrefixExtension, dif_neg small] using
      (measurable_const : Measurable (fun _ : Fin count → ℝ => (0 : ℝ)))

theorem cumulativeHoldingTime_prefix
    (holdingTimes : ℕ → ℝ) (count previous : ℕ) (previousBound : previous ≤ count) :
    cumulativeHoldingTime (holdingPrefixExtension (holdingPrefix count holdingTimes)) previous =
      cumulativeHoldingTime holdingTimes previous := by
  unfold cumulativeHoldingTime
  apply Finset.sum_congr rfl
  intro index membership
  have small : index < count := (Finset.mem_range.mp membership).trans_le previousBound
  simp only [holdingPrefixExtension, dif_pos small, holdingPrefix]

theorem holdingJumpIndex_past_on_count
    (holdingTimes : ℕ → ℝ) (nonnegative : ∀ index, 0 ≤ holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (time previousTime : ℝ) (timeNonnegative : 0 ≤ time)
    (previousNonnegative : 0 ≤ previousTime) (previousBound : previousTime ≤ time)
    (count previousCount : ℕ) (countEquality : holdingJumpIndex holdingTimes time = count) :
    holdingJumpIndex holdingTimes previousTime = previousCount ↔
      previousCount ≤ count ∧ cumulativeHoldingTime holdingTimes previousCount ≤ previousTime ∧
        (previousCount = count ∨ previousTime < cumulativeHoldingTime holdingTimes (previousCount + 1)) := by
  have originalInterval := (holdingJumpIndex_eq_iff_interval holdingTimes nonnegative nonexplosion
    time timeNonnegative count).mp countEquality
  have previousIff := holdingJumpIndex_eq_iff_interval holdingTimes nonnegative nonexplosion
    previousTime previousNonnegative previousCount
  constructor
  · intro previousEquality
    obtain ⟨lower, upper⟩ := previousIff.mp previousEquality
    have countBound : previousCount ≤ count := by
      by_contra notBounded
      have indexBound : count + 1 ≤ previousCount := by omega
      have ordered := cumulativeHoldingTime_monotone holdingTimes nonnegative indexBound
      exact not_lt_of_ge (ordered.trans (lower.trans previousBound)) originalInterval.2
    exact ⟨countBound, lower, Or.inr upper⟩
  · rintro ⟨_, lower, last | upper⟩
    · subst previousCount
      exact previousIff.mpr ⟨lower, previousBound.trans_lt originalInterval.2⟩
    · exact previousIff.mpr ⟨lower, upper⟩

theorem holdingJumpIndex_past_prefix_on_count
    (holdingTimes : ℕ → ℝ) (nonnegative : ∀ index, 0 ≤ holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (time previousTime : ℝ) (timeNonnegative : 0 ≤ time)
    (previousNonnegative : 0 ≤ previousTime) (previousBound : previousTime ≤ time)
    (count previousCount : ℕ) (countEquality : holdingJumpIndex holdingTimes time = count) :
    holdingJumpIndex holdingTimes previousTime = previousCount ↔
      previousCount ≤ count ∧
      cumulativeHoldingTime (holdingPrefixExtension (holdingPrefix count holdingTimes)) previousCount ≤ previousTime ∧
        (previousCount = count ∨ previousTime <
          cumulativeHoldingTime (holdingPrefixExtension (holdingPrefix count holdingTimes)) (previousCount + 1)) := by
  have actualIff := holdingJumpIndex_past_on_count holdingTimes nonnegative nonexplosion
    time previousTime timeNonnegative previousNonnegative previousBound count previousCount countEquality
  by_cases countBound : previousCount ≤ count
  · rw [cumulativeHoldingTime_prefix holdingTimes count previousCount countBound]
    by_cases last : previousCount = count
    · simpa only [last, true_or] using actualIff
    · rw [cumulativeHoldingTime_prefix holdingTimes count (previousCount + 1) (by omega)]
      exact actualIff
  · simpa only [countBound, false_and] using actualIff

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingPrefixExtension_measurable
#print axioms IGS.Sec31.PoissonClock.cumulativeHoldingTime_prefix
#print axioms IGS.Sec31.PoissonClock.holdingJumpIndex_past_on_count
#print axioms IGS.Sec31.PoissonClock.holdingJumpIndex_past_prefix_on_count
