import RequestProject.Section31.ExponentialHoldingPoissonCountLaw

/-! Deterministic tails of the actual infinite holding-time sample retain
the complete iid law. Cumulative arrival times respect the same shift. -/

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

def shiftedHoldingTimes (offset : ℕ) (holdingTimes : ℕ → ℝ) : ℕ → ℝ :=
  fun index => holdingTimes (offset + index)

theorem shiftedHoldingTimes_measurable (offset : ℕ) :
    Measurable (shiftedHoldingTimes offset) := by
  apply measurable_pi_lambda
  intro index
  exact measurable_pi_apply (offset + index)

theorem shiftedHoldingTimes_hasLaw (offset : ℕ) :
    HasLaw (shiftedHoldingTimes offset) exponentialHoldingTimeLaw exponentialHoldingTimeLaw := by
  refine ⟨(shiftedHoldingTimes_measurable offset).aemeasurable, ?_⟩
  have independent : iIndepFun
      (fun index (holdingTimes : ℕ → ℝ) => holdingTimes (offset + index))
        exponentialHoldingTimeLaw :=
    exponentialHoldingTimeLaw_independent.precomp (fun _ _ equality => Nat.add_left_cancel equality)
  have mapped := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun index => measurable_pi_apply (offset + index))).mp independent
  change exponentialHoldingTimeLaw.map (shiftedHoldingTimes offset) =
    Measure.infinitePi (fun index : ℕ => exponentialHoldingTimeLaw.map
      (fun holdingTimes => holdingTimes (offset + index))) at mapped
  simp_rw [exponentialHoldingTimeLaw_eval] at mapped
  exact mapped

theorem cumulativeHoldingTime_shift_add
    (holdingTimes : ℕ → ℝ) (offset count : ℕ) :
    cumulativeHoldingTime holdingTimes offset +
      cumulativeHoldingTime (shiftedHoldingTimes offset holdingTimes) count =
        cumulativeHoldingTime holdingTimes (offset + count) := by
  simp only [cumulativeHoldingTime, shiftedHoldingTimes, Finset.sum_range_add]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.shiftedHoldingTimes_measurable
#print axioms IGS.Sec31.PoissonClock.shiftedHoldingTimes_hasLaw
#print axioms IGS.Sec31.PoissonClock.cumulativeHoldingTime_shift_add
