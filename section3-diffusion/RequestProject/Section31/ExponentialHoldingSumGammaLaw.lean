import RequestProject.Section31.GammaExponentialMeasureConvolution
import RequestProject.Section31.ExponentialHoldingTimePaths

/-! The actual cumulative holding-time law, supplied from the original
infinite product exponential sample, not assumed as a gamma input. -/

namespace IGS.Sec31.PoissonClock
open ProbabilityTheory MeasureTheory
open scoped Classical BigOperators ENNReal NNReal MeasureTheory
noncomputable section

 theorem exponentialHoldingTime_eval_hasLaw (index : ℕ) :
    HasLaw (fun holdingTimes : ℕ → ℝ => holdingTimes index) (expMeasure 1) exponentialHoldingTimeLaw :=
  ⟨(measurable_pi_apply index).aemeasurable, exponentialHoldingTimeLaw_eval index⟩

 theorem cumulativeHoldingTime_independent_next (count : ℕ) :
    IndepFun (fun holdingTimes : ℕ → ℝ => cumulativeHoldingTime holdingTimes count)
      (fun holdingTimes : ℕ → ℝ => holdingTimes count) exponentialHoldingTimeLaw := by
  simpa only [Finset.sum_apply, cumulativeHoldingTime] using
    exponentialHoldingTimeLaw_independent.indepFun_sum_range_succ
      (fun index => measurable_pi_apply index) count

 theorem cumulativeHoldingTime_gamma_hasLaw (count : ℕ) :
    HasLaw (fun holdingTimes : ℕ → ℝ => cumulativeHoldingTime holdingTimes (count + 1))
      (gammaMeasure ((count : ℝ) + 1) 1) exponentialHoldingTimeLaw := by
  induction count with
  | zero =>
      simpa only [Nat.cast_zero, zero_add, cumulativeHoldingTime, Finset.sum_range_one, expMeasure] using
        exponentialHoldingTime_eval_hasLaw 0
  | succ previous inductionHypothesis =>
      letI : IsProbabilityMeasure (gammaMeasure ((previous : ℝ) + 1) 1) :=
        isProbabilityMeasure_gammaMeasure (by positivity) zero_lt_one
      have added := (cumulativeHoldingTime_independent_next (previous + 1)).hasLaw_fun_add
        inductionHypothesis (exponentialHoldingTime_eval_hasLaw (previous + 1))
      rw [IGS.Sec31.gamma_natural_measure_conv_exponential] at added
      simpa only [Nat.succ_eq_add_one, cumulativeHoldingTime, Finset.sum_range_succ,
        Nat.cast_add, Nat.cast_one] using added

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponentialHoldingTime_eval_hasLaw
#print axioms IGS.Sec31.PoissonClock.cumulativeHoldingTime_independent_next
#print axioms IGS.Sec31.PoissonClock.cumulativeHoldingTime_gamma_hasLaw
