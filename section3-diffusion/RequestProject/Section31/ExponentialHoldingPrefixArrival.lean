import RequestProject.Section31.ExponentialHoldingPrefixNextTailLaw
import Mathlib.Algebra.BigOperators.Fin

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

def holdingPrefixArrival {count : ℕ} (historyPoint : Fin count → ℝ) : ℝ :=
  ∑ index, historyPoint index

theorem holdingPrefixArrival_measurable (count : ℕ) :
    Measurable (holdingPrefixArrival (count := count)) := by
  unfold holdingPrefixArrival
  fun_prop

theorem holdingPrefixArrival_actual (holdingTimes : ℕ → ℝ) (count : ℕ) :
    holdingPrefixArrival (holdingPrefix count holdingTimes) =
      cumulativeHoldingTime holdingTimes count := by
  simp only [holdingPrefixArrival, holdingPrefix, cumulativeHoldingTime, Finset.sum_range]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingPrefixArrival_measurable
#print axioms IGS.Sec31.PoissonClock.holdingPrefixArrival_actual
