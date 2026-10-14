import RequestProject.Section31.ExponentialMemorylessResidualLaw
import Mathlib.Probability.ConditionalProbability

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
noncomputable section

/-- The entire residual-time distribution, conditional on survival, is
again the same unit-exponential distribution. -/
theorem unit_exponential_conditional_residual_law
    (elapsed : ℝ) (elapsedNonnegative : 0 ≤ elapsed) :
    (ProbabilityTheory.cond (expMeasure 1) (Ioi elapsed)).map
      (fun value => value - elapsed) = expMeasure 1 := by
  rw [ProbabilityTheory.cond, Measure.map_smul,
    unit_exponential_surviving_residual_measure elapsed elapsedNonnegative,
    unit_exponential_tail_probability elapsed elapsedNonnegative, smul_smul,
    ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_smul]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.unit_exponential_conditional_residual_law
