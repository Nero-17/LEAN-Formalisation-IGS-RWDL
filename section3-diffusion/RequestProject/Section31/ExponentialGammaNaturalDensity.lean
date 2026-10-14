import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Natural-shape gamma densities for the original iid unit-exponential
holding-time count law. These identities alone are not a Poisson-process proof. -/

namespace IGS.Sec31
open ProbabilityTheory MeasureTheory Real
open scoped ENNReal NNReal
noncomputable section

 theorem gammaPDF_natural_succ_unit_rate (count : ℕ) (value : ℝ) :
    gammaPDF ((count : ℝ) + 1) 1 value =
      if 0 ≤ value then ENNReal.ofReal (value ^ count * Real.exp (-value) / (count.factorial : ℝ)) else 0 := by
  unfold gammaPDF gammaPDFReal
  split_ifs with nonnegative
  · simp only [Real.one_rpow, Real.Gamma_nat_eq_factorial, add_sub_cancel_right,
      Real.rpow_natCast, one_mul]
    congr 1
    ring
  · simp only [ENNReal.ofReal_zero]

 theorem gamma_exponential_density_product_on_interval (count : ℕ) (time position : ℝ)
    (positionNonnegative : 0 ≤ position) (positionAtMostTime : position ≤ time) :
    gammaPDF ((count : ℝ) + 1) 1 position * exponentialPDF 1 (time - position) =
      ENNReal.ofReal (Real.exp (-time) / (count.factorial : ℝ) * position ^ count) := by
  have exponentialIdentity : exponentialPDF 1 (time - position) = ENNReal.ofReal (Real.exp (-(time - position))) := by
    rw [exponentialPDF_eq, if_pos (sub_nonneg.mpr positionAtMostTime)]
    simp only [one_mul]
  rw [gammaPDF_natural_succ_unit_rate, if_pos positionNonnegative, exponentialIdentity,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add]
  have exponentIdentity : -position + -(time - position) = -time := by ring
  rw [exponentIdentity]
  ring

end
end IGS.Sec31

#print axioms IGS.Sec31.gammaPDF_natural_succ_unit_rate
#print axioms IGS.Sec31.gamma_exponential_density_product_on_interval
