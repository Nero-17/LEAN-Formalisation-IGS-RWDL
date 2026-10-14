import RequestProject.Section31.ExponentialGammaNaturalDensity
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The complete gamma--exponential convolution integral, including the
support restriction; this supplies the distributional induction step. -/

namespace IGS.Sec31
open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal NNReal Classical
noncomputable section

 theorem gamma_exponential_product_zero_off_interval (count : ℕ) (time position : ℝ)
    (outside : position ∉ Set.Icc 0 time) :
    gammaPDF ((count : ℝ) + 1) 1 position * exponentialPDF 1 (time - position) = 0 := by
  by_cases nonnegative : 0 ≤ position
  · have afterTime : time < position := lt_of_not_ge (fun before => outside ⟨nonnegative, before⟩)
    rw [exponentialPDF_of_neg (by linarith : time - position < 0), mul_zero]
  · rw [gammaPDF_of_neg (lt_of_not_ge nonnegative), zero_mul]

 theorem gamma_exponential_convolution_integral_nonnegative (count : ℕ) (time : ℝ)
    (timeNonnegative : 0 ≤ time) :
    (∫⁻ position : ℝ, gammaPDF ((count : ℝ) + 1) 1 position * exponentialPDF 1 (time - position)) =
      ENNReal.ofReal (Real.exp (-time) / (count.factorial : ℝ) *
        time ^ (count + 1) / (count + 1 : ℝ)) := by
  have supported (position : ℝ) :
      gammaPDF ((count : ℝ) + 1) 1 position * exponentialPDF 1 (time - position) =
        (Set.Icc 0 time).indicator (fun position : ℝ =>
          ENNReal.ofReal (Real.exp (-time) / (count.factorial : ℝ) * position ^ count)) position := by
    by_cases membership : position ∈ Set.Icc 0 time
    · rw [Set.indicator_of_mem membership]
      exact gamma_exponential_density_product_on_interval count time position membership.1 membership.2
    · rw [Set.indicator_of_notMem membership]
      exact gamma_exponential_product_zero_off_interval count time position membership
  have integrable : IntegrableOn
      (fun position : ℝ => Real.exp (-time) / (count.factorial : ℝ) * position ^ count)
      (Set.Icc 0 time) :=
    (continuous_const.mul (continuous_id.pow count)).integrableOn_Icc
  have nonnegative : 0 ≤ᵐ[volume.restrict (Set.Icc 0 time)]
      (fun position : ℝ => Real.exp (-time) / (count.factorial : ℝ) * position ^ count) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with position membership
    exact mul_nonneg (div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _))
      (pow_nonneg membership.1 count)
  calc
    _ = ∫⁻ position : ℝ, (Set.Icc 0 time).indicator (fun position : ℝ =>
          ENNReal.ofReal (Real.exp (-time) / (count.factorial : ℝ) * position ^ count)) position :=
      lintegral_congr supported
    _ = ∫⁻ position in Set.Icc 0 time,
          ENNReal.ofReal (Real.exp (-time) / (count.factorial : ℝ) * position ^ count) :=
      lintegral_indicator measurableSet_Icc (fun position : ℝ =>
        ENNReal.ofReal (Real.exp (-time) / (count.factorial : ℝ) * position ^ count))
    _ = ENNReal.ofReal (∫ position in Set.Icc 0 time,
          Real.exp (-time) / (count.factorial : ℝ) * position ^ count) :=
      (ofReal_integral_eq_lintegral_ofReal integrable nonnegative).symm
    _ = _ := by
      congr 1
      rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le timeNonnegative, integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero count), sub_zero, Nat.cast_add, Nat.cast_one]
      ring

end
end IGS.Sec31

#print axioms IGS.Sec31.gamma_exponential_product_zero_off_interval
#print axioms IGS.Sec31.gamma_exponential_convolution_integral_nonnegative
