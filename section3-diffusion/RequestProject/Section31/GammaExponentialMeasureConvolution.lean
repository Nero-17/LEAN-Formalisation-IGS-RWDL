import RequestProject.Section31.GammaExponentialConvolutionIntegral
import Mathlib.Probability.HasLaw

/-! Distributional addition of one independent unit-exponential holding time
increments the natural gamma shape. -/

namespace IGS.Sec31
open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal NNReal Classical MeasureTheory
noncomputable section

 theorem gamma_natural_exponential_lconvolution (count : ℕ) :
    MeasureTheory.lconvolution (gammaPDF ((count : ℝ) + 1) 1)
      (exponentialPDF 1) volume = gammaPDF (((count + 1 : ℕ) : ℝ) + 1) 1 := by
  funext time
  rw [MeasureTheory.lconvolution_def]
  have reordered :
      (∫⁻ position : ℝ, gammaPDF ((count : ℝ) + 1) 1 position * exponentialPDF 1 (-position + time)) =
      (∫⁻ position : ℝ, gammaPDF ((count : ℝ) + 1) 1 position * exponentialPDF 1 (time - position)) := by
    apply lintegral_congr
    intro position
    congr 2
    ring
  rw [reordered]
  by_cases timeNonnegative : 0 ≤ time
  · rw [gamma_exponential_convolution_integral_nonnegative count time timeNonnegative,
      gammaPDF_natural_succ_unit_rate, if_pos timeNonnegative]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring
  · rw [gammaPDF_of_neg (lt_of_not_ge timeNonnegative)]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Eventually.of_forall
    intro position
    apply gamma_exponential_product_zero_off_interval
    intro membership
    exact timeNonnegative (membership.1.trans membership.2)

 theorem gamma_natural_measure_conv_exponential (count : ℕ) :
    gammaMeasure ((count : ℝ) + 1) 1 ∗ expMeasure 1 =
      gammaMeasure (((count + 1 : ℕ) : ℝ) + 1) 1 := by
  change volume.withDensity (gammaPDF ((count : ℝ) + 1) 1) ∗
    volume.withDensity (exponentialPDF 1) =
      volume.withDensity (gammaPDF (((count + 1 : ℕ) : ℝ) + 1) 1)
  rw [MeasureTheory.conv_withDensity_eq_lconvolution
    (measurable_gammaPDFReal ((count : ℝ) + 1) 1).ennreal_ofReal
    (measurable_exponentialPDFReal 1).ennreal_ofReal,
    gamma_natural_exponential_lconvolution]

end
end IGS.Sec31

#print axioms IGS.Sec31.gamma_natural_exponential_lconvolution
#print axioms IGS.Sec31.gamma_natural_measure_conv_exponential
