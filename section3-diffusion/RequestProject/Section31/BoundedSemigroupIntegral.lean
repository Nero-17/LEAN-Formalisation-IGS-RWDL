import RequestProject.Section31.BoundedSemigroupComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The actual bounded exponential solves its integral equation. This is the
finite-operator identity needed to identify the generator after taking the
constructed Yosida limit. -/

namespace IGS.Sec31.BoundedSemigroupIntegral

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

noncomputable local instance : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

theorem exp_apply_hasDerivAt (generator : H →L[ℝ] H) (values : H) (time : ℝ) :
    HasDerivAt (fun parameter : ℝ => NormedSpace.exp ((-parameter) • generator) values)
      (-(NormedSpace.exp ((-time) • generator) (generator values))) time := by
  have operatorDerivative := (hasDerivAt_exp_smul_const generator (-time)).scomp
    time (hasDerivAt_id time).neg
  simp only [Function.comp_def, id_eq, neg_one_smul] at operatorDerivative
  have applied := operatorDerivative.clm_apply (hasDerivAt_const time values)
  simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.map_zero, add_zero] using applied

theorem exp_apply_sub_eq_integral (generator : H →L[ℝ] H) (values : H) (time : ℝ) :
    NormedSpace.exp ((-time) • generator) values - values =
      -(∫ parameter in (0 : ℝ)..time,
        NormedSpace.exp ((-parameter) • generator) (generator values)) := by
  have integrandContinuous : Continuous (fun parameter : ℝ =>
      -(NormedSpace.exp ((-parameter) • generator) (generator values))) :=
    ((NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)).clm_apply continuous_const).neg
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun parameter (_ : parameter ∈ Set.uIcc (0 : ℝ) time) =>
      exp_apply_hasDerivAt generator values parameter)
    (integrandContinuous.intervalIntegrable 0 time)
  rw [intervalIntegral.integral_neg] at identity
  simpa only [neg_zero, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply] using identity.symm

end IGS.Sec31.BoundedSemigroupIntegral

#print axioms IGS.Sec31.BoundedSemigroupIntegral.exp_apply_hasDerivAt
#print axioms IGS.Sec31.BoundedSemigroupIntegral.exp_apply_sub_eq_integral
