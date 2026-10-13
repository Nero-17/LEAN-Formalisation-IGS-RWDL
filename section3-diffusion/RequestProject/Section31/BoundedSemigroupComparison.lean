import RequestProject.Section31.BoundedYosidaSemigroup
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

/-! A comparison estimate for commuting bounded contraction semigroups, proved
by differentiating the actual interpolating operator exponential.  The bound
depends on the generator difference applied to the vector, not on either
generator's operator norm. -/

namespace IGS.Sec31.BoundedSemigroupComparison

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

noncomputable local instance : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

theorem interpolation_hasDerivAt (firstGenerator secondGenerator : H →L[ℝ] H)
    (commuting : Commute firstGenerator secondGenerator) (time parameter : ℝ)
    (values : H) :
    HasDerivAt (fun parameter : ℝ =>
      (NormedSpace.exp ((parameter - time) • firstGenerator) *
        NormedSpace.exp ((-parameter) • secondGenerator)) values)
      ((NormedSpace.exp ((parameter - time) • firstGenerator) *
        NormedSpace.exp ((-parameter) • secondGenerator))
          (firstGenerator values - secondGenerator values)) parameter := by
  have firstDerivative :=
    (hasDerivAt_exp_smul_const firstGenerator (parameter - time)).scomp
      parameter ((hasDerivAt_id parameter).sub_const time)
  have secondDerivative :=
    (hasDerivAt_exp_smul_const secondGenerator (-parameter)).scomp
      parameter (hasDerivAt_id parameter).neg
  simp only [Function.comp_def, id_eq, one_smul, neg_one_smul] at firstDerivative secondDerivative
  have derivative := (firstDerivative.mul secondDerivative).clm_apply
    (hasDerivAt_const parameter values)
  have movingCommute : Commute firstGenerator
      (NormedSpace.exp ((-parameter) • secondGenerator)) :=
    (commuting.smul_right (-parameter)).exp_right
  have derivativeIdentity :
      ((NormedSpace.exp ((parameter - time) • firstGenerator) * firstGenerator) *
          NormedSpace.exp ((-parameter) • secondGenerator) +
        NormedSpace.exp ((parameter - time) • firstGenerator) *
          (-(NormedSpace.exp ((-parameter) • secondGenerator) * secondGenerator))) =
      (NormedSpace.exp ((parameter - time) • firstGenerator) *
        NormedSpace.exp ((-parameter) • secondGenerator)) *
          (firstGenerator - secondGenerator) := by
    rw [mul_assoc (NormedSpace.exp ((parameter - time) • firstGenerator))
      firstGenerator (NormedSpace.exp ((-parameter) • secondGenerator)), movingCommute.eq]
    noncomm_ring
  simpa only [Pi.mul_apply, derivativeIdentity, ContinuousLinearMap.map_zero, add_zero,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply] using derivative

theorem norm_exp_apply_sub_le (firstGenerator secondGenerator : H →L[ℝ] H)
    (commuting : Commute firstGenerator secondGenerator)
    (firstContraction : ∀ time : ℝ, 0 ≤ time →
      ‖NormedSpace.exp ((-time) • firstGenerator)‖ ≤ 1)
    (secondContraction : ∀ time : ℝ, 0 ≤ time →
      ‖NormedSpace.exp ((-time) • secondGenerator)‖ ≤ 1)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (values : H) :
    ‖NormedSpace.exp ((-time) • firstGenerator) values -
      NormedSpace.exp ((-time) • secondGenerator) values‖ ≤
      time * ‖firstGenerator values - secondGenerator values‖ := by
  have firstApplyBound (parameter : ℝ) (parameterBounds : parameter ∈ Set.Icc 0 time)
      (vector : H) :
      ‖NormedSpace.exp ((parameter - time) • firstGenerator) vector‖ ≤ ‖vector‖ := by
    have operatorBound : ‖NormedSpace.exp ((parameter - time) • firstGenerator)‖ ≤ 1 := by
      simpa only [neg_sub] using
        firstContraction (time - parameter) (sub_nonneg.mpr parameterBounds.2)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right operatorBound (norm_nonneg vector))
  have secondApplyBound (parameter : ℝ) (parameterNonnegative : 0 ≤ parameter)
      (vector : H) :
      ‖NormedSpace.exp ((-parameter) • secondGenerator) vector‖ ≤ ‖vector‖ := by
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (secondContraction parameter parameterNonnegative) (norm_nonneg vector))
  have derivativeBound : ∀ parameter ∈ Set.Ico 0 time,
      ‖(NormedSpace.exp ((parameter - time) • firstGenerator) *
        NormedSpace.exp ((-parameter) • secondGenerator))
          (firstGenerator values - secondGenerator values)‖ ≤
      ‖firstGenerator values - secondGenerator values‖ := by
    intro parameter parameterBounds
    exact (firstApplyBound parameter ⟨parameterBounds.1, parameterBounds.2.le⟩ _).trans
      (secondApplyBound parameter parameterBounds.1 _)
  have comparison := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun parameter (_ : parameter ∈ Set.Icc 0 time) =>
      (interpolation_hasDerivAt firstGenerator secondGenerator commuting time parameter values).hasDerivWithinAt)
    derivativeBound time ⟨timeNonnegative, le_rfl⟩
  simpa only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, zero_sub, neg_zero,
    mul_one, sub_zero, norm_sub_rev, mul_comm] using comparison

theorem norm_exp_apply_sub_self_le (generator : H →L[ℝ] H)
    (contraction : ∀ time : ℝ, 0 ≤ time →
      ‖NormedSpace.exp ((-time) • generator)‖ ≤ 1)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (values : H) :
    ‖NormedSpace.exp ((-time) • generator) values - values‖ ≤
      time * ‖generator values‖ := by
  have zeroContraction : ∀ parameter : ℝ, 0 ≤ parameter →
      ‖NormedSpace.exp ((-parameter) • (0 : H →L[ℝ] H))‖ ≤ 1 := by
    intro parameter _
    simpa only [smul_zero, NormedSpace.exp_zero] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := H))
  simpa using norm_exp_apply_sub_le generator 0 (Commute.zero_right generator)
    contraction zeroContraction time timeNonnegative values

#print axioms interpolation_hasDerivAt
#print axioms norm_exp_apply_sub_le
#print axioms norm_exp_apply_sub_self_le

end IGS.Sec31.BoundedSemigroupComparison
