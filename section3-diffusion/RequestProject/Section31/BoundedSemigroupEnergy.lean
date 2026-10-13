import RequestProject.Section31.BoundedSemigroupIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Energy dissipation for the actual bounded exponential. The argument uses
derivatives and interval integrals, without a spectral representation. -/

namespace IGS.Sec31.BoundedSemigroupEnergy

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

theorem exp_apply_hasDerivAt (generator : H →L[ℝ] H) (values : H) (time : ℝ) :
    HasDerivAt (fun parameter : ℝ => NormedSpace.exp ((-parameter) • generator) values)
      (-(generator (NormedSpace.exp ((-time) • generator) values))) time := by
  have commuting : Commute generator (NormedSpace.exp ((-time) • generator)) :=
    ((Commute.refl generator).smul_right (-time)).exp_right
  have evaluation := congrArg (fun operator : H →L[ℝ] H => operator values) commuting.eq
  simp only [ContinuousLinearMap.mul_apply] at evaluation
  simpa only [evaluation] using
    BoundedSemigroupIntegral.exp_apply_hasDerivAt generator values time

theorem norm_sq_hasDerivAt (generator : H →L[ℝ] H) (values : H) (time : ℝ) :
    HasDerivAt (fun parameter : ℝ => ‖NormedSpace.exp ((-parameter) • generator) values‖ ^ 2)
      (-2 * inner ℝ (generator (NormedSpace.exp ((-time) • generator) values))
        (NormedSpace.exp ((-time) • generator) values)) time := by
  have derivative := (exp_apply_hasDerivAt generator values time).inner ℝ
    (exp_apply_hasDerivAt generator values time)
  simp only [real_inner_self_eq_norm_sq, inner_neg_left, inner_neg_right] at derivative
  rw [real_inner_comm (generator (NormedSpace.exp ((-time) • generator) values))
    (NormedSpace.exp ((-time) • generator) values)] at derivative
  convert derivative using 1 <;> ring

theorem energy_hasDerivAt (generator : H →L[ℝ] H) (selfAdjoint : IsSelfAdjoint generator)
    (values : H) (time : ℝ) :
    HasDerivAt (fun parameter : ℝ =>
      inner ℝ (generator (NormedSpace.exp ((-parameter) • generator) values))
        (NormedSpace.exp ((-parameter) • generator) values))
      (-2 * ‖generator (NormedSpace.exp ((-time) • generator) values)‖ ^ 2) time := by
  have derivative := (generator.hasFDerivAt.comp_hasDerivAt time
    (exp_apply_hasDerivAt generator values time)).inner ℝ
      (exp_apply_hasDerivAt generator values time)
  simp only [Function.comp_def, map_neg, inner_neg_left, inner_neg_right] at derivative
  have symmetryIdentity :
      inner ℝ (generator (generator (NormedSpace.exp ((-time) • generator) values)))
          (NormedSpace.exp ((-time) • generator) values) =
        inner ℝ (generator (NormedSpace.exp ((-time) • generator) values))
          (generator (NormedSpace.exp ((-time) • generator) values)) :=
    selfAdjoint.isSymmetric (generator (NormedSpace.exp ((-time) • generator) values))
      (NormedSpace.exp ((-time) • generator) values)
  rw [symmetryIdentity] at derivative
  simp only [real_inner_self_eq_norm_sq] at derivative
  convert derivative using 1 <;> ring

theorem energy_antitone (generator : H →L[ℝ] H) (selfAdjoint : IsSelfAdjoint generator)
    (values : H) : Antitone (fun time : ℝ =>
      inner ℝ (generator (NormedSpace.exp ((-time) • generator) values))
        (NormedSpace.exp ((-time) • generator) values)) := by
  apply antitone_of_hasDerivAt_nonpos (energy_hasDerivAt generator selfAdjoint values)
  intro time
  have squareNonnegative := sq_nonneg ‖generator (NormedSpace.exp ((-time) • generator) values)‖
  dsimp
  linarith

theorem norm_sq_dissipation (generator : H →L[ℝ] H) (values : H) (time : ℝ) :
    ‖NormedSpace.exp ((-time) • generator) values‖ ^ 2 - ‖values‖ ^ 2 =
      -2 * ∫ parameter in (0 : ℝ)..time,
        inner ℝ (generator (NormedSpace.exp ((-parameter) • generator) values))
          (NormedSpace.exp ((-parameter) • generator) values) := by
  have orbitContinuous : Continuous (fun parameter : ℝ =>
      NormedSpace.exp ((-parameter) • generator) values) :=
    (NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)).clm_apply
      continuous_const
  have energyContinuous : Continuous (fun parameter : ℝ =>
      inner ℝ (generator (NormedSpace.exp ((-parameter) • generator) values))
        (NormedSpace.exp ((-parameter) • generator) values)) :=
    (generator.continuous.comp orbitContinuous).inner orbitContinuous
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun parameter (_ : parameter ∈ Set.uIcc (0 : ℝ) time) =>
      norm_sq_hasDerivAt generator values parameter)
    ((continuous_const.mul energyContinuous).intervalIntegrable 0 time)
  rw [intervalIntegral.integral_const_mul] at identity
  simpa only [neg_zero, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply]
    using identity.symm

theorem energy_time_bound (generator : H →L[ℝ] H) (selfAdjoint : IsSelfAdjoint generator)
    (values : H) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    2 * time * inner ℝ (generator (NormedSpace.exp ((-time) • generator) values))
      (NormedSpace.exp ((-time) • generator) values) ≤ ‖values‖ ^ 2 := by
  have orbitContinuous : Continuous (fun parameter : ℝ =>
      NormedSpace.exp ((-parameter) • generator) values) :=
    (NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)).clm_apply
      continuous_const
  have energyContinuous : Continuous (fun parameter : ℝ =>
      inner ℝ (generator (NormedSpace.exp ((-parameter) • generator) values))
        (NormedSpace.exp ((-parameter) • generator) values)) :=
    (generator.continuous.comp orbitContinuous).inner orbitContinuous
  have comparison := intervalIntegral.integral_mono_on (μ := volume) timeNonnegative
    (continuous_const.intervalIntegrable 0 time) (energyContinuous.intervalIntegrable 0 time)
    (fun parameter (parameterBounds : parameter ∈ Set.Icc 0 time) =>
      energy_antitone generator selfAdjoint values parameterBounds.2)
  rw [intervalIntegral.integral_const] at comparison
  simp only [sub_zero, smul_eq_mul] at comparison
  have dissipation := norm_sq_dissipation generator values time
  nlinarith [sq_nonneg ‖NormedSpace.exp ((-time) • generator) values‖]

end IGS.Sec31.BoundedSemigroupEnergy

#print axioms IGS.Sec31.BoundedSemigroupEnergy.exp_apply_hasDerivAt
#print axioms IGS.Sec31.BoundedSemigroupEnergy.norm_sq_hasDerivAt
#print axioms IGS.Sec31.BoundedSemigroupEnergy.energy_hasDerivAt
#print axioms IGS.Sec31.BoundedSemigroupEnergy.energy_antitone
#print axioms IGS.Sec31.BoundedSemigroupEnergy.norm_sq_dissipation
#print axioms IGS.Sec31.BoundedSemigroupEnergy.energy_time_bound
