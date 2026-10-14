import RequestProject.Section31.BoundedSemigroupEnergy

/-! A uniform first-derivative bound for positive self-adjoint bounded
exponentials. This uses the two dissipation identities and no spectral
representation. It is intended for the already constructed Yosida generators.
The source remains a candidate until its whole-file compiler receipt exists. -/

namespace IGS.Sec31.BoundedSemigroupEnergy

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance derivativeBoundNormedAlgebraRat : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

theorem generator_exp_apply_eq (generator : H →L[ℝ] H) (values : H) (time : ℝ) :
    generator (NormedSpace.exp ((-time) • generator) values) =
      NormedSpace.exp ((-time) • generator) (generator values) := by
  have commuting : Commute generator (NormedSpace.exp ((-time) • generator)) :=
    ((Commute.refl generator).smul_right (-time)).exp_right
  exact congrArg (fun operator : H →L[ℝ] H => operator values) commuting.eq

theorem generator_orbit_norm_sq_antitone
    (generator : H →L[ℝ] H)
    (nonnegative : ∀ values, 0 ≤ inner ℝ (generator values) values)
    (values : H) :
    Antitone (fun time : ℝ =>
      ‖generator (NormedSpace.exp ((-time) • generator) values)‖ ^ 2) := by
  simp only [generator_exp_apply_eq]
  apply antitone_of_hasDerivAt_nonpos (norm_sq_hasDerivAt generator (generator values))
  intro time
  have pairingNonnegative := nonnegative
    (NormedSpace.exp ((-time) • generator) (generator values))
  dsimp
  linarith

theorem energy_dissipation_between
    (generator : H →L[ℝ] H) (selfAdjoint : IsSelfAdjoint generator)
    (values : H) (firstTime lastTime : ℝ) :
    inner ℝ (generator (NormedSpace.exp ((-lastTime) • generator) values))
        (NormedSpace.exp ((-lastTime) • generator) values) -
      inner ℝ (generator (NormedSpace.exp ((-firstTime) • generator) values))
        (NormedSpace.exp ((-firstTime) • generator) values) =
      -2 * ∫ parameter in firstTime..lastTime,
        ‖generator (NormedSpace.exp ((-parameter) • generator) values)‖ ^ 2 := by
  have orbitContinuous : Continuous (fun parameter : ℝ =>
      NormedSpace.exp ((-parameter) • generator) values) :=
    (NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)).clm_apply
      continuous_const
  have squareContinuous : Continuous (fun parameter : ℝ =>
      ‖generator (NormedSpace.exp ((-parameter) • generator) values)‖ ^ 2) :=
    (generator.continuous.comp orbitContinuous).norm.pow 2
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun parameter (_ : parameter ∈ Set.uIcc firstTime lastTime) =>
      energy_hasDerivAt generator selfAdjoint values parameter)
    ((continuous_const.mul squareContinuous).intervalIntegrable firstTime lastTime)
  rw [intervalIntegral.integral_const_mul] at identity
  exact identity.symm

theorem generator_exp_apply_norm_le
    (generator : H →L[ℝ] H) (selfAdjoint : IsSelfAdjoint generator)
    (nonnegative : ∀ values, 0 ≤ inner ℝ (generator values) values)
    (values : H) (time : ℝ) (timePositive : 0 < time) :
    ‖generator (NormedSpace.exp ((-time) • generator) values)‖ ≤ ‖values‖ / time := by
  have orbitContinuous : Continuous (fun parameter : ℝ =>
      NormedSpace.exp ((-parameter) • generator) values) :=
    (NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)).clm_apply
      continuous_const
  have squareContinuous : Continuous (fun parameter : ℝ =>
      ‖generator (NormedSpace.exp ((-parameter) • generator) values)‖ ^ 2) :=
    (generator.continuous.comp orbitContinuous).norm.pow 2
  have comparison := intervalIntegral.integral_mono_on (μ := volume)
    (show time / 2 ≤ time by linarith)
    (continuous_const.intervalIntegrable (time / 2) time)
    (squareContinuous.intervalIntegrable (time / 2) time)
    (fun parameter (parameterBounds : parameter ∈ Set.Icc (time / 2) time) =>
      generator_orbit_norm_sq_antitone generator nonnegative values parameterBounds.2)
  rw [intervalIntegral.integral_const] at comparison
  simp only [smul_eq_mul] at comparison
  have dissipation := energy_dissipation_between generator selfAdjoint values (time / 2) time
  have energyNonnegative := nonnegative (NormedSpace.exp ((-time) • generator) values)
  have halfTimeBound := energy_time_bound generator selfAdjoint values (time / 2)
    (by linarith : 0 ≤ time / 2)
  have firstBound :
      time * ‖generator (NormedSpace.exp ((-time) • generator) values)‖ ^ 2 ≤
        inner ℝ (generator (NormedSpace.exp ((-(time / 2)) • generator) values))
          (NormedSpace.exp ((-(time / 2)) • generator) values) := by
    nlinarith only [comparison, dissipation, energyNonnegative]
  have multiplied := mul_le_mul_of_nonneg_left firstBound timePositive.le
  have squareBound :
      (time * ‖generator (NormedSpace.exp ((-time) • generator) values)‖) ^ 2 ≤
        ‖values‖ ^ 2 := by
    nlinarith only [multiplied, halfTimeBound]
  apply (le_div_iff₀ timePositive).mpr
  have bound := (sq_le_sq₀
    (mul_nonneg timePositive.le
      (norm_nonneg (generator (NormedSpace.exp ((-time) • generator) values))))
    (norm_nonneg values)).mp squareBound
  simpa only [mul_comm] using bound

theorem generator_exp_norm_le
    (generator : H →L[ℝ] H) (selfAdjoint : IsSelfAdjoint generator)
    (nonnegative : ∀ values, 0 ≤ inner ℝ (generator values) values)
    (time : ℝ) (timePositive : 0 < time) :
    ‖generator * NormedSpace.exp ((-time) • generator)‖ ≤ time⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr timePositive.le)
  intro values
  have bound := generator_exp_apply_norm_le generator selfAdjoint nonnegative values time timePositive
  simpa only [ContinuousLinearMap.mul_apply, div_eq_mul_inv, mul_comm] using bound

end IGS.Sec31.BoundedSemigroupEnergy

#print axioms IGS.Sec31.BoundedSemigroupEnergy.generator_exp_apply_eq
#print axioms IGS.Sec31.BoundedSemigroupEnergy.generator_orbit_norm_sq_antitone
#print axioms IGS.Sec31.BoundedSemigroupEnergy.energy_dissipation_between
#print axioms IGS.Sec31.BoundedSemigroupEnergy.generator_exp_apply_norm_le
#print axioms IGS.Sec31.BoundedSemigroupEnergy.generator_exp_norm_le
