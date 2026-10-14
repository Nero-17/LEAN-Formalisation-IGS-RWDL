import RequestProject.Section31.BoundedSemigroupEnergy

/-! An energy-controlled increment for the genuine bounded-operator
exponential. Self-adjointness moves half the orbit to the other argument;
the previously proved energy monotonicity bounds the resulting pairing.
The scalar fundamental theorem of calculus and positivity give the increment
bound without a spectral representation or an assumed increment estimate. -/

namespace IGS.Sec31.BoundedSemigroupEnergyIncrement

open MeasureTheory
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance incrementNormedAlgebraRational : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

theorem generator_exp_pairing_half_energy (generator : H →L[ℝ] H)
    (selfAdjoint : IsSelfAdjoint generator) (values : H) (time : ℝ) :
    inner ℝ (generator (NormedSpace.exp ((-time) • generator) values)) values =
      inner ℝ (generator (NormedSpace.exp ((-(time / 2)) • generator) values))
        (NormedSpace.exp ((-(time / 2)) • generator) values) := by
  have halfSelfAdjoint : IsSelfAdjoint (NormedSpace.exp ((-(time / 2)) • generator)) :=
    ((IsSelfAdjoint.all (-(time / 2))).smul selfAdjoint).exp
  have commuting : Commute ((-(time / 2)) • generator) ((-(time / 2)) • generator) :=
    Commute.refl _
  have exponentEquality : ((-(time / 2)) • generator + (-(time / 2)) • generator) =
      (-time) • generator := by
    rw [← add_smul]
    congr 1
    ring
  have halfSquare := NormedSpace.exp_add_of_commute commuting
  rw [exponentEquality] at halfSquare
  have generatorCommuting : Commute generator (NormedSpace.exp ((-(time / 2)) • generator)) :=
    ((Commute.refl generator).smul_right (-(time / 2))).exp_right
  have commuteOnOrbit := congrArg
    (fun operator : H →L[ℝ] H => operator (NormedSpace.exp ((-(time / 2)) • generator) values))
    generatorCommuting.eq
  simp only [ContinuousLinearMap.mul_apply] at commuteOnOrbit
  rw [halfSquare, ContinuousLinearMap.mul_apply, commuteOnOrbit]
  exact halfSelfAdjoint.isSymmetric
    (generator (NormedSpace.exp ((-(time / 2)) • generator) values)) values

theorem generator_exp_pairing_le_initial_energy (generator : H →L[ℝ] H)
    (selfAdjoint : IsSelfAdjoint generator) (values : H) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    inner ℝ (generator (NormedSpace.exp ((-time) • generator) values)) values ≤
      inner ℝ (generator values) values := by
  rw [generator_exp_pairing_half_energy generator selfAdjoint values time]
  have monotonicity := BoundedSemigroupEnergy.energy_antitone generator selfAdjoint values
    (show (0 : ℝ) ≤ time / 2 by linarith)
  simpa only [neg_zero, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply] using monotonicity

theorem exp_pairing_sub_eq_integral (generator : H →L[ℝ] H) (values : H) (time : ℝ) :
    inner ℝ (NormedSpace.exp ((-time) • generator) values) values - inner ℝ values values =
      -(∫ parameter in (0 : ℝ)..time,
        inner ℝ (generator (NormedSpace.exp ((-parameter) • generator) values)) values) := by
  have derivative (parameter : ℝ) :
      HasDerivAt (fun parameter : ℝ => inner ℝ (NormedSpace.exp ((-parameter) • generator) values) values)
        (-(inner ℝ (generator (NormedSpace.exp ((-parameter) • generator) values)) values)) parameter := by
    have pairingDerivative :=
      (BoundedSemigroupEnergy.exp_apply_hasDerivAt generator values parameter).inner ℝ
        (hasDerivAt_const parameter values)
    simpa only [inner_neg_left, inner_zero_right, add_zero, zero_add] using pairingDerivative
  have orbitContinuous : Continuous (fun parameter : ℝ =>
      NormedSpace.exp ((-parameter) • generator) values) :=
    (NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)).clm_apply continuous_const
  have integrandContinuous : Continuous (fun parameter : ℝ =>
      -(inner ℝ (generator (NormedSpace.exp ((-parameter) • generator) values)) values)) :=
    ((generator.continuous.comp orbitContinuous).inner continuous_const).neg
  have integralIdentity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun parameter (_ : parameter ∈ Set.uIcc (0 : ℝ) time) => derivative parameter)
    (integrandContinuous.intervalIntegrable 0 time)
  rw [intervalIntegral.integral_neg] at integralIdentity
  simpa only [neg_zero, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply] using integralIdentity.symm

theorem positive_exp_apply_sub_self_sq_le (generator : H →L[ℝ] H)
    (selfAdjoint : IsSelfAdjoint generator)
    (nonnegative : ∀ values, 0 ≤ inner ℝ (generator values) values)
    (values : H) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    ‖NormedSpace.exp ((-time) • generator) values - values‖ ^ 2 ≤
      2 * time * inner ℝ (generator values) values := by
  have normDecreasing : Antitone (fun parameter : ℝ =>
      ‖NormedSpace.exp ((-parameter) • generator) values‖ ^ 2) := by
    apply antitone_of_hasDerivAt_nonpos (BoundedSemigroupEnergy.norm_sq_hasDerivAt generator values)
    intro parameter
    have pairingNonnegative := nonnegative (NormedSpace.exp ((-parameter) • generator) values)
    dsimp
    linarith
  have normBound := normDecreasing timeNonnegative
  simp only [neg_zero, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply] at normBound
  have orbitContinuous : Continuous (fun parameter : ℝ =>
      NormedSpace.exp ((-parameter) • generator) values) :=
    (NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)).clm_apply continuous_const
  have pairingContinuous : Continuous (fun parameter : ℝ =>
      inner ℝ (generator (NormedSpace.exp ((-parameter) • generator) values)) values) :=
    (generator.continuous.comp orbitContinuous).inner continuous_const
  have integralBound := intervalIntegral.integral_mono_on (μ := volume) timeNonnegative
    (pairingContinuous.intervalIntegrable 0 time) (continuous_const.intervalIntegrable 0 time)
    (fun parameter (parameterBounds : parameter ∈ Set.Icc 0 time) =>
      generator_exp_pairing_le_initial_energy generator selfAdjoint values parameter parameterBounds.1)
  rw [intervalIntegral.integral_const] at integralBound
  simp only [sub_zero, smul_eq_mul] at integralBound
  have pairingIdentity := exp_pairing_sub_eq_integral generator values time
  rw [real_inner_self_eq_norm_sq] at pairingIdentity
  rw [norm_sub_sq_real]
  nlinarith

end
end IGS.Sec31.BoundedSemigroupEnergyIncrement

#print axioms IGS.Sec31.BoundedSemigroupEnergyIncrement.generator_exp_pairing_half_energy
#print axioms IGS.Sec31.BoundedSemigroupEnergyIncrement.exp_pairing_sub_eq_integral
#print axioms IGS.Sec31.BoundedSemigroupEnergyIncrement.positive_exp_apply_sub_self_sq_le
