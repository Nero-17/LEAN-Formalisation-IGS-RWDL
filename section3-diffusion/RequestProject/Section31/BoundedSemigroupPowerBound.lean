import RequestProject.Section31.BoundedSemigroupDerivativeBound
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Uniform factorial and scalar-coefficient bounds for positive self-adjoint
bounded generators. The equal-time factorization makes the estimates independent
of the norm of the generator. These are candidate leaves for the actual Yosida
scalar-power-series argument; no analyticity of the strong limit is assumed.
Whole-file compilation remains pending. -/

namespace IGS.Sec31.BoundedSemigroupEnergy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

theorem positive_exp_norm_le_one
    (generator : H →L[ℝ] H)
    (nonnegative : ∀ values, 0 ≤ inner ℝ (generator values) values)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    ‖NormedSpace.exp ((-time) • generator)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro values
  have decreasing : Antitone (fun parameter : ℝ =>
      ‖NormedSpace.exp ((-parameter) • generator) values‖ ^ 2) := by
    apply antitone_of_hasDerivAt_nonpos (norm_sq_hasDerivAt generator values)
    intro parameter
    have pairingNonnegative := nonnegative (NormedSpace.exp ((-parameter) • generator) values)
    dsimp
    linarith
  have squareBound := decreasing timeNonnegative
  simp only [neg_zero, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply] at squareBound
  simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg values)).mp squareBound

theorem generator_power_exp_factorization
    (generator : H →L[ℝ] H) (time : ℝ) (power : ℕ) (powerPositive : 0 < power) :
    (generator * NormedSpace.exp ((-(time / (power : ℝ))) • generator)) ^ power =
      generator ^ power * NormedSpace.exp ((-time) • generator) := by
  have commuting : Commute generator
      (NormedSpace.exp ((-(time / (power : ℝ))) • generator)) :=
    ((Commute.refl generator).smul_right (-(time / (power : ℝ)))).exp_right
  have powerRealNonzero : (power : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt powerPositive
  have scaleIdentity : power • ((-(time / (power : ℝ))) • generator) = (-time) • generator := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp [powerRealNonzero]
  rw [commuting.mul_pow, ← NormedSpace.exp_nsmul, scaleIdentity]

theorem generator_power_exp_norm_le
    (generator : H →L[ℝ] H) (selfAdjoint : IsSelfAdjoint generator)
    (nonnegative : ∀ values, 0 ≤ inner ℝ (generator values) values)
    (time : ℝ) (timePositive : 0 < time) (power : ℕ) (powerPositive : 0 < power) :
    ‖generator ^ power * NormedSpace.exp ((-time) • generator)‖ ≤
      ((power : ℝ) / time) ^ power := by
  have powerRealPositive : (0 : ℝ) < power := by exact_mod_cast powerPositive
  have divisionPositive : 0 < time / (power : ℝ) := div_pos timePositive powerRealPositive
  calc
    _ = ‖(generator * NormedSpace.exp ((-(time / (power : ℝ))) • generator)) ^ power‖ :=
      congrArg norm (generator_power_exp_factorization generator time power powerPositive).symm
    _ ≤ ‖generator * NormedSpace.exp ((-(time / (power : ℝ))) • generator)‖ ^ power :=
      norm_pow_le' _ powerPositive
    _ ≤ ((time / (power : ℝ))⁻¹) ^ power := by
      exact pow_le_pow_left₀ (norm_nonneg _)
        (generator_exp_norm_le generator selfAdjoint nonnegative _ divisionPositive) power
    _ = ((power : ℝ) / time) ^ power := by rw [inv_div]

theorem generator_power_exp_factorial_bound
    (generator : H →L[ℝ] H) (selfAdjoint : IsSelfAdjoint generator)
    (nonnegative : ∀ values, 0 ≤ inner ℝ (generator values) values)
    (time : ℝ) (timePositive : 0 < time) (power : ℕ) :
    ‖generator ^ power * NormedSpace.exp ((-time) • generator)‖ / (power.factorial : ℝ) ≤
      (Real.exp 1 / time) ^ power := by
  rcases Nat.eq_zero_or_pos power with rfl | powerPositive
  · simpa only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, div_one] using
      positive_exp_norm_le_one generator nonnegative time timePositive.le
  · have exponentialBound := Real.pow_div_factorial_le_exp (power : ℝ) (Nat.cast_nonneg power : (0 : ℝ) ≤ power) power
    calc
      _ ≤ (((power : ℝ) / time) ^ power) / (power.factorial : ℝ) :=
        div_le_div_of_nonneg_right
          (generator_power_exp_norm_le generator selfAdjoint nonnegative time timePositive power powerPositive)
          (Nat.cast_nonneg _)
      _ = ((power : ℝ) ^ power / (power.factorial : ℝ)) / time ^ power := by rw [div_pow]; ring
      _ ≤ Real.exp (power : ℝ) / time ^ power :=
        div_le_div_of_nonneg_right exponentialBound (pow_nonneg timePositive.le _)
      _ = (Real.exp 1 / time) ^ power := by
        rw [div_pow, ← Real.exp_nat_mul, mul_one]

theorem generator_scalar_coefficient_bound
    (generator : H →L[ℝ] H) (selfAdjoint : IsSelfAdjoint generator)
    (nonnegative : ∀ values, 0 ≤ inner ℝ (generator values) values)
    (first second : H) (time : ℝ) (timePositive : 0 < time) (power : ℕ) :
    |(-1 : ℝ) ^ power *
      inner ℝ first ((generator ^ power * NormedSpace.exp ((-time) • generator)) second) /
        (power.factorial : ℝ)| ≤
      (‖first‖ * ‖second‖) * (Real.exp 1 / time) ^ power := by
  have factorialPositive : (0 : ℝ) < power.factorial := by exact_mod_cast power.factorial_pos
  simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos factorialPositive]
  calc
    _ ≤ (‖first‖ *
        (‖generator ^ power * NormedSpace.exp ((-time) • generator)‖ * ‖second‖)) /
          (power.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ factorialPositive.le
      exact (abs_real_inner_le_norm first _).trans
        (mul_le_mul_of_nonneg_left
          ((generator ^ power * NormedSpace.exp ((-time) • generator)).le_opNorm second)
          (norm_nonneg first))
    _ = (‖first‖ * ‖second‖) *
        (‖generator ^ power * NormedSpace.exp ((-time) • generator)‖ / (power.factorial : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (generator_power_exp_factorial_bound generator selfAdjoint nonnegative time timePositive power)
      (mul_nonneg (norm_nonneg first) (norm_nonneg second))

end IGS.Sec31.BoundedSemigroupEnergy

#print axioms IGS.Sec31.BoundedSemigroupEnergy.positive_exp_norm_le_one
#print axioms IGS.Sec31.BoundedSemigroupEnergy.generator_power_exp_factorization
#print axioms IGS.Sec31.BoundedSemigroupEnergy.generator_power_exp_norm_le
#print axioms IGS.Sec31.BoundedSemigroupEnergy.generator_power_exp_factorial_bound
#print axioms IGS.Sec31.BoundedSemigroupEnergy.generator_scalar_coefficient_bound
