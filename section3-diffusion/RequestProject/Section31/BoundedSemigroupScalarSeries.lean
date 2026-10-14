import RequestProject.Section31.BoundedSemigroupPowerBound

/-! The exact centered scalar exponential series of a bounded generator.
This identity holds for every real increment. Positivity and self-adjointness
are needed for the uniform coefficient bounds in the predecessor, not for this
algebraic series identity. Candidate source, awaiting whole-file compilation. -/

namespace IGS.Sec31.BoundedSemigroupEnergy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

theorem bounded_generator_scalar_centered_series
    (generator : H →L[ℝ] H) (first second : H) (center increment : ℝ) :
    HasSum (fun power : ℕ =>
      ((-1 : ℝ) ^ power *
        inner ℝ first ((generator ^ power * NormedSpace.exp ((-center) • generator)) second) /
          (power.factorial : ℝ)) * increment ^ power)
      (inner ℝ first (NormedSpace.exp ((-(center + increment)) • generator) second)) := by
  have operatorSum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((-increment) • generator)
  have vectorSum := operatorSum.map
    (ContinuousLinearMap.apply ℝ H (NormedSpace.exp ((-center) • generator) second))
    (ContinuousLinearMap.apply ℝ H (NormedSpace.exp ((-center) • generator) second)).continuous
  have scalarSum := vectorSum.map (innerSL ℝ first) (innerSL ℝ first).continuous
  have termEquality (power : ℕ) :
      inner ℝ first (((power.factorial : ℝ)⁻¹ • ((-increment) • generator) ^ power)
        (NormedSpace.exp ((-center) • generator) second)) =
      ((-1 : ℝ) ^ power *
        inner ℝ first ((generator ^ power * NormedSpace.exp ((-center) • generator)) second) /
          (power.factorial : ℝ)) * increment ^ power := by
    rw [smul_pow, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      inner_smul_right, inner_smul_right, ContinuousLinearMap.mul_apply]
    rw [show (-increment : ℝ) = (-1) * increment by ring, mul_pow]
    ring
  have commuting : Commute ((-increment) • generator) ((-center) • generator) :=
    ((Commute.refl generator).smul_left (-increment)).smul_right (-center)
  have exponentEquality : ((-increment) • generator) + ((-center) • generator) =
      (-(center + increment)) • generator := by
    rw [← add_smul]
    congr 1
    ring
  have productEquality : NormedSpace.exp ((-increment) • generator) *
      NormedSpace.exp ((-center) • generator) =
      NormedSpace.exp ((-(center + increment)) • generator) := by
    rw [← NormedSpace.exp_add_of_commute commuting, exponentEquality]
  simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply,
    termEquality, ← ContinuousLinearMap.mul_apply, productEquality] using scalarSum

end IGS.Sec31.BoundedSemigroupEnergy

#print axioms IGS.Sec31.BoundedSemigroupEnergy.bounded_generator_scalar_centered_series
