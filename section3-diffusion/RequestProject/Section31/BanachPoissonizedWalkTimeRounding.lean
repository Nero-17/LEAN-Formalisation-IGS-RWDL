import RequestProject.Section31.PoissonizedWalkMoments
import RequestProject.Section31.BoundedSemigroupComparison
import RequestProject.Section31.EIGSDiscreteFiniteObservations

/-! De-Poissonization in a Banach space, including finite vertex functions
with their supremum norm. The only operator input is norm contraction of
the discrete transition. Exponential contraction is proved from the actual
nonnegative Poisson weights summing to one; no Hilbert space is required.
The native finite graph transition must still supply its supremum-norm
contraction when these generic estimates are applied. -/

namespace IGS.Sec31.PoissonizedWalk.Banach

open Filter Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [CompleteSpace Space]

noncomputable local instance : NormedAlgebra ℚ (Space →L[ℝ] Space) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- The Poisson mixture of powers of a contraction is a contraction. -/
theorem exponential_apply_norm_le (transition : Space →L[ℝ] Space)
    (contraction : ‖transition‖ ≤ 1) (parameter : ℝ)
    (parameterNonnegative : 0 ≤ parameter) (values : Space) :
    ‖NormedSpace.exp ((-parameter) • (1 - transition)) values‖ ≤ ‖values‖ := by
  have mixture := apply_hasSum transition 1 parameter values
  have weightSum := (weights_hasSum parameter).mul_right ‖values‖
  have mixtureBound := mixture.norm_le_of_bounded weightSum (fun jumps => by
    simp only [mul_one, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (weight_nonnegative parameter parameterNonnegative jumps)]
    exact mul_le_mul_of_nonneg_left
      (contraction_power_apply_le transition contraction jumps values)
      (weight_nonnegative parameter parameterNonnegative jumps))
  simpa only [one_smul, one_mul] using mixtureBound

theorem exponential_norm_le (transition : Space →L[ℝ] Space)
    (contraction : ‖transition‖ ≤ 1) (parameter : ℝ)
    (parameterNonnegative : 0 ≤ parameter) :
    ‖NormedSpace.exp ((-parameter) • (1 - transition))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro values
  simpa only [one_mul] using
    exponential_apply_norm_le transition contraction parameter parameterNonnegative values

/-- Comparison of two actual exponential times uses the just-proved
Poisson contraction and the bounded-generator interpolation identity. -/
theorem exponential_scalar_difference_le (transition : Space →L[ℝ] Space)
    (contraction : ‖transition‖ ≤ 1)
    (first second : ℝ) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) (values : Space) :
    ‖NormedSpace.exp ((-first) • (1 - transition)) values -
      NormedSpace.exp ((-second) • (1 - transition)) values‖ ≤
        |first - second| * ‖(1 - transition) values‖ := by
  have scaledContraction (scalar : ℝ) (scalarNonnegative : 0 ≤ scalar) :
      ∀ parameter : ℝ, 0 ≤ parameter →
        ‖NormedSpace.exp ((-parameter) • (scalar • (1 - transition)))‖ ≤ 1 := by
    intro parameter parameterNonnegative
    simpa only [smul_smul, neg_mul] using
      exponential_norm_le transition contraction (parameter * scalar)
        (mul_nonneg parameterNonnegative scalarNonnegative)
  have comparison := BoundedSemigroupComparison.norm_exp_apply_sub_le
    (first • (1 - transition)) (second • (1 - transition))
    (((Commute.refl (1 - transition)).smul_left first).smul_right second)
    (scaledContraction first firstNonnegative)
    (scaledContraction second secondNonnegative) 1 zero_le_one values
  simpa only [smul_smul, neg_one_mul, one_mul, ContinuousLinearMap.smul_apply,
    ← sub_smul, norm_smul, Real.norm_eq_abs] using comparison

/-- Floor-clock comparison in the supremum norm or any other Banach norm. -/
theorem discrete_power_floor_poisson_comparison
    (transition : Space →L[ℝ] Space) (contraction : ‖transition‖ ≤ 1)
    (rate : ℝ) (ratePositive : 0 < rate)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (values : Space) :
    ‖(transition ^ Nat.floor (time * rate)) values -
      NormedSpace.exp ((-(time * rate)) • (1 - transition)) values‖ ≤
      ((Real.sqrt (Nat.floor (time * rate)) + 1) / rate) *
        ‖(rate • (1 - transition)) values‖ := by
  have floorBound := Nat.floor_le (mul_nonneg timeNonnegative ratePositive.le)
  have floorGap := Nat.lt_floor_add_one (time * rate)
  have timeComparison := exponential_scalar_difference_le transition contraction
    (Nat.floor (time * rate)) (time * rate)
    (Nat.cast_nonneg _) (mul_nonneg timeNonnegative ratePositive.le) values
  have gapBound : |(Nat.floor (time * rate) : ℝ) - time * rate| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr floorBound)]
    linarith
  have boundedTimeComparison := timeComparison.trans
    (mul_le_mul_of_nonneg_right gapBound (norm_nonneg ((1 - transition) values)))
  have poissonComparison :=
    IGS.Sec31.PoissonizedWalk.discrete_power_poisson_comparison transition contraction values
      (Nat.floor (time * rate))
  have defectNorm : ‖transition values - values‖ = ‖(1 - transition) values‖ := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, norm_sub_rev]
  rw [defectNorm, norm_sub_rev] at poissonComparison
  have triangle := dist_triangle ((transition ^ Nat.floor (time * rate)) values)
    (NormedSpace.exp ((-(Nat.floor (time * rate) : ℝ)) • (1 - transition)) values)
    (NormedSpace.exp ((-(time * rate)) • (1 - transition)) values)
  simp only [dist_eq_norm] at triangle
  have generatorNorm : ‖(rate • (1 - transition)) values‖ =
      rate * ‖(1 - transition) values‖ := by
    rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos ratePositive]
  rw [generatorNorm]
  have cancellation : ((Real.sqrt (Nat.floor (time * rate)) + 1) / rate) *
      (rate * ‖(1 - transition) values‖) =
      (Real.sqrt (Nat.floor (time * rate)) + 1) * ‖(1 - transition) values‖ := by
    field_simp [ratePositive.ne']
  rw [cancellation]
  linarith

/-- Actual multi-time transitions use differences of absolute floors.
The additional one-step error is retained in the coefficient `+ 2`. -/
theorem discrete_power_absolute_floor_increment_poisson_comparison
    (transition : Space →L[ℝ] Space) (contraction : ‖transition‖ ≤ 1)
    (rate : ℝ) (ratePositive : 0 < rate)
    (first second : ℝ) (firstNonnegative : 0 ≤ first)
    (ordered : first ≤ second) (values : Space) :
    ‖(transition ^ (Nat.floor (second * rate) - Nat.floor (first * rate))) values -
      NormedSpace.exp ((-((second - first) * rate)) • (1 - transition)) values‖ ≤
      ((Real.sqrt (Nat.floor ((second - first) * rate)) + 2) / rate) *
        ‖(rate • (1 - transition)) values‖ := by
  have incrementComparison :=
    IGS.Sec31.PoissonizedWalk.contraction_floor_increment_comparison transition contraction
      rate first second ratePositive.le firstNonnegative ordered values
  have poissonComparison := discrete_power_floor_poisson_comparison transition contraction rate
    ratePositive (second - first) (sub_nonneg.mpr ordered) values
  have triangle := dist_triangle
    ((transition ^ (Nat.floor (second * rate) - Nat.floor (first * rate))) values)
    ((transition ^ Nat.floor ((second - first) * rate)) values)
    (NormedSpace.exp ((-((second - first) * rate)) • (1 - transition)) values)
  simp only [dist_eq_norm] at triangle
  have defectNorm : ‖transition values - values‖ =
      rate⁻¹ * ‖(rate • (1 - transition)) values‖ := by
    rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos ratePositive,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, norm_sub_rev,
      ← mul_assoc, inv_mul_cancel₀ ratePositive.ne', one_mul]
  calc
    _ ≤ ‖(transition ^ (Nat.floor (second * rate) - Nat.floor (first * rate))) values -
        (transition ^ Nat.floor ((second - first) * rate)) values‖ +
      ‖(transition ^ Nat.floor ((second - first) * rate)) values -
        NormedSpace.exp ((-((second - first) * rate)) • (1 - transition)) values‖ := triangle
    _ ≤ ‖transition values - values‖ +
      ((Real.sqrt (Nat.floor ((second - first) * rate)) + 1) / rate) *
        ‖(rate • (1 - transition)) values‖ := add_le_add incrementComparison poissonComparison
    _ = _ := by
      rw [defectNorm]
      ring

end IGS.Sec31.PoissonizedWalk.Banach

#print axioms IGS.Sec31.PoissonizedWalk.Banach.exponential_apply_norm_le
#print axioms IGS.Sec31.PoissonizedWalk.Banach.exponential_norm_le
#print axioms IGS.Sec31.PoissonizedWalk.Banach.exponential_scalar_difference_le
#print axioms IGS.Sec31.PoissonizedWalk.Banach.discrete_power_floor_poisson_comparison
#print axioms IGS.Sec31.PoissonizedWalk.Banach.discrete_power_absolute_floor_increment_poisson_comparison
