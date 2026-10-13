import RequestProject.Section31.PoissonizedWalkMoments
import RequestProject.Section31.BoundedSemigroupComparison
import RequestProject.Section31.EIGSNativeSemigroup
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.Order.Field

/-! Genuine floor-time comparison for a bounded contraction. The two errors
are the proved Poisson Chernoff bound and the actual exponential's time
increment bound. The coefficient vanishes as the jump rate tends to infinity. -/

namespace IGS.Sec31.PoissonizedWalk

open Filter Topology

section Hilbert

variable {Space : Type*} [NormedAddCommGroup Space]
    [InnerProductSpace ℝ Space] [CompleteSpace Space]

noncomputable local instance : NormedAlgebra ℚ (Space →L[ℝ] Space) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

omit [CompleteSpace Space] in
theorem contraction_difference_nonnegative (transition : Space →L[ℝ] Space)
    (contraction : ‖transition‖ ≤ 1) (values : Space) :
    0 ≤ inner ℝ ((1 - transition) values) values := by
  have applicationBound : ‖transition values‖ ≤ ‖values‖ :=
    (transition.le_opNorm values).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right contraction (norm_nonneg values))
  have pairingBound := real_inner_le_norm (transition values) values
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    inner_sub_left, real_inner_self_eq_norm_sq]
  nlinarith [mul_le_mul_of_nonneg_right applicationBound (norm_nonneg values)]

theorem contraction_exponential_scalar_difference_le
    (transition : Space →L[ℝ] Space) (contraction : ‖transition‖ ≤ 1)
    (first second : ℝ) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) (values : Space) :
    ‖NormedSpace.exp ((-first) • (1 - transition)) values -
      NormedSpace.exp ((-second) • (1 - transition)) values‖ ≤
        |first - second| * ‖(1 - transition) values‖ := by
  have scaledNonnegative (scalar : ℝ) (scalarNonnegative : 0 ≤ scalar)
      (vector : Space) :
      0 ≤ inner ℝ ((scalar • (1 - transition)) vector) vector := by
    simpa only [ContinuousLinearMap.smul_apply, real_inner_smul_left] using
      mul_nonneg scalarNonnegative
        (contraction_difference_nonnegative transition contraction vector)
  have comparison := BoundedSemigroupComparison.norm_exp_apply_sub_le
    (first • (1 - transition)) (second • (1 - transition))
    (((Commute.refl (1 - transition)).smul_left first).smul_right second)
    (BoundedSemigroupEnergy.exp_operator_norm_le_of_nonnegative _
      (scaledNonnegative first firstNonnegative))
    (BoundedSemigroupEnergy.exp_operator_norm_le_of_nonnegative _
      (scaledNonnegative second secondNonnegative))
    1 zero_le_one values
  simpa only [smul_smul, neg_one_mul, one_mul, ContinuousLinearMap.smul_apply,
    ← sub_smul, norm_smul, Real.norm_eq_abs] using comparison

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
  have timeComparison := contraction_exponential_scalar_difference_le
    transition contraction (Nat.floor (time * rate)) (time * rate)
    (Nat.cast_nonneg _) (mul_nonneg timeNonnegative ratePositive.le) values
  have gapBound : |(Nat.floor (time * rate) : ℝ) - time * rate| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr floorBound)]
    linarith
  have boundedTimeComparison := timeComparison.trans
    (mul_le_mul_of_nonneg_right gapBound (norm_nonneg ((1 - transition) values)))
  have poissonComparison := discrete_power_poisson_comparison
    transition contraction values (Nat.floor (time * rate))
  have defectNorm : ‖transition values - values‖ = ‖(1 - transition) values‖ := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      norm_sub_rev]
  rw [defectNorm, norm_sub_rev] at poissonComparison
  have triangle := dist_triangle ((transition ^ Nat.floor (time * rate)) values)
    (NormedSpace.exp ((-(Nat.floor (time * rate) : ℝ)) • (1 - transition)) values)
    (NormedSpace.exp ((-(time * rate)) • (1 - transition)) values)
  simp only [dist_eq_norm] at triangle
  have generatorNorm : ‖(rate • (1 - transition)) values‖ =
      rate * ‖(1 - transition) values‖ := by
    rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos ratePositive]
  rw [generatorNorm]
  have cancellation : ((Real.sqrt (Nat.floor (time * rate)) + 1) / rate) *
      (rate * ‖(1 - transition) values‖) =
      (Real.sqrt (Nat.floor (time * rate)) + 1) * ‖(1 - transition) values‖ := by
    field_simp [ne_of_gt ratePositive]
  rw [cancellation]
  linarith

end Hilbert

theorem rounding_coefficient_nonnegative (time rate : ℝ) (ratePositive : 0 < rate) :
    0 ≤ (Real.sqrt (Nat.floor (time * rate)) + 1) / rate :=
  div_nonneg (by positivity) ratePositive.le

theorem rounding_coefficient_le (time rate : ℝ)
    (timeNonnegative : 0 ≤ time) (ratePositive : 0 < rate) :
    (Real.sqrt (Nat.floor (time * rate)) + 1) / rate ≤
      Real.sqrt (time / rate) + 1 / rate := by
  have floorBound := Nat.floor_le (mul_nonneg timeNonnegative ratePositive.le)
  have quotientBound : (Nat.floor (time * rate) : ℝ) / rate ^ 2 ≤ time / rate := by
    apply (div_le_iff₀ (sq_pos_of_pos ratePositive)).mpr
    calc
      (Nat.floor (time * rate) : ℝ) ≤ time * rate := floorBound
      _ = time / rate * rate ^ 2 := by field_simp [ne_of_gt ratePositive]
  have sqrtBound := Real.sqrt_le_sqrt quotientBound
  rw [Real.sqrt_div (Nat.cast_nonneg _) (rate ^ 2),
    Real.sqrt_sq ratePositive.le] at sqrtBound
  rw [add_div]
  linarith

theorem rounding_coefficient_tendsto_zero
    {Index : Type*} {filter : Filter Index} (rate : Index → ℝ)
    (rateLimit : Tendsto rate filter atTop) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    Tendsto (fun index =>
      (Real.sqrt (Nat.floor (time * rate index)) + 1) / rate index)
      filter (𝓝 0) := by
  have inverseLimit : Tendsto (fun index => (rate index)⁻¹) filter (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp rateLimit
  have quotientLimit : Tendsto (fun index => time / rate index) filter (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul inverseLimit
  have upperLimit : Tendsto (fun index =>
      Real.sqrt (time / rate index) + 1 / rate index) filter (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero, one_div, zero_add] using
      quotientLimit.sqrt.add inverseLimit
  have eventuallyPositive : ∀ᶠ index in filter, 0 < rate index :=
    rateLimit.eventually (eventually_gt_atTop (0 : ℝ))
  apply squeeze_zero'
    (eventuallyPositive.mono (fun index positive =>
      rounding_coefficient_nonnegative time (rate index) positive))
    (eventuallyPositive.mono (fun index positive =>
      rounding_coefficient_le time (rate index) timeNonnegative positive)) upperLimit

#print axioms contraction_difference_nonnegative
#print axioms contraction_exponential_scalar_difference_le
#print axioms discrete_power_floor_poisson_comparison
#print axioms rounding_coefficient_nonnegative
#print axioms rounding_coefficient_le
#print axioms rounding_coefficient_tendsto_zero

end IGS.Sec31.PoissonizedWalk
