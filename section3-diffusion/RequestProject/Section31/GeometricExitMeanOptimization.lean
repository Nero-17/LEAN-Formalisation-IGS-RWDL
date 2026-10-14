import RequestProject.Section31.ContinuousPathBallExit
import RequestProject.Section31.NashTwoScaleOptimization
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace IGS.Sec31
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

theorem continuousPathBallExit_mono_radius {Space : Type*} [MetricSpace Space]
    (path : C(ℝ≥0, Space)) (center : Space) {firstRadius secondRadius : ℝ}
    (ordered : firstRadius ≤ secondRadius) :
    continuousPathBallExit path center firstRadius ≤ continuousPathBallExit path center secondRadius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro time survives
  apply le_of_lt
  apply (time_lt_continuousPathBallExit_iff path center secondRadius time).mpr
  intro observed before
  exact ((time_lt_continuousPathBallExit_iff path center firstRadius time).mp survives observed before).trans_le ordered

theorem geometric_exit_mean_radius_choice (distanceRate timeRate radiusScale upper : ℝ)
    (distanceGreaterThanOne : 1 < distanceRate) (timeGreaterThanOne : 1 < timeRate)
    (radiusScalePositive : 0 < radiusScale) (upperPositive : 0 < upper) :
    ∃ constant cutoff : ℝ, 0 < constant ∧ 0 < cutoff ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ cutoff →
        ∃ level : ℕ, 1 ≤ level ∧ radius ≤ radiusScale * distanceRate⁻¹ ^ level ∧
          upper * timeRate⁻¹ ^ level ≤ constant * radius ^ (Real.log timeRate / Real.log distanceRate) := by
  have distancePositive := zero_lt_one.trans distanceGreaterThanOne
  have timePositive := zero_lt_one.trans timeGreaterThanOne
  let exponent := Real.log timeRate / Real.log distanceRate
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    distanceRate timeRate distanceGreaterThanOne timeGreaterThanOne.le
  let constant := upper * timeRate / radiusScale ^ exponent
  have constantPositive : 0 < constant := div_pos (mul_pos upperPositive timePositive)
    (Real.rpow_pos_of_pos radiusScalePositive exponent)
  refine ⟨constant, radiusScale / distanceRate, constantPositive,
    div_pos radiusScalePositive distancePositive, ?_⟩
  intro radius radiusPositive radiusSmall
  have ratioAtLeastDistance : distanceRate ≤ radiusScale / radius := by
    apply (le_div_iff₀ radiusPositive).mpr
    have bound := (le_div_iff₀ distancePositive).mp radiusSmall
    simpa only [mul_comm] using bound
  obtain ⟨level, lower, upperLevel⟩ := exists_nat_pow_near
    (distanceGreaterThanOne.le.trans ratioAtLeastDistance) distanceGreaterThanOne
  have levelPositive : 1 ≤ level := by
    by_contra zero
    have levelZero : level = 0 := by omega
    subst level
    simp only [pow_zero, zero_add, pow_one] at upperLevel
    exact (not_lt_of_ge ratioAtLeastDistance) upperLevel
  refine ⟨level, levelPositive, ?_, ?_⟩
  · rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos distancePositive level)).mpr
    have bound := (le_div_iff₀ radiusPositive).mp lower
    simpa only [mul_comm] using bound
  · have nextRadius : radiusScale / distanceRate ^ (level + 1) ≤ radius := by
      apply (div_le_iff₀ (pow_pos distancePositive _)).mpr
      have bound := (div_lt_iff₀ radiusPositive).mp upperLevel
      simpa only [mul_comm] using bound.le
    have scalePower : (distanceRate ^ (level + 1)) ^ exponent = timeRate ^ (level + 1) := by
      rw [growthIdentity, ← Real.rpow_mul_natCast distancePositive.le,
        mul_comm exponent, Real.rpow_natCast_mul distancePositive.le]
    have identity : upper * timeRate⁻¹ ^ level =
        constant * (radiusScale / distanceRate ^ (level + 1)) ^ exponent := by
      dsimp only [constant]
      rw [Real.div_rpow radiusScalePositive.le (pow_nonneg distancePositive.le _),
        scalePower, pow_succ, inv_pow]
      field_simp [pow_ne_zero level timePositive.ne', timePositive.ne',
        (Real.rpow_pos_of_pos radiusScalePositive exponent).ne']
      <;> ring
    rw [identity]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg radiusScalePositive.le (pow_nonneg distancePositive.le _))
        nextRadius exponentNonnegative) constantPositive.le

theorem continuous_exit_mean_all_radii_of_geometric
    {Space : Type*} [MetricSpace Space] [MeasurableSpace C(ℝ≥0, Space)]
    (law : Measure C(ℝ≥0, Space)) (distanceRate timeRate radiusScale upper : ℝ)
    (distanceGreaterThanOne : 1 < distanceRate) (timeGreaterThanOne : 1 < timeRate)
    (radiusScalePositive : 0 < radiusScale) (upperPositive : 0 < upper)
    (geometricBounds : ∀ level : ℕ, 1 ≤ level → ∀ center : Space,
      (∫⁻ path, continuousPathBallExit path center (radiusScale * distanceRate⁻¹ ^ level) ∂law) ≤
        ENNReal.ofReal (upper * timeRate⁻¹ ^ level)) :
    ∃ constant cutoff : ℝ, 0 < constant ∧ 0 < cutoff ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ cutoff → ∀ center : Space,
        (∫⁻ path, continuousPathBallExit path center radius ∂law) ≤
          ENNReal.ofReal (constant * radius ^ (Real.log timeRate / Real.log distanceRate)) := by
  obtain ⟨constant, cutoff, constantPositive, cutoffPositive, choice⟩ :=
    geometric_exit_mean_radius_choice distanceRate timeRate radiusScale upper
      distanceGreaterThanOne timeGreaterThanOne radiusScalePositive upperPositive
  refine ⟨constant, cutoff, constantPositive, cutoffPositive, ?_⟩
  intro radius radiusPositive radiusSmall center
  obtain ⟨level, levelPositive, radiusBound, timeBound⟩ := choice radius radiusPositive radiusSmall
  exact (lintegral_mono fun path => continuousPathBallExit_mono_radius path center radiusBound).trans
    ((geometricBounds level levelPositive center).trans (ENNReal.ofReal_le_ofReal timeBound))

end
end IGS.Sec31

#print axioms IGS.Sec31.continuousPathBallExit_mono_radius
#print axioms IGS.Sec31.geometric_exit_mean_radius_choice
#print axioms IGS.Sec31.continuous_exit_mean_all_radii_of_geometric
