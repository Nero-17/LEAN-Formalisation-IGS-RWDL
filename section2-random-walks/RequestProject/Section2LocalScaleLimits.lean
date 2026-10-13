import RequestProject.Section2ScaleLimits

/-! The local dimension convention with a fixed original-unit radius and
the actual growing diameter in the denominator. -/

namespace EIGS

open Filter Topology

theorem local_logarithmic_dimension_limit
    {sequence diameter : ℕ → ℝ}
    {rate distance_rate lower upper diameter_lower diameter_upper radius : ℝ}
    (rate_positive : 0 < rate) (distance_rate_gt_one : 1 < distance_rate)
    (lower_positive : 0 < lower) (upper_positive : 0 < upper)
    (diameter_lower_positive : 0 < diameter_lower)
    (diameter_upper_positive : 0 < diameter_upper) (radius_positive : 0 < radius)
    (growth : ∀ᶠ level in atTop, lower * rate ^ level ≤ sequence level ∧
      sequence level ≤ upper * rate ^ level)
    (diameter_growth : ∀ᶠ level in atTop,
      diameter_lower * distance_rate ^ level ≤ diameter level ∧
      diameter level ≤ diameter_upper * distance_rate ^ level) :
    Tendsto (fun level => Real.log (sequence level) / (-Real.log (radius / diameter level)))
      atTop (nhds (Real.log rate / Real.log distance_rate)) := by
  have sequence_limit := logarithmic_geometric_scale_limit rate_positive lower_positive
    upper_positive tendsto_id growth
  have diameter_limit := logarithmic_geometric_scale_limit (zero_lt_one.trans distance_rate_gt_one)
    diameter_lower_positive diameter_upper_positive tendsto_id diameter_growth
  simp only [id_eq] at sequence_limit diameter_limit
  have constant_limit : Tendsto (fun level : ℕ => Real.log radius / (level : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have denominator_limit : Tendsto (fun level : ℕ =>
      (-Real.log (radius / diameter level)) / (level : ℝ)) atTop
      (nhds (Real.log distance_rate)) := by
    have difference_limit := diameter_limit.sub constant_limit
    simp only [sub_zero] at difference_limit
    apply difference_limit.congr'
    filter_upwards [diameter_growth] with level bounds
    have diameter_positive := (mul_pos diameter_lower_positive
      (pow_pos (zero_lt_one.trans distance_rate_gt_one) level)).trans_le bounds.1
    rw [Real.log_div radius_positive.ne' diameter_positive.ne']
    ring
  apply (sequence_limit.div denominator_limit (Real.log_pos distance_rate_gt_one).ne').congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with level level_positive
  have level_ne : (level : ℝ) ≠ 0 := by exact_mod_cast level_positive.ne'
  exact div_div_div_cancel_right₀ level_ne (Real.log (sequence level))
    (-Real.log (radius / diameter level))

end EIGS

#print axioms EIGS.local_logarithmic_dimension_limit
