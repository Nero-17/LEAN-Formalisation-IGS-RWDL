import RequestProject.Section21

/-!
# Resistance dimension for every positive resistance growth rate

The resistance rate may be less than, equal to, or greater than one. Only the
metric growth rate must exceed one. This includes the zero-resistance-dimension
diamond hierarchical lattice and negative resistance dimensions.
-/

namespace EIGS

open Filter Topology

theorem logarithmic_geometric_growth_limit {sequence : ℕ → ℝ}
    {rate lower upper : ℝ} (rate_positive : 0 < rate)
    (lower_positive : 0 < lower) (upper_positive : 0 < upper)
    (growth : ∀ level, lower * rate ^ level ≤ sequence level ∧
      sequence level ≤ upper * rate ^ level) :
    Tendsto (fun level => Real.log (sequence level) / (level : ℝ)) atTop
      (nhds (Real.log rate)) := by
  have lower_limit : Tendsto (fun level : ℕ => Real.log lower / (level : ℝ) + Real.log rate)
      atTop (nhds (Real.log rate)) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const
      (Real.log rate)
  have upper_limit : Tendsto (fun level : ℕ => Real.log upper / (level : ℝ) + Real.log rate)
      atTop (nhds (Real.log rate)) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const
      (Real.log rate)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower_limit upper_limit
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with level level_positive
    have cast_ne : (level : ℝ) ≠ 0 := by exact_mod_cast level_positive.ne'
    have logarithm_lower := Real.log_le_log (mul_pos lower_positive (pow_pos rate_positive level))
      (growth level).1
    rw [Real.log_mul lower_positive.ne' (pow_pos rate_positive level).ne', Real.log_pow]
      at logarithm_lower
    calc
      _ = (Real.log lower + (level : ℝ) * Real.log rate) / (level : ℝ) := by
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right logarithm_lower (Nat.cast_nonneg level)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with level level_positive
    have cast_ne : (level : ℝ) ≠ 0 := by exact_mod_cast level_positive.ne'
    have sequence_positive := lt_of_lt_of_le
      (mul_pos lower_positive (pow_pos rate_positive level)) (growth level).1
    have logarithm_upper := Real.log_le_log sequence_positive (growth level).2
    rw [Real.log_mul upper_positive.ne' (pow_pos rate_positive level).ne', Real.log_pow]
      at logarithm_upper
    calc
      _ ≤ (Real.log upper + (level : ℝ) * Real.log rate) / (level : ℝ) :=
        div_le_div_of_nonneg_right logarithm_upper (Nat.cast_nonneg level)
      _ = _ := by field_simp

/-- Theorem 2.11's analytic limit permits every positive resistance rate. -/
theorem resistance_dimension_limit_of_pos_rates {resistance distance : ℕ → ℝ}
    {resistance_rate distance_rate resistance_lower resistance_upper distance_lower distance_upper : ℝ}
    (resistance_rate_positive : 0 < resistance_rate) (distance_rate_gt_one : 1 < distance_rate)
    (resistance_lower_positive : 0 < resistance_lower)
    (resistance_upper_positive : 0 < resistance_upper)
    (distance_lower_positive : 0 < distance_lower) (distance_upper_positive : 0 < distance_upper)
    (resistance_growth : ∀ level, resistance_lower * resistance_rate ^ level ≤ resistance level ∧
      resistance level ≤ resistance_upper * resistance_rate ^ level)
    (distance_growth : ∀ level, distance_lower * distance_rate ^ level ≤ distance level ∧
      distance level ≤ distance_upper * distance_rate ^ level) :
    Tendsto (fun level => Real.log (resistance level) / Real.log (distance level)) atTop
      (nhds (Real.log resistance_rate / Real.log distance_rate)) := by
  have resistance_limit := logarithmic_geometric_growth_limit resistance_rate_positive
    resistance_lower_positive resistance_upper_positive resistance_growth
  have distance_limit := logarithmic_geometric_growth_limit
    (zero_lt_one.trans distance_rate_gt_one) distance_lower_positive distance_upper_positive
    distance_growth
  have ratio_limit := resistance_limit.div distance_limit
    (Real.log_pos distance_rate_gt_one).ne'
  apply ratio_limit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with level level_positive
  have cast_ne : (level : ℝ) ≠ 0 := by exact_mod_cast level_positive.ne'
  exact div_div_div_cancel_right₀ cast_ne (Real.log (resistance level)) (Real.log (distance level))

theorem resistance_dimension_eq_of_pos_rates {resistance distance : ℕ → ℝ}
    {resistance_rate distance_rate : ℝ}
    (resistance_rate_positive : 0 < resistance_rate) (distance_rate_gt_one : 1 < distance_rate)
    (resistance_growth : ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * resistance_rate ^ level ≤ resistance level ∧ resistance level ≤ upper * resistance_rate ^ level)
    (distance_growth : ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * distance_rate ^ level ≤ distance level ∧ distance level ≤ upper * distance_rate ^ level) :
    resistanceDimension resistance distance = Real.log resistance_rate / Real.log distance_rate := by
  obtain ⟨resistance_lower, resistance_upper, resistance_lower_positive,
    resistance_upper_positive, resistance_growth⟩ := resistance_growth
  obtain ⟨distance_lower, distance_upper, distance_lower_positive,
    distance_upper_positive, distance_growth⟩ := distance_growth
  exact (resistance_dimension_limit_of_pos_rates resistance_rate_positive distance_rate_gt_one
    resistance_lower_positive resistance_upper_positive distance_lower_positive distance_upper_positive
    resistance_growth distance_growth).limUnder_eq

end EIGS
