import RequestProject.Section2Dimension

/-! Logarithmic limits along arbitrary diverging geometric scales. The bounds
need hold only eventually, as in the paper's admissible-radius definition. -/

namespace EIGS

open Filter Topology

theorem geometric_depth_tendsto_of_radius_tendsto
    {radius : ℕ → ℝ} {depth : ℕ → ℕ} {rate upper : ℝ}
    (rate_ge_one : 1 ≤ rate) (upper_positive : 0 < upper)
    (radius_tendsto : Tendsto radius atTop atTop)
    (radius_upper : ∀ᶠ index in atTop, radius index ≤ upper * rate ^ depth index) :
    Tendsto depth atTop atTop := by
  apply tendsto_atTop.mpr
  intro threshold
  filter_upwards [radius_tendsto.eventually_gt_atTop (upper * rate ^ threshold), radius_upper]
    with index radius_large radius_bound
  by_contra depth_small
  have power_bound : rate ^ depth index ≤ rate ^ threshold :=
    pow_le_pow_right₀ rate_ge_one (le_of_lt (Nat.lt_of_not_ge depth_small))
  exact (not_lt_of_ge (radius_bound.trans
    (mul_le_mul_of_nonneg_left power_bound upper_positive.le))) radius_large

theorem logarithmic_geometric_scale_limit
    {sequence : ℕ → ℝ} {depth : ℕ → ℕ} {rate lower upper : ℝ}
    (rate_positive : 0 < rate) (lower_positive : 0 < lower)
    (upper_positive : 0 < upper) (depth_tendsto : Tendsto depth atTop atTop)
    (growth : ∀ᶠ index in atTop, lower * rate ^ depth index ≤ sequence index ∧
      sequence index ≤ upper * rate ^ depth index) :
    Tendsto (fun index => Real.log (sequence index) / (depth index : ℝ)) atTop
      (nhds (Real.log rate)) := by
  have depth_cast_tendsto : Tendsto (fun index => (depth index : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp depth_tendsto
  have lower_limit : Tendsto (fun index => Real.log lower / (depth index : ℝ) + Real.log rate)
      atTop (nhds (Real.log rate)) := by
    simpa using (tendsto_const_nhds.div_atTop depth_cast_tendsto).add_const (Real.log rate)
  have upper_limit : Tendsto (fun index => Real.log upper / (depth index : ℝ) + Real.log rate)
      atTop (nhds (Real.log rate)) := by
    simpa using (tendsto_const_nhds.div_atTop depth_cast_tendsto).add_const (Real.log rate)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower_limit upper_limit
  · filter_upwards [depth_tendsto.eventually_gt_atTop 0, growth]
      with index depth_positive bounds
    have depth_ne : (depth index : ℝ) ≠ 0 := by exact_mod_cast depth_positive.ne'
    have logarithm_lower := Real.log_le_log
      (mul_pos lower_positive (pow_pos rate_positive _)) bounds.1
    rw [Real.log_mul lower_positive.ne' (pow_pos rate_positive _).ne', Real.log_pow]
      at logarithm_lower
    calc
      _ = (Real.log lower + (depth index : ℝ) * Real.log rate) / (depth index : ℝ) := by
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right logarithm_lower (Nat.cast_nonneg _)
  · filter_upwards [depth_tendsto.eventually_gt_atTop 0, growth]
      with index depth_positive bounds
    have depth_ne : (depth index : ℝ) ≠ 0 := by exact_mod_cast depth_positive.ne'
    have sequence_positive := (mul_pos lower_positive (pow_pos rate_positive _)).trans_le bounds.1
    have logarithm_upper := Real.log_le_log sequence_positive bounds.2
    rw [Real.log_mul upper_positive.ne' (pow_pos rate_positive _).ne', Real.log_pow]
      at logarithm_upper
    calc
      _ ≤ (Real.log upper + (depth index : ℝ) * Real.log rate) / (depth index : ℝ) :=
        div_le_div_of_nonneg_right logarithm_upper (Nat.cast_nonneg _)
      _ = _ := by field_simp

theorem logarithmic_ratio_limit_of_geometric_scale
    {sequence radius : ℕ → ℝ} {depth : ℕ → ℕ}
    {rate distance_rate lower upper radius_lower radius_upper : ℝ}
    (rate_positive : 0 < rate) (distance_rate_gt_one : 1 < distance_rate)
    (lower_positive : 0 < lower) (upper_positive : 0 < upper)
    (radius_lower_positive : 0 < radius_lower) (radius_upper_positive : 0 < radius_upper)
    (radius_tendsto : Tendsto radius atTop atTop)
    (growth : ∀ᶠ index in atTop, lower * rate ^ depth index ≤ sequence index ∧
      sequence index ≤ upper * rate ^ depth index)
    (radius_growth : ∀ᶠ index in atTop,
      radius_lower * distance_rate ^ depth index ≤ radius index ∧
      radius index ≤ radius_upper * distance_rate ^ depth index) :
    Tendsto (fun index => Real.log (sequence index) / Real.log (radius index)) atTop
      (nhds (Real.log rate / Real.log distance_rate)) := by
  have depth_tendsto := geometric_depth_tendsto_of_radius_tendsto distance_rate_gt_one.le
    radius_upper_positive radius_tendsto (radius_growth.mono (fun _ bounds => bounds.2))
  have sequence_limit := logarithmic_geometric_scale_limit rate_positive
    lower_positive upper_positive depth_tendsto growth
  have radius_limit := logarithmic_geometric_scale_limit (zero_lt_one.trans distance_rate_gt_one)
    radius_lower_positive radius_upper_positive depth_tendsto radius_growth
  apply (sequence_limit.div radius_limit (Real.log_pos distance_rate_gt_one).ne').congr'
  filter_upwards [depth_tendsto.eventually_gt_atTop 0] with index depth_positive
  have depth_ne : (depth index : ℝ) ≠ 0 := by exact_mod_cast depth_positive.ne'
  exact div_div_div_cancel_right₀ depth_ne (Real.log (sequence index)) (Real.log (radius index))

end EIGS

#print axioms EIGS.geometric_depth_tendsto_of_radius_tendsto
#print axioms EIGS.logarithmic_geometric_scale_limit
#print axioms EIGS.logarithmic_ratio_limit_of_geometric_scale
