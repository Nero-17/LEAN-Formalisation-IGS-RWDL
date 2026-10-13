import RequestProject.Section2MassConvergence
import Mathlib.Analysis.Normed.Group.Tannery

/-! Normalized cumulative actual vertex births. -/

namespace EIGS

open Filter Topology
open scoped BigOperators Classical

noncomputable section

theorem normalized_partial_sum_tendsto {sequence : ℕ → ℝ} {rate limit : ℝ}
    (rateGreaterThanOne : 1 < rate)
    (convergence : Tendsto (fun level => sequence level / rate ^ level) atTop (𝓝 limit)) :
    Tendsto (fun level => (∑ birth ∈ Finset.range level, sequence birth) / rate ^ level)
      atTop (𝓝 (limit / (rate - 1))) := by
  have ratePositive : 0 < rate := zero_lt_one.trans rateGreaterThanOne
  have inverseNonnegative : 0 ≤ rate⁻¹ := inv_nonneg.mpr ratePositive.le
  have inverseLessThanOne : rate⁻¹ < 1 := (inv_lt_one₀ ratePositive).mpr rateGreaterThanOne
  obtain ⟨bound, boundCondition⟩ :=
    (Metric.isBounded_range_of_tendsto (fun level => sequence level / rate ^ level) convergence).exists_norm_le
  have boundNonnegative : 0 ≤ bound :=
    (norm_nonneg (sequence 0 / rate ^ 0)).trans (boundCondition _ ⟨0, rfl⟩)
  let ageSummand (level age : ℕ) : ℝ :=
    if age < level then
      sequence (level - 1 - age) / rate ^ (level - 1 - age) * rate⁻¹ ^ (age + 1)
    else 0
  have ageLimit : ∀ age,
      Tendsto (fun level => ageSummand level age) atTop (𝓝 (limit * rate⁻¹ ^ (age + 1))) := by
    intro age
    have shiftedIndex : Tendsto (fun level : ℕ => level - 1 - age) atTop atTop :=
      (tendsto_sub_atTop_nat age).comp (tendsto_sub_atTop_nat 1)
    apply ((convergence.comp shiftedIndex).mul_const (rate⁻¹ ^ (age + 1))).congr'
    filter_upwards [eventually_gt_atTop age] with level ageLessThanLevel
    simp only [ageSummand, ageLessThanLevel, ↓reduceIte, Function.comp_apply]
  have summableBound : Summable (fun age : ℕ => bound * rate⁻¹ ^ (age + 1)) := by
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      (summable_geometric_of_lt_one inverseNonnegative inverseLessThanOne).mul_left (bound * rate⁻¹)
  have summandBound : ∀ level age, ‖ageSummand level age‖ ≤ bound * rate⁻¹ ^ (age + 1) := by
    intro level age
    by_cases ageLessThanLevel : age < level
    · simp only [ageSummand, ageLessThanLevel, ↓reduceIte, norm_mul,
        Real.norm_of_nonneg (pow_nonneg inverseNonnegative _)]
      exact mul_le_mul_of_nonneg_right (boundCondition _ ⟨level - 1 - age, rfl⟩)
        (pow_nonneg inverseNonnegative _)
    · simp only [ageSummand, ageLessThanLevel, ↓reduceIte, norm_zero]
      exact mul_nonneg boundNonnegative (pow_nonneg inverseNonnegative _)
  have seriesLimit := tendsto_tsum_of_dominated_convergence summableBound ageLimit
    (Eventually.of_forall summandBound)
  have seriesValue : (∑' age : ℕ, limit * rate⁻¹ ^ (age + 1)) = limit / (rate - 1) := by
    simp_rw [pow_succ, ← mul_assoc]
    rw [tsum_mul_right, tsum_mul_left,
      tsum_geometric_of_lt_one inverseNonnegative inverseLessThanOne]
    field_simp
  have finiteSumValue : ∀ level,
      (∑' age : ℕ, ageSummand level age) =
        (∑ birth ∈ Finset.range level, sequence birth) / rate ^ level := by
    intro level
    rw [tsum_eq_sum (s := Finset.range level) (fun age ageNotMem => by
      simp only [Finset.mem_range] at ageNotMem
      simp only [ageSummand, ageNotMem, ↓reduceIte])]
    calc
      _ = ∑ age ∈ Finset.range level, sequence (level - 1 - age) / rate ^ level := by
        apply Finset.sum_congr rfl
        intro age ageMem
        have ageLessThanLevel := Finset.mem_range.mp ageMem
        simp only [ageSummand, ageLessThanLevel, ↓reduceIte, inv_pow]
        rw [← div_eq_mul_inv, div_div]
        have exponentEquality : level - 1 - age + (age + 1) = level := by omega
        rw [← pow_add, exponentEquality]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_range_reflect]
  simpa only [seriesValue, finiteSumValue] using seriesLimit

end
end EIGS




#print axioms EIGS.normalized_partial_sum_tendsto
