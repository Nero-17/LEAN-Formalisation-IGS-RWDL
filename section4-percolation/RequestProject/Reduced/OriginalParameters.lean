import RequestProject.Reduced.Params

namespace Reduced

/-- The simplified diamond parameter is exactly the original conditional probability. -/
theorem pdiamond_original_formula {p : ℝ} (positive : 0 < p) (below_one : p < 1) :
    pdiamond p = p ^ 4 / (2 * p ^ 2 - p ^ 4) := by
  have simplified_denominator_positive := two_sub_sq_pos below_one positive
  have original_denominator_positive : 0 < 2 * p ^ 2 - p ^ 4 := by
    have factorization : 2 * p ^ 2 - p ^ 4 = p ^ 2 * (2 - p ^ 2) := by ring
    rw [factorization]
    exact mul_pos (sq_pos_of_pos positive) simplified_denominator_positive
  unfold pdiamond
  apply (div_eq_div_iff (ne_of_gt simplified_denominator_positive)
    (ne_of_gt original_denominator_positive)).mpr
  ring

/-- The simplified series parameter is exactly the original conditional probability. -/
theorem pseries_original_formula {p : ℝ} (positive : 0 < p) (below_one : p < 1) :
    pseries p = (2 * p ^ 2 - 2 * p ^ 4) / (2 * p ^ 2 - p ^ 4) := by
  have simplified_denominator_positive := two_sub_sq_pos below_one positive
  have original_denominator_positive : 0 < 2 * p ^ 2 - p ^ 4 := by
    have factorization : 2 * p ^ 2 - p ^ 4 = p ^ 2 * (2 - p ^ 2) := by ring
    rw [factorization]
    exact mul_pos (sq_pos_of_pos positive) simplified_denominator_positive
  unfold pseries
  apply (div_eq_div_iff (ne_of_gt simplified_denominator_positive)
    (ne_of_gt original_denominator_positive)).mpr
  ring

end Reduced
