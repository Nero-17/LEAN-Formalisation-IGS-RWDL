import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! A scalar backwards iteration used to obtain ultracontractive estimates
from a two-scale Nash bound and energy smoothing. The recurrence is an
explicit generic input; the actual semigroup must supply it separately. -/

namespace IGS.Sec31

open Filter Topology
open scoped BigOperators

theorem geometric_backward_iteration_finite
    (values : ℕ → ℝ) (contraction growth forcing : ℝ)
    (contractionNonnegative : 0 ≤ contraction)
    (recurrence : ∀ index, values index ≤ contraction * values (index + 1) + forcing * growth ^ index)
    (count : ℕ) :
    values 0 ≤ contraction ^ count * values count +
      forcing * ∑ index ∈ Finset.range count, (contraction * growth) ^ index := by
  induction count with
  | zero => simp
  | succ count induction =>
      calc
        values 0 ≤ contraction ^ count * values count +
            forcing * ∑ index ∈ Finset.range count, (contraction * growth) ^ index := induction
        _ ≤ contraction ^ count * (contraction * values (count + 1) + forcing * growth ^ count) +
            forcing * ∑ index ∈ Finset.range count, (contraction * growth) ^ index :=
          add_le_add (mul_le_mul_of_nonneg_left (recurrence count)
            (pow_nonneg contractionNonnegative count)) le_rfl
        _ = contraction ^ (count + 1) * values (count + 1) +
            forcing * ∑ index ∈ Finset.range (count + 1), (contraction * growth) ^ index := by
          simp only [Finset.sum_range_succ, pow_succ, mul_pow]
          ring

theorem geometric_backward_iteration_bound
    (values : ℕ → ℝ) (contraction growth forcing bound : ℝ)
    (contractionNonnegative : 0 ≤ contraction) (contractionLessThanOne : contraction < 1)
    (growthNonnegative : 0 ≤ growth) (forcingNonnegative : 0 ≤ forcing)
    (productLessThanOne : contraction * growth < 1)
    (bounded : ∀ index, values index ≤ bound)
    (recurrence : ∀ index, values index ≤ contraction * values (index + 1) + forcing * growth ^ index) :
    values 0 ≤ forcing / (1 - contraction * growth) := by
  have denominatorPositive : 0 < 1 - contraction * growth := sub_pos.mpr productLessThanOne
  have finiteSumBound (count : ℕ) :
      (∑ index ∈ Finset.range count, (contraction * growth) ^ index) ≤
        1 / (1 - contraction * growth) := by
    apply (le_div_iff₀ denominatorPositive).mpr
    rw [geom_sum_mul_neg]
    exact sub_le_self _ (pow_nonneg (mul_nonneg contractionNonnegative growthNonnegative) count)
  have upperBound (count : ℕ) : values 0 ≤ contraction ^ count * bound +
      forcing / (1 - contraction * growth) := by
    calc
      _ ≤ contraction ^ count * values count +
          forcing * ∑ index ∈ Finset.range count, (contraction * growth) ^ index :=
        geometric_backward_iteration_finite values contraction growth forcing contractionNonnegative recurrence count
      _ ≤ contraction ^ count * bound + forcing * (1 / (1 - contraction * growth)) :=
        add_le_add (mul_le_mul_of_nonneg_left (bounded count) (pow_nonneg contractionNonnegative count))
          (mul_le_mul_of_nonneg_left (finiteSumBound count) forcingNonnegative)
      _ = _ := by ring
  have tailLimit := (tendsto_pow_atTop_nhds_zero_of_lt_one contractionNonnegative
    contractionLessThanOne).mul_const bound
  have limit : Tendsto (fun count : ℕ => contraction ^ count * bound +
      forcing / (1 - contraction * growth)) atTop
      (𝓝 (forcing / (1 - contraction * growth))) := by
    simpa only [zero_mul, zero_add] using tailLimit.add_const (forcing / (1 - contraction * growth))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds limit (Filter.Eventually.of_forall upperBound)

end IGS.Sec31

#print axioms IGS.Sec31.geometric_backward_iteration_finite
#print axioms IGS.Sec31.geometric_backward_iteration_bound
